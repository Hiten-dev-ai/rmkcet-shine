"""Workbook heuristics used by the standalone marksheet parser."""

import re

import pandas as pd


def detect_column_types(df: pd.DataFrame, sample_rows: int = 20):
    """Classify workbook columns based on a small sample of row values."""

    detections = {}
    subject_columns = {}
    sample = df.head(sample_rows)

    for col_idx in range(len(df.columns)):
        col_data = sample.iloc[:, col_idx].dropna().astype(str)
        if col_data.empty:
            continue

        scores = {
            "sno": _score_sno(col_data),
            "reg_no": _score_reg_no(col_data),
            "name": _score_name(col_data),
            "phone": _score_phone(col_data),
            "email": _score_email(col_data),
            "marks": _score_marks(col_data),
        }

        best = max(scores, key=scores.get)
        confidence = scores[best]

        if confidence > 0.4:
            if best == "marks":
                header_val = str(df.columns[col_idx]).strip()
                header_l = header_val.lower()
                header_norm = re.sub(r"[^a-z0-9]", "", header_l)
                skip_headers = (
                    "sl. no",
                    "sl no",
                    "s.no",
                    "s no",
                    "reg",
                    "name",
                    "g / m",
                    "g/m",
                    "d/h",
                    "girl / boy",
                    "girl/boy",
                    "cut off",
                    "cutoff",
                    "unnamed",
                    "nan",
                    "attendance",
                    "attendence",
                )
                if any(token in header_l for token in skip_headers):
                    continue
                if header_norm in ("attendance", "att", "attendence"):
                    continue
                if header_val and header_l not in ("unnamed", "nan", ""):
                    subject_columns[col_idx] = header_val
                else:
                    subject_columns[col_idx] = f"Subject_{col_idx}"
            elif best not in detections or confidence > detections[best][1]:
                detections[best] = (col_idx, confidence)

    result = {key: value[0] for key, value in detections.items()}
    result["subjects"] = subject_columns
    return result


def _score_sno(col: pd.Series) -> float:
    try:
        nums = col.apply(lambda value: float(str(value).replace(".0", "")))
        if nums.max() < 200 and nums.min() >= 0:
            diffs = nums.diff().dropna()
            if len(diffs) > 0 and (diffs == 1).mean() > 0.7:
                return 0.9
        return 0.1
    except Exception:
        return 0.0


def _score_reg_no(col: pd.Series) -> float:
    matches = col.apply(lambda value: bool(re.match(r"^\d{8,15}\.?0?$", str(value).strip())))
    return matches.mean()


def _score_name(col: pd.Series) -> float:
    matches = col.apply(lambda value: bool(re.match(r"^[A-Za-z][A-Za-z\s\.\-]{2,50}$", str(value).strip())))
    return matches.mean()


def _score_phone(col: pd.Series) -> float:
    def is_phone(value):
        digits = "".join(char for char in str(value) if char.isdigit())
        return len(digits) >= 10

    return col.apply(is_phone).mean()


def _score_email(col: pd.Series) -> float:
    matches = col.apply(lambda value: bool(re.match(r"^[^@]+@[^@]+\.[^@]+$", str(value).strip())))
    return matches.mean()


def _score_marks(col: pd.Series) -> float:
    header_hint = str(getattr(col, "name", "") or "").strip().lower()
    header_norm = re.sub(r"[^a-z0-9]", "", header_hint)
    if header_norm in ("attendance", "att", "attendence"):
        return 0.0
    if any(token in header_hint for token in ("sl", "reg", "name", "g / m", "d/h", "girl", "boy", "cut off")):
        return 0.0

    def is_mark(value):
        text = str(value).strip().upper()
        if text in ("ABSENT", "A", "AB", "-"):
            return True
        try:
            numeric = float(text)
            return 0 <= numeric <= 100
        except ValueError:
            return False

    return col.apply(is_mark).mean()


def find_header_row(df_raw: pd.DataFrame, max_rows: int = 15) -> int:
    keywords = [
        "name",
        "reg",
        "reg.",
        "register",
        "s.no",
        "sno",
        "sl",
        "roll",
        "roll no",
        "student",
        "gpa",
        "whatsapp",
        "phone",
        "mail",
        "email",
    ]
    for row_idx in range(min(max_rows, len(df_raw))):
        row_vals = [str(value).strip().lower() for value in df_raw.iloc[row_idx].values if pd.notna(value)]
        if not row_vals:
            continue
        matches = sum(1 for keyword in keywords if any(keyword in value for value in row_vals))
        has_marks_labels = any(value in {"maths", "chem", "gpa"} for value in row_vals)
        has_reg_like = any(("reg" in value) or ("roll" in value) for value in row_vals)
        has_name_like = any(("name" in value) or ("student" in value) for value in row_vals)
        if matches >= 2 and (has_marks_labels or (has_reg_like and has_name_like)):
            return row_idx
    return 0


def find_data_start_row(df_raw: pd.DataFrame, header_row: int) -> int:
    for row_idx in range(header_row + 1, min(header_row + 10, len(df_raw))):
        row = df_raw.iloc[row_idx]
        non_null = row.dropna()
        if len(non_null) < 3:
            continue
        for value in non_null:
            text = str(value).strip()
            if re.match(r"^\d{5,}", text):
                return row_idx
            try:
                numeric = float(text)
                if 0 < numeric < 200:
                    return row_idx
            except ValueError:
                continue
    return header_row + 1
