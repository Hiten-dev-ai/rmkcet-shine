"""Standalone test metadata extraction helpers for marksheet parsing."""

import re


ROMAN_MAP = {
    "I": 1,
    "II": 2,
    "III": 3,
    "IV": 4,
    "V": 5,
    "VI": 6,
    "VII": 7,
    "VIII": 8,
}


def normalize_test_name(raw_name: str) -> str:
    """Normalize workbook labels into the fixed Shine upload test names."""

    text = re.sub(r"\s+", " ", str(raw_name or "").strip().upper())
    if not text:
        return ""

    compact = re.sub(r"[^A-Z0-9]", "", text)
    if "MODEL" in text:
        return "MODEL EXAM"

    if compact.endswith("II") or "IAT2" in compact or "UNITTEST2" in compact or "UNITTESTII" in compact:
        return "IAT 2"
    if compact.endswith("I") or "IAT1" in compact or "UNITTEST1" in compact or "UNITTESTI" in compact:
        return "IAT 1"

    if "IAT" in text or "UNIT TEST" in text or "INTERNAL ASSESSMENT" in text:
        return "IAT 1"

    return ""


def extract_test_info_from_text(text: str):
    info = {
        "test_name": "",
        "semester": 0,
        "academic_year": "",
        "department": "",
        "batch_name": "",
    }
    if not text:
        return info

    text = str(text).strip()

    year_match = re.search(r"\(?(\d{4})\s*[-/]\s*(\d{2,4})\)?", text)
    if year_match:
        year_start = year_match.group(1)
        year_end = year_match.group(2)
        if len(year_end) == 2:
            year_end = year_start[:2] + year_end
        info["academic_year"] = f"{year_start}-{year_end[-2:]}"
        info["batch_name"] = info["academic_year"]

    semester_match = re.search(r"(?:semester|sem)\s*[-:]?\s*([IVX]+|\d+)", text, re.IGNORECASE)
    if not semester_match:
        semester_match = re.search(r"([IVX]+)\s*(?:sem|semester)", text, re.IGNORECASE)
    if semester_match:
        value = semester_match.group(1).upper()
        info["semester"] = ROMAN_MAP.get(value, int(value) if value.isdigit() else 0)

    info["test_name"] = normalize_test_name(text) or "IAT 1"

    department_match = re.search(
        r"(?<![A-Z0-9])(CSE\s*\(\s*CS\s*\)|EE\s*\(\s*VLSI\s*\)|ECE|CSE|AIDS|IT|BME)(?![A-Z0-9])",
        text,
        re.IGNORECASE,
    )
    if department_match:
        info["department"] = department_match.group(1).upper().replace(" ", "")

    return info
