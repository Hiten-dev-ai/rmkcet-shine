"""Standalone workbook parser used by the rebuild reports upload flow."""

import re

import pandas as pd

from data_models import StudentRecord, TestInfo
from excel_detective import detect_column_types, find_data_start_row, find_header_row
from test_metadata import extract_test_info_from_text


class IntelligentParser:
    """Parse uploaded Excel files with lightweight Shine heuristics."""

    def __init__(self):
        self.test_info = TestInfo()
        self.students = []
        self.raw_headers = []
        self.errors = []

    def parse_file(self, file_obj, filename: str = ""):
        self.errors = []
        self.students = []
        self.test_info = TestInfo()

        try:
            workbook = pd.ExcelFile(file_obj)
        except Exception as exc:
            self.errors.append(f"Cannot read Excel file: {exc}")
            return self.test_info, self.students

        if filename:
            metadata = extract_test_info_from_text(filename)
            self.test_info.test_name = metadata.get("test_name", "")
            self.test_info.semester = metadata.get("semester", 0)
            self.test_info.academic_year = metadata.get("academic_year", "")
            self.test_info.batch_name = metadata.get("batch_name", "")
            self.test_info.department = metadata.get("department", "")

        all_students = {}
        for sheet_name in workbook.sheet_names:
            try:
                students = self._parse_sheet(workbook, sheet_name)
                for student in students:
                    key = student.reg_no
                    if key in all_students:
                        all_students[key].marks.update(student.marks)
                    else:
                        all_students[key] = student
            except Exception as exc:
                self.errors.append(f"Error in sheet '{sheet_name}': {exc}")

        self.students = list(all_students.values())

        if workbook.sheet_names:
            self._extract_header_metadata(workbook, workbook.sheet_names[0])

        return self.test_info, self.students

    def _parse_sheet(self, workbook: pd.ExcelFile, sheet_name: str):
        df_raw = pd.read_excel(workbook, sheet_name=sheet_name, header=None)
        if df_raw.empty:
            return []

        header_row = find_header_row(df_raw)
        data_start = find_data_start_row(df_raw, header_row)

        df = pd.read_excel(workbook, sheet_name=sheet_name, header=header_row)
        if df.empty:
            return []

        self.test_info.header_row = header_row
        self.test_info.data_start_row = data_start

        detections = detect_column_types(df)
        reg_col = detections.get("reg_no")
        name_col = detections.get("name")
        phone_col = detections.get("phone")
        email_col = detections.get("email")
        subject_cols = detections.get("subjects", {})

        if reg_col is None and name_col is None:
            self.errors.append(f"Sheet '{sheet_name}': Cannot detect reg_no or name columns")
            return []

        for col_idx, subject_name in subject_cols.items():
            self.test_info.subject_columns[col_idx] = subject_name
            if subject_name not in [subject.get("name") for subject in self.test_info.subjects]:
                self.test_info.subjects.append({
                    "name": subject_name,
                    "code": self._generate_subject_code(subject_name),
                })

        students = []
        section = ""
        sheet_label = sheet_name.strip().upper()
        section_match = re.search(r"(?:-|\s)([A-Z])$", sheet_label)
        if len(sheet_label) <= 2:
            section = sheet_label
        elif section_match:
            section = section_match.group(1)

        for row_idx in range(len(df)):
            try:
                row = df.iloc[row_idx]
                reg_no = str(row.iloc[reg_col]).strip() if reg_col is not None else ""
                name = str(row.iloc[name_col]).strip() if name_col is not None else ""
                phone = str(row.iloc[phone_col]).strip() if phone_col is not None else ""
                email = str(row.iloc[email_col]).strip() if email_col is not None else ""

                if not reg_no or reg_no.lower() in ("nan", "none", ""):
                    continue

                lowered_name = name.strip().lower()
                if lowered_name.startswith("total") or "pass %" in lowered_name or "overall" in lowered_name:
                    continue

                marks = {}
                for col_idx, subject_name in subject_cols.items():
                    marks[subject_name] = self._parse_mark(row.iloc[col_idx])

                student = StudentRecord(
                    reg_no=reg_no,
                    name=name,
                    department=self.test_info.department,
                    phone=phone,
                    email=email,
                    marks=marks,
                    section=section,
                )
                if student.is_valid() and re.match(r"^\d{8,15}$", student.reg_no):
                    students.append(student)
            except Exception:
                continue

        return students

    def _extract_header_metadata(self, workbook: pd.ExcelFile, sheet_name: str):
        try:
            df_raw = pd.read_excel(workbook, sheet_name=sheet_name, header=None, nrows=10)
            for row_idx in range(min(8, len(df_raw))):
                for value in df_raw.iloc[row_idx]:
                    if pd.notna(value):
                        text = str(value).strip()
                        if len(text) <= 10:
                            continue
                        metadata = extract_test_info_from_text(text)
                        if metadata["test_name"] and not self.test_info.test_name:
                            self.test_info.test_name = metadata["test_name"]
                        if metadata["semester"] and not self.test_info.semester:
                            self.test_info.semester = metadata["semester"]
                        if metadata["academic_year"] and not self.test_info.academic_year:
                            self.test_info.academic_year = metadata["academic_year"]
                            self.test_info.batch_name = metadata["academic_year"]
                        if metadata["department"] and not self.test_info.department:
                            self.test_info.department = metadata["department"]
                        if not self.test_info.section:
                            section_match = re.search(
                                r"branch\s*&\s*section\s*:\s*([A-Z0-9()]+)\s*[-:]\s*([A-Z])",
                                text,
                                re.IGNORECASE,
                            )
                            if section_match:
                                self.test_info.department = self.test_info.department or section_match.group(1).upper()
                                self.test_info.section = section_match.group(2).upper()
        except Exception:
            pass

    @staticmethod
    def _parse_mark(value):
        if pd.isna(value):
            return "Absent"

        text = str(value).strip().upper()
        if text in ("ABSENT", "A", "AB", "-", ""):
            return "Absent"

        try:
            numeric = float(text)
            if numeric == int(numeric):
                return str(int(numeric))
            return str(round(numeric, 1))
        except ValueError:
            return text

    @staticmethod
    def _generate_subject_code(name: str):
        words = re.sub(r"[^A-Za-z\s]", "", name).split()
        if len(words) == 1:
            return words[0][:4].upper()
        return "".join(word[0] for word in words if word).upper()[:5]
