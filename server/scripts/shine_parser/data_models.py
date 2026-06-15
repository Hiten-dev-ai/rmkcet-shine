"""Minimal marksheet parser data models for the standalone rebuild."""

from decimal import Decimal, InvalidOperation


class StudentRecord:
    """Represents a single student row parsed from a marksheet."""

    def __init__(self, reg_no="", name="", department="", phone="", email="", marks=None, section=""):
        self.reg_no = self._clean_reg_no(reg_no)
        self.name = str(name).strip() if name else ""
        self.department = str(department).strip() if department else ""
        self.phone = self._clean_phone(phone)
        self.email = str(email).strip() if email else ""
        self.marks = marks or {}
        self.section = section

    @staticmethod
    def _clean_reg_no(val):
        value = str(val).strip()
        if value.endswith(".0"):
            value = value[:-2]
        return value.replace(" ", "")

    @staticmethod
    def _clean_phone(val):
        if val is None:
            return ""

        raw = val
        if isinstance(val, float):
            raw = str(int(val)) if val.is_integer() else format(val, "f")
        else:
            value = str(val).strip()
            if "e" in value.lower():
                try:
                    raw = format(Decimal(value), "f")
                except (InvalidOperation, ValueError):
                    raw = value
            else:
                raw = value

        digits = "".join(char for char in str(raw) if char.isdigit())
        return digits[-10:] if len(digits) >= 10 else digits

    def is_valid(self):
        return bool(self.reg_no and self.name)

    def to_dict(self):
        return {
            "reg_no": self.reg_no,
            "name": self.name,
            "department": self.department,
            "phone": self.phone,
            "email": self.email,
            "marks": self.marks,
            "section": self.section,
        }


class TestInfo:
    """Represents marksheet-level metadata extracted from workbook content."""

    def __init__(self):
        self.test_name = ""
        self.semester = 0
        self.academic_year = ""
        self.batch_name = ""
        self.department = ""
        self.section = ""
        self.subjects = []
        self.subject_columns = {}
        self.header_row = 0
        self.data_start_row = 7
        self.max_marks = 100

    def to_dict(self):
        return {
            "test_name": self.test_name,
            "semester": self.semester,
            "academic_year": self.academic_year,
            "batch_name": self.batch_name,
            "department": self.department,
            "section": self.section,
            "subjects": self.subjects,
            "subject_columns": self.subject_columns,
            "header_row": self.header_row,
            "data_start_row": self.data_start_row,
            "max_marks": self.max_marks,
        }
