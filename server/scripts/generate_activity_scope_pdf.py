import json
import math
import sys
import tempfile
from collections import defaultdict
from datetime import datetime
from pathlib import Path

from fpdf import FPDF
from PIL import Image


TEST_ORDER = {"IAT 1": 1, "IAT 2": 2, "MODEL EXAM": 3}
HEADERS = ["Counselor", "Email", "Students", "Reached", "Pending", "Completion", "Status", "Last Login"]
COL_WIDTHS = [30, 52, 14, 14, 14, 20, 20, 22]
ROW_HEIGHT = 6
ROWS_PER_PAGE = 18


def year_label(year_level: int) -> str:
    suffix_map = {1: "st", 2: "nd", 3: "rd"}
    safe_year = max(1, int(year_level or 1))
    suffix = suffix_map.get(safe_year if safe_year < 20 else safe_year % 10, "th")
    return f"{safe_year}{suffix} Year"


def semester_label(semester: str) -> str:
    value = str(semester or "").strip()
    if value == "1":
        return "Sem - I"
    if value == "2":
        return "Sem - II"
    return f"Sem - {value or '-'}"


def pdf_bytes(pdf: FPDF) -> bytes:
    raw = pdf.output(dest="S")
    if isinstance(raw, (bytes, bytearray)):
        return bytes(raw)
    return str(raw).encode("latin-1")


def shorten(value: object, limit: int) -> str:
    text = str(value or "").strip()
    if len(text) <= limit:
        return text
    return f"{text[:max(0, limit - 1)].rstrip()}..."


def flatten_image_for_pdf(source_path: Path) -> str | None:
    if not source_path.is_file():
        return None

    with Image.open(source_path) as image:
        rgba = image.convert("RGBA")
        alpha = rgba.getchannel("A")
        bbox = alpha.getbbox()
        if bbox:
            rgba = rgba.crop(bbox)
        canvas = Image.new("RGBA", rgba.size, (255, 255, 255, 255))
        canvas.alpha_composite(rgba)
        flattened = canvas.convert("RGB")

        temp_file = tempfile.NamedTemporaryFile(delete=False, suffix=".png")
        temp_path = temp_file.name
        temp_file.close()
        flattened.save(temp_path, format="PNG")
        return temp_path


def draw_page_header(
    pdf: FPDF,
    banner_path: str | None,
    generated_label: str,
    department: str,
    year_level: int,
    semester: str,
    test_name: str,
    stats: dict,
    chunk_label: str,
) -> None:
    page_width = 210
    content_width = sum(COL_WIDTHS)

    pdf.set_fill_color(244, 247, 255)
    pdf.set_draw_color(214, 224, 246)
    pdf.rect(12, 10, 186, 33, style="FD")
    pdf.set_fill_color(99, 116, 238)
    pdf.rect(12, 10, 186, 3, style="F")

    if banner_path:
        pdf.image(banner_path, x=16, y=15, w=44)

    pdf.set_text_color(25, 36, 73)
    pdf.set_xy(63, 15)
    pdf.set_font("helvetica", "B", 15)
    pdf.cell(120, 7, "Counselor Activity Scope Report", align="L")

    pdf.set_xy(63, 23)
    pdf.set_font("helvetica", "", 8.5)
    pdf.set_text_color(86, 98, 128)
    pdf.cell(120, 5, "RMKCET Shine - activity completion export", align="L")

    pdf.set_xy(63, 29)
    pdf.set_font("helvetica", "", 8)
    pdf.cell(120, 5, f"Generated: {generated_label}", align="L")

    pdf.set_fill_color(238, 242, 255)
    pdf.set_draw_color(210, 221, 248)
    pdf.rect(12, 48, 186, 12, style="FD")
    pdf.set_xy(16, 51.5)
    pdf.set_font("helvetica", "B", 9)
    pdf.set_text_color(53, 73, 135)
    pdf.cell(0, 0, f"{department}  |  {year_label(year_level)}  |  {semester_label(semester)}{chunk_label}")

    pdf.set_fill_color(98, 114, 235)
    pdf.set_text_color(255, 255, 255)
    pdf.rect(12, 64, 186, 13, style="FD")
    pdf.set_xy(16, 68)
    pdf.set_font("helvetica", "B", 10)
    pdf.cell(0, 0, shorten(test_name, 40))

    pdf.set_xy(16, 73)
    pdf.set_font("helvetica", "", 8)
    pdf.cell(
        0,
        0,
        (
            f"Counselors: {stats.get('total_counselors', 0)}   "
            f"Complete: {stats.get('complete', 0)}   "
            f"Pending: {stats.get('pending', 0)}   "
            f"Average: {stats.get('avg_completion', 0)}%"
        ),
    )

    pdf.set_xy(12, 83)
    pdf.set_font("helvetica", "B", 8)
    pdf.set_text_color(255, 255, 255)
    pdf.set_fill_color(44, 62, 122)
    for width, header in zip(COL_WIDTHS, HEADERS):
        pdf.cell(width, 7, header, border=1, align="C", fill=True)
    pdf.ln(7)

    pdf.set_x((page_width - content_width) / 2)


def draw_table_rows(pdf: FPDF, rows: list[dict]) -> None:
    pdf.set_font("helvetica", "", 8)
    pdf.set_text_color(25, 36, 73)

    if not rows:
        pdf.set_fill_color(250, 252, 255)
        pdf.cell(sum(COL_WIDTHS), 9, "No counselor rows available for this selection.", border=1, align="C", fill=True)
        pdf.ln(9)
        return

    for index, row in enumerate(rows):
        completion = int(round(float(row.get("completion_pct") or 0)))
        status = shorten(str(row.get("work_status") or "-").upper(), 12)
        last_login = shorten(str(row.get("last_login") or "Never"), 18)
        pending = int(round(float(row.get("pending_count") or 0)))

        pdf.set_fill_color(255, 255, 255 if index % 2 == 0 else 250)
        if index % 2 == 0:
            pdf.set_fill_color(255, 255, 255)
        else:
            pdf.set_fill_color(247, 249, 255)

        pdf.cell(COL_WIDTHS[0], ROW_HEIGHT, shorten(row.get("name") or "", 20), border=1, fill=True)
        pdf.cell(COL_WIDTHS[1], ROW_HEIGHT, shorten(row.get("email") or "", 34), border=1, fill=True)
        pdf.cell(COL_WIDTHS[2], ROW_HEIGHT, str(int(round(float(row.get("student_count") or 0)))), border=1, align="C", fill=True)
        pdf.cell(COL_WIDTHS[3], ROW_HEIGHT, str(int(round(float(row.get("unique_students_messaged") or 0)))), border=1, align="C", fill=True)
        pdf.cell(COL_WIDTHS[4], ROW_HEIGHT, str(pending), border=1, align="C", fill=True)
        pdf.cell(COL_WIDTHS[5], ROW_HEIGHT, f"{completion}%", border=1, align="C", fill=True)
        pdf.cell(COL_WIDTHS[6], ROW_HEIGHT, status, border=1, align="C", fill=True)
        pdf.cell(COL_WIDTHS[7], ROW_HEIGHT, last_login, border=1, align="C", fill=True)
        pdf.ln(ROW_HEIGHT)


def draw_page_footer(pdf: FPDF) -> None:
    pdf.set_y(-10)
    pdf.set_font("helvetica", "", 7.5)
    pdf.set_text_color(118, 128, 156)
    pdf.cell(0, 5, f"Page {pdf.page_no()}", align="R")


def build_pdf(payload: dict) -> bytes:
    sections = payload.get("sections") or []
    generated_at = payload.get("generated_at") or datetime.now().isoformat()
    try:
        generated_label = datetime.fromisoformat(str(generated_at).replace("Z", "+00:00")).strftime("%d %b %Y, %I:%M %p")
    except Exception:
        generated_label = datetime.now().strftime("%d %b %Y, %I:%M %p")

    grouped = defaultdict(list)
    for section in sections:
        key = (
            str(section.get("department") or "").strip().upper(),
            int(section.get("year_level") or 1),
            str(section.get("semester") or "").strip(),
        )
        grouped[key].append(section)

    pdf = FPDF(orientation="P", unit="mm", format="A4")
    pdf.set_auto_page_break(auto=False)
    pdf.set_margins(12, 10, 12)

    asset_root = Path(__file__).resolve().parents[2] / "client" / "public" / "assets"
    banner_path = flatten_image_for_pdf(asset_root / "banner.png") or flatten_image_for_pdf(asset_root / "shine-logo.png")

    try:
        for department, year_level, semester in sorted(grouped.keys(), key=lambda item: (item[0], item[1], item[2])):
            test_sections = sorted(
                grouped[(department, year_level, semester)],
                key=lambda item: TEST_ORDER.get(str(item.get("test_name") or "").strip().upper(), 99),
            )
            for section in test_sections:
                rows = section.get("rows") or []
                stats = section.get("stats") or {}
                chunk_count = max(1, int(math.ceil(len(rows) / float(ROWS_PER_PAGE))) if rows else 1)

                for chunk_index in range(chunk_count):
                    start = chunk_index * ROWS_PER_PAGE
                    chunk_rows = rows[start:start + ROWS_PER_PAGE]
                    chunk_label = f"  |  Part {chunk_index + 1} of {chunk_count}" if chunk_count > 1 else ""

                    pdf.add_page()
                    draw_page_header(
                        pdf,
                        banner_path,
                        generated_label,
                        department,
                        year_level,
                        semester,
                        str(section.get("test_name") or "").strip().upper(),
                        stats,
                        chunk_label,
                    )
                    draw_table_rows(pdf, chunk_rows)
                    draw_page_footer(pdf)
    finally:
        if banner_path:
            try:
                Path(banner_path).unlink(missing_ok=True)
            except Exception:
                pass

    return pdf_bytes(pdf)


def main() -> int:
    payload = json.load(sys.stdin)
    result = build_pdf(payload)
    sys.stdout.buffer.write(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
