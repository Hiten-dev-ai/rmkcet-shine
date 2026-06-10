import io
import json
import sys
from pathlib import Path


def main():
    if len(sys.argv) < 3:
        raise RuntimeError("Usage: parse_marksheet.py <file_path> <original_filename>")

    file_path = Path(sys.argv[1]).resolve()
    original_filename = sys.argv[2]

    script_path = Path(__file__).resolve()
    workspace_root = script_path.parents[3]
    backend_root = workspace_root / "backend"

    sys.path.insert(0, str(backend_root))

    from core.intelligent_parser import IntelligentParser

    parser = IntelligentParser()
    with file_path.open("rb") as handle:
        file_bytes = handle.read()

    test_info, students = parser.parse_file(io.BytesIO(file_bytes), original_filename)
    payload = {
        "testInfo": test_info.to_dict(),
        "students": [student.to_dict() for student in students],
        "errors": parser.errors,
    }
    sys.stdout.write(json.dumps(payload))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        sys.stderr.write(str(exc))
        sys.exit(1)
