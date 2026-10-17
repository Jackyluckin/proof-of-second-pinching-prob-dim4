"""Check the static file hashes in input_manifest.json; no mathematical replay."""

from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import sys


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate manifest key: " + key)
        result[key] = value
    return result


def main():
    root = Path(__file__).resolve().parent
    try:
        manifest = json.loads(
            (root / "input_manifest.json").read_text(encoding="utf-8"),
            object_pairs_hook=unique_keys,
        )
        files = manifest["files"]
        if not isinstance(files, dict) or not files:
            raise ValueError("The manifest has no static-file entries.")
        failed = []
        for name, expected in files.items():
            relative = PurePosixPath(name)
            if relative.is_absolute() or ".." in relative.parts or "\\" in name:
                raise ValueError("Invalid manifest path: " + name)
            if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
                raise ValueError("Invalid SHA-256 entry: " + name)
            path = root.joinpath(*relative.parts).resolve()
            path.relative_to(root)
            if not path.is_file():
                failed.append((name, "missing"))
            elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                failed.append((name, "SHA-256 mismatch"))
        if failed:
            for name, reason in failed:
                print("FAIL: {} ({})".format(name, reason))
            return 1
        print("PASS: {} static-file hashes match.".format(len(files)))
        print("File integrity only; this does not run the mathematical verification.")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("FAIL: {}".format(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
