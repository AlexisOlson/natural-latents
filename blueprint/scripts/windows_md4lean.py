"""Enable MD4Lean's C entry-point exports for the Lean 4.34 Windows linker."""

import json
from pathlib import Path
import subprocess
import sys


def main() -> None:
    if sys.platform != "win32":
        return
    package = Path(__file__).resolve().parents[1]
    manifest = json.loads((package / "lake-manifest.json").read_text(encoding="utf-8"))
    pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "MD4Lean")
    dependency = package / ".lake" / "packages" / "MD4Lean"
    head = subprocess.check_output(
        ["git", "-C", str(dependency), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != pin:
        raise RuntimeError(f"MD4Lean checkout {head} differs from manifest pin {pin}")
    config = dependency / "lakefile.lean"
    source = config.read_bytes()
    newline = b"\r\n" if b"\r\n" in source else b"\n"
    marker = b"  -- Windows FFI exports for Lean 4.34 (blueprint/scripts/windows_md4lean.py)."
    if marker in source:
        print(f"MD4Lean Windows FFI exports already configured at {pin}.")
        return
    anchor = newline.join([
        b"lean_lib MD4Lean where", b"  precompileModules := true", b""
    ])
    if source.count(anchor) != 1:
        raise RuntimeError("Pinned MD4Lean library configuration has changed")
    replacement = anchor + newline.join([
        marker,
        b'  moreLinkArgs := #["-Wl,--export-all-symbols"]',
        b"",
    ])
    config.write_bytes(source.replace(anchor, replacement, 1))
    print(f"Configured MD4Lean Windows FFI exports at unchanged pin {pin}.")


if __name__ == "__main__":
    main()
