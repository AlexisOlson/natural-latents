"""Check that NaturalLatents/Statement.lean is byte-identical to the approved statement.

Exit 0 when the SHA-256 matches, 1 otherwise. The approved hash changes only with the owner's approval.
"""
import hashlib
import sys
from pathlib import Path

APPROVED = "c2be14d721fc4a3188a2cfe6beac9e62bd067d082c7f0078b81971ef1ccf6bfc"

path = Path(__file__).resolve().parent.parent / "NaturalLatents" / "Statement.lean"
digest = hashlib.sha256(path.read_bytes()).hexdigest()
if digest != APPROVED:
    print(f"Statement.lean changed: sha256 {digest}, approved {APPROVED}")
    sys.exit(1)
