#!/usr/bin/env python3
"""Check that the root imports every project library source and the audit imports the root."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sources = sorted((ROOT / "CopelandErdos").rglob("*.lean"))
expected = {".".join(p.relative_to(ROOT).with_suffix("").parts) for p in sources}
root_text = (ROOT / "CopelandErdos.lean").read_text()
actual = set(re.findall(r"^import\s+(CopelandErdos(?:\.\w+)+)\s*$", root_text, re.M))
audit_text = (ROOT / "CopelandErdosAudit.lean").read_text()
errors = []
if actual != expected:
    errors.append(f"root import mismatch: missing={sorted(expected - actual)}, "
                  f"extra={sorted(actual - expected)}")
if not re.search(r"^import CopelandErdos\s*$", audit_text, re.M):
    errors.append("audit does not import CopelandErdos")
for path in sources + [ROOT / "CopelandErdos.lean"]:
    text = path.read_text()
    # This is a source hygiene check; the Lean audit is the authoritative axiom check.
    if re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", text):
        errors.append(f"forbidden source token in {path.relative_to(ROOT)}")
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"Lean inventory passed: {len(sources)} library source(s), root and audit connected")
