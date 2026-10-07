#!/usr/bin/env python3
"""Lightweight source-hygiene checks for the TeX validation ledger.

This does not replace a TeX build. It catches accidental control characters
introduced by escaping backslashes while updating LaTeX through JSON/JS.
"""
from pathlib import Path
import sys

filename = Path('audit.tex')
raw = filename.read_bytes()
try:
    content = raw.decode('utf-8')
except UnicodeDecodeError as exc:
    raise SystemExit(f'FAIL: audit.tex is not UTF-8: {exc}') from exc

bad = [(i, byte) for i, byte in enumerate(raw)
       if byte < 32 and byte not in (10, 13)]
if bad:
    print('FAIL: forbidden ASCII control character(s) in audit.tex:', file=sys.stderr)
    for pos, byte in bad[:12]:
        line = raw[:pos].count(b'\n') + 1
        print(f'  line {line}: byte 0x{byte:02x}', file=sys.stderr)
    sys.exit(1)

for fragment in ('\\begin{document}', '\\end{document}',
                 '\\subsection{Lemma 27}', '\\subsection{Theorem 13 gluing}'):
    if fragment not in content:
        raise SystemExit(f'FAIL: audit.tex is missing {fragment!r}')

if 'b^{,n-M}' in content:
    raise SystemExit('FAIL: malformed tree-height exponent in audit.tex')

print('PASS: audit.tex UTF-8 and control-character checks')
