#!/usr/bin/env python3
"""Text-equality audit: transcription vs the spec's emu-alg.

spec.html emu-algs are plain indented text (ecmarkdown): every step
marker is literally "1."; nesting is indentation. Depth is mapped
from indent buckets; markers canonicalized (1. a. i. 1.). Our side:
┊-prefixed lines, depth = marker count.
"""
import html, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC_HTML = "/tmp/opencode/spec/spec.html"
CASES = {
    "sec-iscallable":    "spec/6/2/5/1/spec.lean",
    "sec-isconstructor": "spec/6/2/5/2/spec.lean",
    "sec-toprimitive":   "spec/7/1/1/spec.lean",
    "sec-getmethod":     "spec/7/3/10/spec.lean",
    "sec-ordinaryget":   "spec/7/3/2/spec.lean",
    "sec-toobject":      "spec/7/1/13/spec.lean",
    "sec-getv":          "spec/7/3/1/spec.lean",
    "sec-ordinarytoprimitive": "spec/7/1/1/1/spec.lean",
}
MARKERS = ["1.", "a.", "i.", "1.", "a."]

def spec_alg(clause_id):
    src = open(SPEC_HTML, encoding="utf-8").read()
    m = re.search(r'<emu-clause id="%s".*?</emu-clause>' % clause_id, src, re.S)
    alg = re.search(r"<emu-alg>(.*?)</emu-alg>", m.group(0), re.S).group(1)
    text = html.unescape(re.sub(r"<[^>]+>", "", alg))
    lines = []
    for raw in text.splitlines():
        line = raw.replace("_", "").replace("*", "").strip()
        m2 = re.match(r"^(\d+)\.\s*(.*)$", line)
        if m2:
            lines.append((len(raw) - len(raw.lstrip()), m2.group(2)))
    # map indent widths to depth order
    widths = sorted({w for w, _ in lines})
    depth_of = {w: i for i, w in enumerate(widths)}
    return [(MARKERS[depth_of[w]], re.sub(r"\s+", "", t)) for w, t in lines]

# Documented deviations (text-equality exceptions):
# 1. zero-arg MOP calls `x.[[M]]()` -> field-read form (grammar can't
#    pattern-match empty parens)
DEVIATIONS = [
    ("sec-ordinaryget", ".[[GetPrototypeOf]]().", ".[[GetPrototypeOf]]."),
]

def apply_deviations(cid: str, step) -> tuple:
    mark, text = step
    for c, frm, to in DEVIATIONS:
        if c == cid:
            text = text.replace(frm, to)
    # cross-reference trailers ("See for a description of X objects.")
    # are links, not algorithm text
    import re as _re
    text = _re.sub(r'Seeforadescriptionof\w+objects\.?$', '', text)
    return (mark, text)

def trans_alg(path):
    src = open(os.path.join(ROOT, path), encoding="utf-8").read()
    body = re.search(r"\[alg\|(.*)\]", src, re.S).group(1)
    out = []
    for raw in body.splitlines():
        m2 = re.match(r"^((?:┊\s*)*)(\w+)\.\s*(.*)$", raw.strip())
        if m2:
            d = raw.count("┊")
            out.append((MARKERS[d] if d < len(MARKERS) else "?", re.sub(r"\s+", "", m2.group(3))))
    return out

fail = 0
for cid, path in sorted(CASES.items()):
    a, b = spec_alg(cid), trans_alg(path)
    a = [apply_deviations(cid, s) for s in a]
    if a == b:
        print(f"EQUAL  {cid:22s} {path}  ({len(a)} steps)")
    else:
        fail += 1
        print(f"DIFF   {cid:22s} {path}")
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                print(f"  first divergence at step {i}:")
                print(f"    spec: {x}")
                print(f"    ours: {y}")
                break
        else:
            print(f"  step count: spec {len(a)}, ours {len(b)}")
            if a: print(f"    last spec step: {a[-1]}")
            if b: print(f"    last ours step: {b[-1]}")
sys.exit(1 if fail else 0)
