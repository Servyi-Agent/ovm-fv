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
    "sec-isdatadescriptor": "spec/6/2/6/2/spec.lean",
    "sec-isaccessordescriptor": "spec/6/2/6/3/spec.lean",
}
MARKERS = ["1.", "a.", "i.", "1.", "a."]

def spec_alg(clause_id):
    src = open(SPEC_HTML, encoding="utf-8").read()
    m = re.search(r'<emu-clause [^>]*?id=(?:"%s"|%s)(?=[\s>])[^>]*>' % (clause_id, clause_id), src)
    if not m:
        raise SystemExit(f"clause {clause_id} not found")
    end = src.find('</emu-clause>', m.end())
    seg = src[m.start():end]
    alg = re.search(r"<emu-alg>(.*?)</emu-alg>", seg, re.S).group(1)
    # Built spec: <ol><li> structure, numbering via CSS. Synthesize the
    # canonical markers (1. a. i. 1.) from the list nesting.
    toks = [(mm.start(), mm.end())
            for mm in re.finditer(r"<li\b[^>]*>|<ol>|</ol>", alg)]
    def fmt(depth, n):
        return MARKERS[depth] if depth < len(MARKERS) else "?"
    lines = []
    counters = []
    for k, (p, q) in enumerate(toks):
        tok = alg[p:q]
        if tok == "<ol>":
            counters.append(0)
        elif tok == "</ol>":
            if counters: counters.pop()
        else:  # <li ...>
            if not counters: counters = [0]
            counters[-1] += 1
            end = toks[k + 1][0] if k + 1 < len(toks) else len(alg)
            body = alg[q : end]
            body = re.sub(r"<ol>.*$", "", body, flags=re.S)  # drop nested list
            text = html.unescape(re.sub(r"<[^>]+>", "", body))
            text = text.replace("_", "").replace("*", "").strip()
            lines.append((fmt(len(counters) - 1, counters[-1]),
                          re.sub(r"\s+", "", text)))
    return lines

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
    # emu-val markers on our side: ~string~ -> string
    text = re.sub(r'~([\w.]+)~', r'\1', text)
    # cross-reference trailers ("See 20.3 for a description of X objects.")
    # are links, not algorithm text
    text = re.sub(r'See\d+(\.\d+)*foradescriptionof[\w-]+objects\.?$', '', text)
    text = re.sub(r'Seeforadescriptionof[\w-]+objects\.?$', '', text)
    return (mark, text)

def trans_alg(path):
    src = open(os.path.join(ROOT, path), encoding="utf-8").read()
    body = re.search(r"\[alg\|(.*)\]", src, re.S).group(1)
    out = []
    for raw in body.splitlines():
        m2 = re.match(r"^((?:┊\s*)*)(\w+)\.\s*(.*)$", raw.strip())
        if m2:
            d = raw.count("┊")
            t = re.sub(r"\s+", "", m2.group(3))
            t = re.sub(r"~([\w.]+)~", r"\1", t)   # emu-val markers
            out.append((MARKERS[d] if d < len(MARKERS) else "?", t))
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
