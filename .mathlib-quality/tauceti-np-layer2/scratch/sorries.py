#!/usr/bin/env python3
"""List the declarations of the board's skeleton that use `sorry`, in source order, with the full
statement text. Output: scratch/sorries.json and a readable listing on stdout. Run from the repo root."""
import json, os, re
D = 'PhD/TauCeti/Code/NewtonPolygons/Coeff/'
FILES = [D + f for f in ['NormedAddValuation.lean', 'Generic.lean', 'CoeffVal.lean', 'PowerSeries.lean',
         'Polynomial.lean', 'Extension.lean', 'SupportValue.lean', 'GaussNorm.lean', 'Pure.lean',
         'Distinguished.lean', 'Padic.lean', 'Examples.lean']]
KW = re.compile(r'^(@\[[^\]]*\]\s*)?(private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|class|example)\b')
out = []
for f in FILES:
    lines = open(f).read().split('\n')
    starts = [i for i, l in enumerate(lines) if KW.match(l)]
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        block = lines[i:j]
        text = '\n'.join(block)
        if 'sorry' not in text:
            continue
        stmt = []
        for l in block:
            stmt.append(l)
            if re.search(r':=\s*by\s*$', l) or re.search(r':=\s*$', l) or l.rstrip().endswith(' where') or re.search(r':=\s*by sorry\s*$', l):
                break
        st = '\n'.join(stmt)
        st = re.sub(r'\s*:=\s*by sorry\s*$', '', st)
        st = re.sub(r'\s*:=\s*by\s*$', '', st)
        st = re.sub(r'\s*:=\s*$', '', st)
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|class|example)\s+([^\s:({\[]+)?', block[0])
        kind, name = m.group(1), (m.group(2) or '(anonymous)')
        out.append(dict(file=f, line=i + 1, kind=kind, name=name, statement=st, sorries=text.count('sorry')))
os.makedirs('.mathlib-quality/tauceti-np-layer2/scratch', exist_ok=True)
json.dump(out, open('.mathlib-quality/tauceti-np-layer2/scratch/sorries.json', 'w'), indent=1, ensure_ascii=False)
cur = None
for o in out:
    if o['file'] != cur:
        cur = o['file']; print('\n##', cur)
    print(f"{o['line']:4d} {o['kind']:8s} {o['name']}  [{o['sorries']}]")
print('\nTOTAL declarations with sorry:', len(out), ' total sorries:', sum(o['sorries'] for o in out))
