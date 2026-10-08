#!/usr/bin/env python3
"""List the declarations of the board's skeleton that use `sorry`, in source order, with the full
statement text. Output: scratch/sorries.json and a readable listing on stdout. Run from the repo root."""
import json, os, re
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
FILES = [D + f for f in ['NegLog.lean', 'RatLog.lean', 'Basic.lean', 'RankOne.lean', 'Commensurable.lean',
         'Discrete.lean', 'Normed.lean', 'Padic.lean', 'LaurentSeries.lean', 'Extension.lean',
         'PadicComplex.lean', 'Examples.lean']]
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
        d = i - 1
        doc = []
        while d >= 0 and (lines[d].startswith('@[') or lines[d].startswith('omit ') or lines[d].startswith('include ') or lines[d].startswith('open ') or lines[d].startswith('variable (') or lines[d].startswith('set_option')):
            d -= 1
        if d >= 0 and lines[d].rstrip().endswith('-/'):
            e = d
            while e >= 0 and not lines[e].lstrip().startswith('/--'):
                e -= 1
            doc = lines[e:d + 1]
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
        out.append(dict(file=f, line=i + 1, kind=kind, name=name, statement=st, doc='\n'.join(doc), sorries=text.count('sorry')))
json.dump(out, open('.mathlib-quality/tauceti-np-layer1/scratch/sorries.json', 'w'), indent=1, ensure_ascii=False)
cur = None
for o in out:
    if o['file'] != cur:
        cur = o['file']; print('\n##', cur)
    print(f"{o['line']:4d} {o['kind']:8s} {o['name']}  [{o['sorries']}]")
print('\nTOTAL declarations with sorry:', len(out), ' total sorries:', sum(o['sorries'] for o in out))
