#!/usr/bin/env python3
"""List the declarations of the board's skeleton that use `sorry`, in source order, with the full
statement text. Output: scratch/sorries.json and a readable listing on stdout."""
import json, os, re, subprocess, sys
FILES = [
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/Seminorm.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/SpectralValue.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/Integral.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/Banach.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/BanachAlgebra/Module.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm/FunctionAlgebra.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/SupSeminorm.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/PowerBounded.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/Reduction.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/FunctionAlgebra.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/ReductionFunctor.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/SupExamples.lean',
]
KW = re.compile(r'^(@\[[^\]]*\]\s*)?(private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|class|example)\b')
out = []
for f in FILES:
    lines = open(f).read().split('\n')
    # declaration starts
    starts = [i for i, l in enumerate(lines) if KW.match(l)]
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        block = lines[i:j]
        text = '\n'.join(block)
        if 'sorry' not in text:
            continue
        # docstring: walk back
        d = i - 1
        doc = []
        # skip attribute/omit/open lines directly above
        while d >= 0 and (lines[d].startswith('@[') or lines[d].startswith('omit ') or lines[d].startswith('open ') or lines[d].startswith('variable (') or lines[d].startswith('set_option')):
            d -= 1
        if d >= 0 and lines[d].rstrip().endswith('-/'):
            e = d
            while e >= 0 and not lines[e].lstrip().startswith('/--'):
                e -= 1
            doc = lines[e:d + 1]
        # statement: up to ':= by' / 'where'
        stmt = []
        for l in block:
            stmt.append(l)
            if re.search(r':=\s*by\s*$', l) or re.search(r':=\s*$', l) or l.rstrip().endswith(' where'):
                break
        st = '\n'.join(stmt)
        st = re.sub(r'\s*:=\s*by\s*$', '', st)
        st = re.sub(r'\s*:=\s*$', '', st)
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|class|example)\s+([^\s:({\[]+)?', block[0])
        kind, name = m.group(1), (m.group(2) or '(anonymous)')
        nsorry = text.count('sorry')
        out.append(dict(file=f, line=i + 1, kind=kind, name=name, statement=st, doc='\n'.join(doc), sorries=nsorry))
json.dump(out, open('.mathlib-quality/tauceti-rag-layer2/scratch/sorries.json', 'w'), indent=1, ensure_ascii=False)
cur = None
tot = 0
for o in out:
    if o['file'] != cur:
        cur = o['file']
        print('\n##', cur)
    tot += 1
    print(f"  {o['line']:4d} {o['kind']:8s} {o['name']}" + (f"  [{o['sorries']} sorries]" if o['sorries'] > 1 else ''))
print('\nTOTAL declarations with sorry:', tot, ' total sorry tokens:', sum(o['sorries'] for o in out))
