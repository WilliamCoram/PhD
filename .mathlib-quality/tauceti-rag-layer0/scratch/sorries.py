#!/usr/bin/env python3
"""List the declarations of the board's skeleton that use `sorry`, in source order, with the full
statement text. Output: scratch/sorries.json and a readable listing on stdout."""
import json, os, re, subprocess, sys
FILES = [
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Basic.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Reduction.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Eval.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/EvalReduction.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/SupSeminorm.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/MaxModulus.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Distinguished.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Finiteness.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Chart.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Rueckert.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Rueckert.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Bald.lean',
 'PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/OrthonormalLift.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/StrictlyClosed.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/WeaklyStable.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/Japanese.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Stable.lean',
 'PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Examples.lean',
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
        while d >= 0 and (lines[d].startswith('@[') or lines[d].startswith('omit ') or lines[d].startswith('open ') or lines[d].startswith('variable (K n) in')):
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
json.dump(out, open('.mathlib-quality/tauceti-rag-layer0/scratch/sorries.json', 'w'), indent=1, ensure_ascii=False)
cur = None
tot = 0
for o in out:
    if o['file'] != cur:
        cur = o['file']
        print('\n##', cur)
    tot += 1
    print(f"  {o['line']:4d} {o['kind']:8s} {o['name']}" + (f"  [{o['sorries']} sorries]" if o['sorries'] > 1 else ''))
print('\nTOTAL declarations with sorry:', tot, ' total sorry tokens:', sum(o['sorries'] for o in out))
