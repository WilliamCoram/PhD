#!/usr/bin/env python3
"""List every declaration (open or proved) of the board's files with its fully qualified name and
write `allsigs.lean` with `#check @name` for each, to audit dropped section variables."""
import re, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
FILES = json.load(open(os.path.join(HERE, 'files.json')))
KW = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure)\s+([^\s:({\[]+)')
out = ['import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples', '']
rows = []
for f in FILES:
    stack = []
    for i, l in enumerate(open(f).read().split('\n')):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'^section(\s+\S+)?\s*$', l)
        if m: stack.append(('sec', '')); continue
        m = re.match(r'^end(\s+\S+)?\s*$', l)
        if m and stack: stack.pop(); continue
        m = KW.match(l)
        if m and m.group(1) != 'instance':
            nm = m.group(2)
            ns = '.'.join(n for k, n in stack if k == 'ns')
            full = nm[len('_root_.'):] if nm.startswith('_root_.') else (ns + '.' + nm if ns else nm)
            rows.append((f, i + 1, full))
            out.append(f'#check @{full}')
open(os.path.join(HERE, 'allsigs.lean'), 'w').write('\n'.join(out) + '\n')
json.dump(rows, open(os.path.join(HERE, 'allnames.json'), 'w'), indent=0)
print(len(rows), 'declarations')
