#!/usr/bin/env python3
"""Collect every backticked identifier in the tickets' "Mathlib lemmas needed" blocks and write a Lean file
`#check`ing each one against the pin."""
import re, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
txt = open(os.path.join(HERE, '..', 'tickets.md')).read()
names = set()
for m in re.finditer(r'#### Mathlib lemmas needed\n(.*?)\n#### Sources', txt, re.S):
    for n in re.findall(r'`([^`\s]+)`', m.group(1)):
        if re.match(r"^[A-Za-z_][\w.'₀₁₂₃₄₅₆₇₈₉ᵃ-ᵒ]*$", n):
            names.add(n)
proj = {n for _, _, n in json.load(open(os.path.join(HERE, 'fullnames.json')))}
proj_short = {n.split('.')[-1] for n in proj}
names = sorted(n for n in names if n not in proj)
with open(os.path.join(HERE, 'names_tickets_mathlib.lean'), 'w') as g:
    g.write('import PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples\n')
    for n in names:
        g.write(f'#check @{n}\n')
print(len(names), 'names written')
