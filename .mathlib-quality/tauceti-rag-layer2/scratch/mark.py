#!/usr/bin/env python3
"""Usage: mark.py <ID> <status> "<progress note>" — set a ticket's Status and append a Progress line."""
import sys, datetime, re, os
tid, status, note = sys.argv[1], sys.argv[2], sys.argv[3]
p = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tickets.md')
s = open(p).read()
now = datetime.datetime.now().strftime('%Y-%m-%dT%H:%M')
head = f'### [{tid}]'
i = s.index(head)
j = s.index('\n- **Status**: ', i)
k = s.index(' · ', j)
st = f'done ({now[:10]})' if status == 'done' else (f'in_progress (started {now})' if status == 'in_progress' else status)
s = s[:j] + '\n- **Status**: ' + st + s[k:]
# progress line: after the Status line (and after an existing Progress line if any)
line_end = s.index('\n', j + 1)
nxt = s[line_end + 1:]
if nxt.startswith('- **Progress**: '):
    pe = s.index('\n', line_end + 1)
    s = s[:pe] + f' · {now}: {note}' + s[pe:]
else:
    s = s[:line_end + 1] + f'- **Progress**: {now}: {note}\n' + s[line_end + 1:]
open(p, 'w').write(s)
print(f'{tid} -> {st}')
