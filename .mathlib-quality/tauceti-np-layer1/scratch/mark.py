#!/usr/bin/env python3
"""Mark tickets done in ../tickets.md: python3 mark.py ID [ID ...] with progress notes from NOTES."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(HERE, '..', 'tickets.md')
s = open(P).read()
NOTES = {}
exec(open(os.path.join(HERE, 'notes.py')).read())
for tid in sys.argv[1:]:
    m = re.search(r'### \[' + re.escape(tid) + r'\][^\n]*\n- \*\*Status\*\*: open', s)
    assert m, tid
    s = s[:m.end() - 4] + 'done (2026-10-06)' + s[m.end():]
    note = NOTES.get(tid)
    if note:
        # insert a Progress line after the status line
        i = s.index('\n', m.end()) + 1
        s = s[:i] + f'- **Progress**: {note}\n' + s[i:]
open(P, 'w').write(s)
print('marked', len(sys.argv) - 1)
