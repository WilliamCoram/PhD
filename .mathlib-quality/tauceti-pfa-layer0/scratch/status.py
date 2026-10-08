# usage: python3 status.py "<note>" ID [ID ...]   -> marks tickets done (2026-09-29) with a Progress line
import re,sys
p='.mathlib-quality/tauceti-pfa-layer0/tickets.md'
s=open(p).read()
note=sys.argv[1]
for tid in sys.argv[2:]:
    m=re.search(r'^### \[%s\] .*\n- \*\*Status\*\*: ([^·]*)·'%re.escape(tid),s,re.M)
    assert m,tid
    a,b=m.span(1)
    s=s[:a]+'done (2026-09-29) '+s[b:]
    # append progress line after the status line
    e=s.index('\n',m.start()+len(m.group(0))-1)
    line_end=s.index('\n',s.index('- **Status**',m.start()))
    s=s[:line_end+1]+'- **Progress**: 2026-09-29 DONE — '+note+'\n'+s[line_end+1:]
open(p,'w').write(s)
