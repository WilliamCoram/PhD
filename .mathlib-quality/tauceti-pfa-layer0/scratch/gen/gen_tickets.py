import re, sys
D='/Users/nkw24xru/Desktop/Lean/PhD/PhD/TauCeti/Code/PadicFunctionalAnalysis/'
cache={}
def lines(f):
    if f not in cache: cache[f]=open(D+f).read().split('\n')
    return cache[f]
KW=r'(?:theorem|lemma|def|noncomputable def|instance|noncomputable instance|abbrev|structure|class)'
def stmt(f,key):
    L=lines(f)
    pat=re.compile(r'^'+KW+r'\s+'+re.escape(key)+r'(?![\w.₀-₉\'])') if not key.startswith('RE:') else re.compile(key[3:])
    idx=[i for i,l in enumerate(L) if pat.search(l)]
    assert len(idx)==1, (f,key,len(idx))
    i=idx[0]; out=[]
    # include a preceding attribute line
    if i>0 and L[i-1].startswith('@['): out.append(L[i-1])
    while True:
        l=L[i]; out.append(l)
        if l.rstrip().endswith(' where') or l.strip()=='where':
            # a structure-valued definition: show its fields (up to the next blank line)
            j=i+1
            while j<len(L) and L[j].strip()!='' and L[j].startswith(' '):
                out.append(L[j]); j+=1
            return '\n'.join(out)
        if re.search(r':=\s*(by)?\s*$',l) or re.search(r':= ',l): break
        i+=1
    # strip trailing " := by" bodies for readability
    out[-1]=re.sub(r'\s*:=\s*by\s*$',' := by sorry',out[-1])
    return '\n'.join(out)
def block(f,keys):
    return '\n'.join(stmt(f,k) for k in keys)

T=[]  # tickets
def ticket(id,title,file,deps,par,typ,leaves,keys,sketch,mathlib,sources,gen,milestone=False):
    T.append(dict(id=id,title=title,file=file,deps=deps,par=par,typ=typ,leaves=leaves,keys=keys,sketch=sketch,mathlib=mathlib,sources=sources,gen=gen,milestone=milestone))
def cleanup(id,file,deps,note=''):
    T.append(dict(id=id,cleanup=True,file=file,deps=deps,note=note))

exec(open(sys.argv[1]).read())

out=[]
for t in T:
    if t.get('raw'):
        out.append(t['raw']); continue
    if t.get('cleanup'):
        if t['id'].startswith('CLEANUP-ALL') or t['id']=='CLEANUP-FINAL':
            out.append(f"### [{t['id']}] Run /cleanup-all on `PhD/TauCeti/Code/PadicFunctionalAnalysis/`\n- **Status**: open · **Depends on**: {t['deps']} · **Parallel**: no · **Type**: cleanup\n- {t['note']}\n")
        else:
            out.append(f"### [{t['id']}] Run /cleanup on `{t['file']}`\n- **Status**: open · **File**: `{t['file']}` · **Depends on**: {t['deps']} · **Parallel**: no · **Type**: cleanup\n- {t['note'] or 'Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.'}\n")
        continue
    ms=' · **MILESTONE**' if t['milestone'] else ''
    out.append(f"### [{t['id']}] {t['title']}\n- **Status**: open · **File**: `{t['file']}` · **Depends on**: {t['deps']} · **Parallel**: {t['par']} · **Type**: {t['typ']}{ms}\n- **Leaves**: {t['leaves']}\n\n#### Statement\n```lean\n{block(t['file'],t['keys'])}\n```\n#### Proof sketch\n{t['sketch']}\n#### Mathlib lemmas needed\n{t['mathlib']}\n#### Sources\n{t['sources']}\n#### Generality decision\n{t['gen']}\n")
open(sys.argv[2],'w').write('\n'.join(out))
print(len([t for t in T if not t.get('cleanup')]),'proof tickets;',len([t for t in T if t.get('cleanup')]),'cleanups')
