import sys, glob
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
files = sys.argv[1:] or [p.split('/')[-1][:-5] for p in sorted(glob.glob(D + '*.lean'))]
n = 0
for f in files:
    for i, l in enumerate(open(D + f + '.lean').read().split('\n'), 1):
        if len(l) > 100:
            print(f'{f}:{i}: {len(l)}'); n += 1
print('long lines:', n)
