#!/usr/bin/env python3
import sys
for f in sys.argv[1:]:
    for i, l in enumerate(open(f).read().split('\n'), 1):
        if len(l) > 100:
            print(f'{f}:{i}: {len(l)} codepoints')
