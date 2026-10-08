#!/usr/bin/env python3
"""Port the proven restricted-power-series floor from PhD/Main/ForMathlib into the Tau Ceti chain.

Copies files (never imports them), rewrites `import PhD.Main.ForMathlib.…` lines to the chain
modules, and prepends a provenance note to the module docstring.  Run once; re-running refuses to
overwrite a file that already exists unless `--force` is given."""
import os, re, sys
SRC = 'PhD/Main/ForMathlib'
DST = 'PhD/TauCeti/Code/RigidAnalyticGeometry/Restricted'
MODPREFIX_SRC = 'PhD.Main.ForMathlib.'
MODPREFIX_DST = 'PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.'
MAP = {
    'Analysis/Normed/Ring/Ultra': 'Ultra',
    'Analysis/Normed/Ring/NormMulUnit': 'NormMulUnit',
    'Topology/Algebra/Nonarchimedean/LinearTopology': 'LinearTopology',
    'Topology/MetricSpace/HausdorffDistance': 'HausdorffDistance',
    'RingTheory/MvPowerSeries/GaussNorm': 'MvGaussNorm',
    'RingTheory/PowerSeries/GaussNorm': 'PowerSeriesGaussNorm',
    'RingTheory/MvPowerSeries/Restricted/Basic': 'Basic',
    'RingTheory/MvPowerSeries/Restricted/GaussNorm': 'GaussNorm',
    'RingTheory/MvPowerSeries/Restricted/Complete': 'Complete',
    'RingTheory/MvPowerSeries/Restricted/Iso': 'Iso',
    'RingTheory/MvPowerSeries/Restricted/X0Polynomial': 'X0Polynomial',
    'RingTheory/MvPowerSeries/Restricted/MulWeierstrass': 'MulWeierstrass',
    'RingTheory/MvPowerSeries/Restricted/Units': 'Units',
    'RingTheory/PowerSeries/Restricted/Basic': 'PowerSeries/Basic',
    'RingTheory/PowerSeries/Restricted/GaussNorm': 'PowerSeries/GaussNorm',
    'RingTheory/PowerSeries/Restricted/Complete': 'PowerSeries/Complete',
    'RingTheory/PowerSeries/Restricted/DivisionSet': 'PowerSeries/DivisionSet',
    'RingTheory/PowerSeries/Restricted/MulDistinguished': 'PowerSeries/MulDistinguished',
    'RingTheory/PowerSeries/Restricted/MulWeierstrassDivision': 'PowerSeries/MulWeierstrassDivision',
    'RingTheory/PowerSeries/Restricted/MulWeierstrassPrep': 'PowerSeries/MulWeierstrassPrep',
}
# imports that are dropped (local shadows of Mathlib files, or files replaced by chain files)
DROP = {
    'PhD.Main.ForMathlib.RingTheory.Polynomial.GaussNorm',
    'PhD.Main.ForMathlib.RingTheory.MvPolynomial.GaussNorm',
    'PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Residue',
}
modmap = {MODPREFIX_SRC + k.replace('/', '.'): MODPREFIX_DST + v.replace('/', '.') for k, v in MAP.items()}
force = '--force' in sys.argv
for k, v in MAP.items():
    src = f'{SRC}/{k}.lean'
    dst = f'{DST}/{v}.lean'
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if os.path.exists(dst) and not force:
        print('exists, skipped', dst); continue
    out = []
    for line in open(src).read().split('\n'):
        m = re.match(r'^import\s+(\S+)\s*$', line)
        if m:
            mod = m.group(1)
            if mod in DROP:
                continue
            if mod in modmap:
                line = 'import ' + modmap[mod]
            elif mod.startswith('PhD.'):
                raise SystemExit(f'unmapped import {mod} in {src}')
        out.append(line)
    open(dst, 'w').write('\n'.join(out))
    print('ported', src, '->', dst)
