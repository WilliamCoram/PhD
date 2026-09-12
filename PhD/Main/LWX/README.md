# `PhD/Main/LWX/` — reading order and file guide

Liu–Wan–Xiao's spectral halo for overconvergent quaternionic modular forms
(*Liu–Wan–Xiao, The eigencurve over the boundary of weight space*), formalised for `p ≠ 2`:
the halo estimate [LWX, Thm 3.16, Cor 3.18], the integral model and the seam with the genuine
`U_p`, the vertex analysis of [LWX, Thm 1.3], the slope theorems of [LWX, Thm 1.5], Steps I and
III of [LWX, §3.23] (Atkin–Lehner and the theta operator), and the degree formulas with
[LWX, Cor 1.4].  Everything is granted the adelic Atkin–Lehner data (`22_AtkinLehnerFamily.lean`);
nothing uses Jacquet–Langlands — see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.

Blueprint chapters: `blueprint/src/chapter/LWXHalo.tex`, `LWXModel.tex`, `LWXSlopes.tex`.
Boards: `.mathlib-quality/lwx-halo/`, `lwx-slopes/`, `lwx-seam/`, `lwx-seam-m/`, `lwx-theta/`,
`lwx-theta-h2/`, `lwx-h1/`, `lwx-conductor/`, `lwx-degrees/`.

## How the numbering works

Each filename carries **its depth in this folder's own import graph**: a file `NN_Name.lean`
imports only files of this folder with a strictly smaller `NN` (plus modules from `PhD/Main/TateFredholm/`, `PhD/Main/QMF/`, `PhD/Main/NewtonPolygons/` and `PhD/Main/ForMathlib/`).  Files that share a number
are independent of one another and can be read in any order.  Because the module names start with a
digit they are imported in French quotes:

```lean
import PhD.Main.LWX.«24_DegreePeriodicity»
```

## Reading order

- **00** — `Colmez`, `HaloRing`, `PadicExpLog`
- **01** — `AmiceValuation`, `Binomial`, `HaloTate`, `UnitsLog`
- **02** — `TiltedDegree`
- **03** — `UpMatrix`
- **04** — `Halo`, `IntegralModel`
- **05** — `AtkinLehner`, `Certificates`, `Sharpness`, `Specialize`, `TateRiesz`, `UpperPolygon`
- **06** — `Claim`, `HaloWeight`, `Vertices`
- **07** — `ConjChar`, `Degrees`, `PowSubOne`, `Seam`, `SlopeRatios`
- **08** — `AmiceBasis`, `HaloWeightH`, `Quaternionic`, `SlopeGrowth`
- **09** — `DiscModel`
- **10** — `AtkinLehnerLocal`, `DiscForms`
- **11** — `AtkinLehnerLocalH`, `SeamH`, `Theta`
- **12** — `Bol`, `QuaternionicH`, `StepOne`
- **13** — `AtkinLehnerInst`, `SlopesSeam`
- **14** — `Touching`
- **15** — `ClassicalPoint`, `StepThree`, `SymPow`, `TouchingH`
- **16** — `TargetPoint`, `ThetaExact`
- **17** — `ClassicalPointH`, `DegreeFormula`, `NebChar`
- **18** — `AtkinLehnerMap`, `TargetPointH`
- **19** — `AtkinLehnerIdentity`, `NebCharH`
- **20** — `AtkinLehnerMapH`
- **21** — `AtkinLehnerIdentityH`
- **22** — `AtkinLehnerFamily`
- **23** — `ConductorSlopes`
- **24** — `DegreePeriodicity`

## Files

| file | imports in this folder | what it is |
|---|---|---|
| `00_Colmez.lean` | — *(+ QMF, TateFredholm)* | Colmez's basis of the Tate algebra, and the Mahler coordinates of monomials |
| `00_HaloRing.lean` | — *(+ TateFredholm)* | The integral halo ring `Λ^{>1/p}` |
| `00_PadicExpLog.lean` | — | `p`-adic exponential and logarithm on `1`-units (odd `p`) |
| `01_AmiceValuation.lean` | `00_PadicExpLog` | The disc-restricted Colmez polynomials and their `p`-adic valuations |
| `01_Binomial.lean` | `00_PadicExpLog` *(+ QMF)* | The `p`-adic binomial theorem for an arbitrary exponent |
| `01_HaloTate.lean` | `00_HaloRing` | The Banach–Tate ring `A = Λ^{>1/p}[1/T]` |
| `01_UnitsLog.lean` | `00_PadicExpLog` *(+ TateFredholm)* | Teichmüller lift and the normalised logarithm at odd `p` |
| `02_TiltedDegree.lean` | `01_UnitsLog` | Tilted degree: the Mahler calculus of [LWX] §3.3–§3.13 |
| `03_UpMatrix.lean` | `00_HaloRing`, `02_TiltedDegree` *(+ TateFredholm)* | The integral `U_p`-matrix |
| `04_Halo.lean` | `03_UpMatrix` *(+ NewtonPolygons, TateFredholm)* | The halo estimate: [LWX] Theorem 3.16 and Corollary 3.18 |
| `04_IntegralModel.lean` | `03_UpMatrix` *(+ QMF, TateFredholm)* | The integral model `S^D_int` |
| `05_AtkinLehner.lean` | `04_IntegralModel` *(+ TateFredholm)* | The Atkin–Lehner element, and the reduction of [LWX, Prop 3.22] |
| `05_Certificates.lean` | `04_Halo`, `04_IntegralModel` *(+ QMF)* | `U_p` on `S^D_int` from coset certificates: [LWX, Prop 3.1] in full |
| `05_Sharpness.lean` | `04_Halo` | Sharpness of the halo estimate: [LWX, Cor 3.18]'s equality clause |
| `05_Specialize.lean` | `04_IntegralModel` | Specialization of `Λ^{>1/p}` at a halo point, as a continuous ring homomorphism |
| `05_TateRiesz.lean` | `01_HaloTate`, `04_Halo` *(+ TateFredholm)* | The halo `U_p` over the Tate ring `A`: Riesz theory at a vertex |
| `05_UpperPolygon.lean` | `04_Halo` | The upper bound polygon and [LWX, Lemma 4.1] |
| `06_Claim.lean` | `05_Sharpness`, `05_UpperPolygon` | The Claim of [LWX, §4.2] |
| `06_HaloWeight.lean` | `01_Binomial`, `05_Specialize` | The halo weight `κ_{T₀}` as an analytic weight |
| `06_Vertices.lean` | `05_Sharpness`, `05_UpperPolygon` *(+ NewtonPolygons)* | The vertex analysis of [LWX, Theorem 1.3, proof Step II] |
| `07_ConjChar.lean` | `06_Vertices` | The conjugate nebentypus `ω⁻¹` |
| `07_Degrees.lean` | `06_Vertices` | Step III of [LWX, Theorem 1.3]: the ordinary dimension at the coefficient level |
| `07_PowSubOne.lean` | `06_HaloWeight` | `(1+T)^{pʰ}` and the binomial power identity |
| `07_Seam.lean` | `00_Colmez`, `05_Certificates`, `06_HaloWeight` *(+ QMF, TateFredholm)* | [LWX, Proposition 2.17]: the integral `Char(P)` specialises to `Char(U_p; S^{D,†,1})` |
| `07_SlopeRatios.lean` | `06_Claim`, `06_Vertices` | Slope ratios near the boundary: [LWX, Theorem 1.5], first half |
| `08_AmiceBasis.lean` | `01_AmiceValuation`, `07_PowSubOne` *(+ TateFredholm)* | Amice's theorem at level `h`: the Colmez basis of the disc model |
| `08_HaloWeightH.lean` | `07_PowSubOne` | The halo weight at analyticity level `h` |
| `08_Quaternionic.lean` | `07_Seam` *(+ ForMathlib, QMF)* | The integral model for a definite quaternion algebra over `ℚ` |
| `08_SlopeGrowth.lean` | `07_SlopeRatios` | The slope ratios increase to infinity |
| `09_DiscModel.lean` | `07_Seam`, `08_AmiceBasis`, `08_HaloWeightH` | The disc model of the induced representation at level `h`, and the `M₁`-action |
| `10_AtkinLehnerLocal.lean` | `05_AtkinLehner`, `09_DiscModel` | The local matrix identities behind `U_p ∘ U'_p = p^{k+1}` |
| `10_DiscForms.lean` | `05_Certificates`, `09_DiscModel` *(+ QMF)* | `S^{D,†,m}` in the disc model, and `U_p` on it |
| `11_AtkinLehnerLocalH.lean` | `10_AtkinLehnerLocal` | The local matrix identities behind `U_p ∘ U'_p = p^{k+1}` at conductor `p^{h+1}` |
| `11_SeamH.lean` | `07_Seam`, `10_DiscForms` *(+ TateFredholm)* | [LWX, Proposition 2.17] at every analyticity level |
| `11_Theta.lean` | `10_DiscForms` *(+ TateFredholm)* | The theta operator on the disc model, and the classical subspace |
| `12_Bol.lean` | `11_Theta` | Bol's identity, and the repaired theta equivariance |
| `12_QuaternionicH.lean` | `08_Quaternionic`, `11_SeamH` | `S^{D,†,m}` and [LWX, Prop 2.17] for a definite quaternion algebra over `ℚ` |
| `12_StepOne.lean` | `06_Vertices`, `07_ConjChar`, `11_Theta` | Step I of [LWX, Theorem 1.3]: the touching |
| `13_AtkinLehnerInst.lean` | `05_AtkinLehner`, `12_Bol`, `12_StepOne` | Instantiating the Atkin–Lehner reduction at the classical space |
| `13_SlopesSeam.lean` | `07_SlopeRatios`, `12_QuaternionicH` | The halo estimates and slope theorems, read on the genuine `U_p` |
| `14_Touching.lean` | `13_AtkinLehnerInst`, `13_SlopesSeam` *(+ NewtonPolygons, QMF, TateFredholm)* | Step I of [LWX, Theorem 1.3]: the squeeze |
| `15_ClassicalPoint.lean` | `14_Touching` | Classical points of the halo |
| `15_StepThree.lean` | `05_TateRiesz`, `07_Degrees`, `14_Touching` *(+ NewtonPolygons, TateFredholm)* | Step III of [LWX, Theorem 1.3]: the degrees |
| `15_SymPow.lean` | `14_Touching` | The `Sym^k` action on polynomials of degree `≤ k` |
| `15_TouchingH.lean` | `14_Touching` | Step I of [LWX, Theorem 1.3] at conductor `p^{h+1}` |
| `16_TargetPoint.lean` | `15_ClassicalPoint`, `15_StepThree` | The theta target of a classical point |
| `16_ThetaExact.lean` | `15_StepThree` *(+ TateFredholm)* | Hypothesis H2 from the classical shapes |
| `17_ClassicalPointH.lean` | `15_TouchingH`, `16_TargetPoint` | Classical points of conductor `p^{h+1}` |
| `17_DegreeFormula.lean` | `16_TargetPoint`, `16_ThetaExact` | The degree formula granted H1 alone |
| `17_NebChar.lean` | `16_TargetPoint` | The nebentypus character at a classical point |
| `18_AtkinLehnerMap.lean` | `10_AtkinLehnerLocal`, `15_SymPow`, `17_NebChar` | The Atkin–Lehner map on classical disc forms |
| `18_TargetPointH.lean` | `17_ClassicalPointH` | The theta target of a classical point of conductor `p^{h+1}` |
| `19_AtkinLehnerIdentity.lean` | `17_DegreeFormula`, `18_AtkinLehnerMap` | `U_p ∘ U'_p = p^{k+1}` and hypothesis H1 |
| `19_NebCharH.lean` | `17_NebChar`, `18_TargetPointH` | The nebentypus character at a classical point of conductor `p^{h+1}` |
| `20_AtkinLehnerMapH.lean` | `11_AtkinLehnerLocalH`, `18_AtkinLehnerMap`, `19_NebCharH` | The Atkin–Lehner map on classical disc forms at conductor `p^{h+1}` |
| `21_AtkinLehnerIdentityH.lean` | `19_AtkinLehnerIdentity`, `20_AtkinLehnerMapH` | `U_p ∘ U'_p = p^{k+1}` and hypothesis H1 at conductor `p^{h+1}` |
| `22_AtkinLehnerFamily.lean` | `21_AtkinLehnerIdentityH` | The Atkin–Lehner data at every classical weight |
| `23_ConductorSlopes.lean` | `13_SlopesSeam`, `22_AtkinLehnerFamily` *(+ NewtonPolygons)* | The slope reflection at conductor `p^{h+1}` |
| `24_DegreePeriodicity.lean` | `23_ConductorSlopes` | The degrees at every classical weight, and [LWX, Corollary 1.4] |
