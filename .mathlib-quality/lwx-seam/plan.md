# Development Plan: the LWX model seam (Prop 2.17 at `m = 1`, Prop 3.1 in full for `D/ℚ`)

**BOARD PATH: `.mathlib-quality/lwx-seam/`** — named board.  The default `.mathlib-quality/`
root belongs to the (completed) NewtonPolygons project; the sibling boards
`.mathlib-quality/lwx-halo/` (Tier 1, complete) and `.mathlib-quality/lwx-slopes/` (complete) are
upstream and are *not* edited here.  **`.mathlib-quality/tate-riesz/` is being executed
concurrently by another agent**: never touch its files — `PhD/LWX/HaloRing.lean`,
`PhD/LWX/HaloTate.lean`, `PhD/LWX/TateRiesz.lean`, `PhD/LWX/PadicExpLog.lean`,
`PhD/TateFredholm/{Coleman,Entire,Pr,Resultant,RieszColeman,SlopeFactor}.lean`, nor its
`beastmode_active` sentinel — and never run `/cleanup` on them.  Every `/beastmode` invocation for
this project must name this path.

Planned 2026-09-05.  Source: Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*
(arXiv:1412.2584v4; cite as [LWX]; printed page = PDF page).  Secondary locators `lwx.txt:NNNN`
refer to the `pypdf` text extraction (36 pages) at
`/private/tmp/claude-1289761130/-Users-nkw24xru-Desktop-Lean-PhD/cffac1cb-ccae-4c29-b859-1624affd9629/scratchpad/lwx.txt`
— regenerate from `~/Desktop/Papers/Liu, Wan, Xiao - The eigencurve over the boundary of weight
space.pdf` with `pypdf.PdfReader(...).pages[i].extract_text()`, one `===== PDF PAGE i =====`
banner per page.  Other references: [Colmez, Astérisque 330 (2010), Thm 1.29], [Koblitz, Ch. IV
§2], [Buzzard, *Eigenvarieties*, Cor 2.6, Lemma 12.2], [Jacobs, Def 1.27, pp. 20–21], mathlib.

## Goal

Close the two seams left open by `lwx-halo` (its `plan.md` §"Still deferred": items 1 and 3):

1. **[LWX, Proposition 2.17] at `m = 1`.**  For an odd prime `p`, an isometric
   `ψ : ℚ_p → K` into a complete ultrametric field, a halo point `T₀` on the **sub-annulus**
   `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹` (`1/2 < v(T₀) < 1`), a tame-level datum `(θ, U, hU)` and
   right-coset certificates `(vRep, idx, u)` with `U_p`-shaped matrices:
   `specCharSeries (UpDatum.ofCerts …) ω ψ T₀ = QMF.Weight.heckeCharPowerSeries θ_K (haloWeight …) U … vRep … idx u`
   — the integral `Char(P)` of [LWX, Thm 3.16] evaluated at `T₀` is the Fredholm determinant of
   `U_p` on the overconvergent forms of the halo weight (**`Seam.lean`,
   `specCharSeries_ofCerts_eq_heckeCharPowerSeries`**).  The halo weight `κ_{T₀} = [−](T₀)` is
   built as a `QMF.AnalyticWeight` (`HaloWeight.lean`), which needs the `p`-adic binomial theorem
   for an arbitrary exponent (`Binomial.lean`), Colmez's basis as an isometric equivalence of the
   Tate algebra (`Colmez.lean`), the specialization as a continuous ring homomorphism
   (`Specialize.lean`) and two general TateFredholm facts (`Conjugation.lean`).
2. **[LWX, Proposition 3.1] in full, and the quaternionic instance.**  The integral
   `U_p = [UηU]` on `S^D_int` (`intHeckeOperator`), the `UpDatum` of a certificate system
   (`UpDatum.ofCerts`) with the shape clause derived from `Iw·(p 0;0 1)·Iw`, the commutative
   diagram `intEvalAtReps ∘ U_p = (ofCerts).op ω ∘ intEvalAtReps`, and (2.11.1) at a neat level
   (**`Certificates.lean`**).  Then, for a definite quaternion algebra `D/ℚ` split at `p`
   (`RigidificationAt ℚ D (p)`), with mathlib's comparison `ℚ_p ≅ ℚ_{(p)}` shown to be an isometry
   at every prime (**`ForMathlib/…/AdicCompletionEquiv.lean`**): `IntFormsQ` is `S^D_int`, the QMF
   side is literally Buzzard's `FormsQ ℚ D v κ U`, and the two milestones
   **`specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ`** (Prop 2.17 for `D/ℚ`) and
   **`evalT_specCharSeries_eq_zero_iff`** — at a neat level, for `a ≠ 0`, `Char(P)(T₀)(a) = 0` iff
   `a⁻¹` is a `U_p`-eigenvalue on `S^D_{κ_{T₀}}(U)` (the fibre of [LWX, Def 2.13]'s spectral curve
   over a halo point) (**`Quaternionic.lean`**).

**Out of scope (recorded so nobody re-litigates):** `m ≥ 2` (functions analytic on
`a + p^{m−1}ℤ_p`; needs [Bu04, Lemma 4]'s level change `Iw_p ↔ Iw_{p^m}` to reach the Tate-algebra
layer), hence the boundary region `v(T₀) ≤ 1/2` — in particular the annulus of [LWX, §4.2]'s Claim;
`p = 2`; the sharp `1`-analyticity radius `v(T₀) > 1/(p−1)` (we use the joint-disc `v(T₀) > 1/2`
that `PadicExpLog.lean` supports — sharp for `p = 3`); existence of certificates for a given tame
level (data; Fujisaki finiteness `classSetFintype` and `finite_image_etaAdelic'_of_isOpen_of_isCompact`
are available for the hypotheses); the rigid-analytic spectral curve; the `ℤ_p[Δ]` factor (per-`ω`
as in lwx-halo); tame Hecke operators; anything on the `tate-riesz` board.

## Architecture (planning-time findings)

Verified against the code on 2026-09-05 (every name below was read in its file):

| Need | Have | Where |
|---|---|---|
| integral `U_p` matrix, its `charCoeff`, well-definedness | `UpDatum.op/matrix`, `matrixCoeff_op`, `summable_minor_upOp`, `norm_charCoeff_upOp_le` | `PhD/LWX/{UpMatrix,Halo}.lean` |
| specialized series | `specCharSeries D ω ψ T₀ = mk (n ↦ specialize ψ T₀ (charCoeff (D.op ω) n))`, `HaloInt.specialize`, `summable_specialize`, `norm_specialize_le`, `specialize_one` | `Halo.lean:157`, `HaloRing.lean:594–711` |
| (2.3.2), Prop 3.4 as a theorem, the seam | `cfunSlash`, `mahlerON/_apply`, `mahlerCoeffs/_apply`, `seqSlashAction`, `seqSlash_coeff`, `mahlerON_seqSlash`, `IntForms`, `intEvalAtReps/_apply`, `intEvalAtReps_comm`, `M1`, `M1.toLocalMat`, `levelM1`, `levelM1ToM1` | `IntegralModel.lean` |
| universal character | `univChar ω a = const (ω ā) * oneAddTPow p (logQuot a)`, `univChar_mul`, `coeff_oneAddTPow`, `logQuot`, `coe_logQuot`, `teichmuller/_mul/_eq_of_norm_sub_le`, `oneUnitPart`, `qlog` | `IntegralModel.lean:58–218`, `UnitsLog.lean` |
| exp/log over `K`, odd `p` | `padicLog/padicExp`, `padicLog_mul`, `padicExp_add`, `padicExp_natCast_mul`, `padicExp_padicLog`, `norm_padicLog_eq`, `sq_norm_factorial_ge` (joint disc `‖·‖² < ‖p‖`) | `PadicExpLog.lean` (frozen; read-only) |
| QMF weight interface | `ExpansionData S ρ U κ` (fields `bounds/col/rowDecay/mem_level/eval`), `AnalyticWeight`, `LevelBounds`, `kappaSlash`, `kappaSlash_apply`, `matrixCoeff_kappaSlash`, `autFactor = col * linX⁻¹^2`, `linX/numX/mobius`, `evalAt/_mul/_pow/_mobius/_linX_inv`, `absSummable_autFactor/_mobius`, `AnalyticWeight.isCompactoid_kappaSlash` | `QMF/Weight/{Char,Series,SlashAction}.lean` |
| QMF forms/Hecke | `levelMonoidOf`, `levelMonoidOfToS`, `Forms`, `heckeOperator`, `heckeBlock`, `heckeBlockOp`, `heckeCharPowerSeries = charPowerSeries (heckeBlockOp …)`, `evalT_heckeCharPowerSeries_eq_zero_iff` (general `σ`), `bijective_evalAtReps_of_stabilizer_eq_bot` | `QMF/Weight/{Forms,Compact,Fredholm}.lean` |
| quaternionic layer | `Dfx`, `globalUnits`, `RigidificationAt`, `toMatrix`, `etaAdelic'`, `toMatrix_etaAdelic'`, `FormsQ`, `heckeUpiQ`, `classSetFintype` | `QMF/{Quaternionic,Slash/Quaternionic,Weight/Quaternionic}.lean` |
| ring-generic Hecke layer | `slashFixedPointsOfLE`, `heckeOperatorSlash`, `heckeOperatorSlash_apply_rep`, `exists_mul_eta_mul_of_bijOn`, `bijective_evalAtRepsSlash`, `stabilizerAtSlash` | `QMF/Slash/{HeckeMonoid,HeckeMatrix}.lean`, `Weight/Compact.lean:221` |
| TateFredholm | `minor`, `charCoeff` (`(−1)^n * ∑' S, minor`), `charPowerSeries`, `matrixCoeff`, `ext_matrixCoeff`, `matrixCoeff_comp`, `ofCoeffs/_apply`, `matrixCoeff_ofCoeffs`, `blockOp`, `matrixCoeff_blockOp`, `blockOp_comp`, `isCompactoid_blockOp`, `IsCompactoid.comp_left/right/finset_sum/smul`, `charPowerSeries_conj`, `cSpace.single/hasSum_single/ofTendsto/blockIncl/blockProj` | `TateFredholm/{Fredholm,Matrix,GenFun,BlockOp,ModelSpace}.lean` |
| mathlib | `fwdDiff` (`Δ_[h]`, scoped `fwdDiff`), `fwdDiff_iter_eq_sum_shift`, `shift_eq_sum_fwdDiff_iter`, `fwdDiff_iter_pow_eq_zero_of_lt`, `fwdDiff_iter_eq_factorial`, `fwdDiff_iter_choose_zero`, `descPochhammer`, `descPochhammer_eval_eq_descFactorial`, `monic_descPochhammer`, `descPochhammer_natDegree`, `Ring.choose`, `Ring.choose_natCast`, `Ring.add_choose_eq` (Chu–Vandermonde), `Ring.descPochhammer_eq_factorial_smul_choose`, `BinomialRing ℤ_[p]` (MahlerBasis.lean:78), `BinomialRing K` via `Module ℚ≥0 K` (Binomial.lean:277), `PadicInt.denseRange_natCast`, `PadicInt.mahler`, `Padic.adicCompletionEquiv`, `PadicInt.adicCompletionIntegersEquiv`, `Rat.HeightOneSpectrum.primesEquiv/natGenerator/span_natGenerator`, `Polynomial.eq_of_infinite_eval_eq`, `RingHom.map_det`, `RingHom.mapMatrix`, `ContinuousLinearEquiv.equivOfInverse`, `IsFractionRing ℤ_[p] ℚ_[p]` | verified by grep on 2026-09-05 |

**Design decisions.**

1. **`m = 1` on the sub-annulus.**  The general-weight layer's coefficient module is the Tate
   algebra `c(ℕ, K)` (analytic on the closed unit disc) = [LWX]'s `OB_{qp^{−m}}` at `m = 1`.  The
   halo weight is `1`-analytic iff `‖log(1+T₀)‖ < p^{−1/(p−1)}`; we take the joint-disc form
   `‖T₀‖² < p⁻¹` (`PadicExpLog.lean`'s convergence discs), i.e. `1/2 < v(T₀) < 1`.  Everything is
   stated with the two hypotheses `h0 : p⁻¹ < ‖T₀‖`, `h1 : ‖T₀‖² < p⁻¹`.
2. **The QMF character is `x ↦ x²·κ_{T₀}(x)`** on `haloUnits ψ = ψ(ℤ_p^×)(1 + p𝒪_K)`, level
   `M1K ψ = ψ(M₁)`, radius `ρ = ‖T₀‖√p`; [Jacobs, Def 1.27]'s `(cz+d)^{−2}` then cancels and the
   automorphy factor is [LWX, (2.3.2)]'s `χ(cz+d)`.  The column is the explicit
   `(cz+d)²·κ(d)·∑_m C(s,m)(c/d)^m z^m`, `s = log(1+T₀)/p` ("`κ(1+wz) = (1+wz)^s`"), so row decay
   is a direct estimate and evaluation is the binomial theorem.
3. **The binomial theorem for an arbitrary exponent** (`Binomial.lean`) is proved by the identity
   theorem in the exponent (both sides are power series in `e` agreeing on `ℕ`), because the fork's
   version needs `e ∈ closure(ℕ)` and ours has `‖s‖ = p‖T₀‖ > 1` and `ℓ⟨x⟩ ∈ 𝒪_K`.
4. **No Stirling numbers, no Mahler theory over `K`.**  Mahler coordinates of monomials are
   forward differences (`mahlerCoeffPow`, mathlib's `fwdDiff` lemmas); the seam identity is checked
   at `ℕ`-points only (`fwdDiff_iter_evalAt_natCast`); `colmezEquiv` is built from the isometry +
   surjectivity (closed + dense range), and the inverse is continuous because it is an isometry —
   mathlib's `ContinuousLinearEquiv.ofBijective` needs `NormedSpace`, which `c(ℕ, K)` lacks.
5. **Diagonal intertwining, not conjugation** (`Conjugation.lean`): `d i·v_{ij} = u_{ij}·d j` with
   `d i` units gives `minor v S = minor u S` termwise, so `charCoeff` agrees with **no compactness
   hypothesis** on either side — exactly [LWX]'s "limit of the characteristic polynomial of the
   first `r×r` minors" — and the unbounded `diag(1/n!)` never appears.
6. **`specialize` is a ring hom + continuous** (`Specialize.lean`), so `charCoeff (specOp) =
   spec (charCoeff (D.op ω))` goes through `RingHom.map_det` and `HasSum.map`; the operator-level
   base change of `TateFredholm/BaseChange.lean` (isometric hom + compactoid `u`) is not applicable
   and not needed.
7. **`ψ : ℚ_p →+* K`** is the primary datum (M₁ has `ℚ_p`-entries); the integral side uses
   `intHom ψ = ψ ∘ (ℤ_p ⊂ ℚ_p)`.  `θ_K = mapMatrix ψ ∘ θ`, `levelMonoidOf θ_K (M1K ψ) = levelM1 θ`.
8. **R1 needs no `η`, no neatness, no bijectivity**: `heckeCharPowerSeries` and `specCharSeries`
   are both defined from block operators; compactness of the QMF operator comes from the
   `U_p`-shape hypothesis entrywise (`isCompactoid_kappaSlash` at `σ = ρ`).  `η`, `hv`, neatness
   enter only in the spectral reading Q10.
9. **`UpDatum.ofCerts`** uses `M1.toLocalMat (certM1 i t)` (no `choose`), so `intEvalAtReps_comm`'s
   display hypothesis is `rfl`; the shape clause is derived (`isUpShape_certM1`), not assumed, once
   `hv` and `‖θη₀₀‖ ≤ p⁻¹` are known.  `Halo.lean`'s `UpDatum.ofCosets` (explicit `v_j`, `choose`)
   is left untouched.
10. **Concrete instance at `F = ℚ`** via mathlib's `Padic.adicCompletionEquiv`; its isometry at
    every prime generalises `JacobsSlash.norm_adicCompletionEquiv` and lands in `ForMathlib`.

## File structure (all new; nothing else edited)

```
PhD/TateFredholm/Conjugation.lean      C  diagonal intertwining; blockDiag; diagBlockEquiv
PhD/LWX/Specialize.lean                S  specializeHom, continuity, values on (1+T)^s and [a]
PhD/LWX/Binomial.lean                  B  the p-adic binomial theorem, arbitrary exponent
PhD/LWX/Colmez.lean                    M  mahlerCoeffPow; colmezToMonomial/colmezEquiv; monomialToMahler = Δ ∘ Ψ
PhD/LWX/HaloWeight.lean                W  haloUnits, haloCharFun/haloChar, M1K, haloCol, haloWeight, autFactor
PhD/LWX/Certificates.lean              H  certM1, UpDatum.ofCerts, shapes, intHeckeOperator, Prop 3.1, (2.11.1)
PhD/LWX/Seam.lean                      E  specOp; thetaK; the seam identity; MILESTONE Prop 2.17 (abstract G)
PhD/ForMathlib/NumberTheory/Padics/AdicCompletionEquiv.lean   F  the comparison is an isometry
PhD/LWX/Quaternionic.lean              Q  D/ℚ instance; MILESTONES Prop 2.17 for D/ℚ, spectral reading
```

Imports: `Seam ← {HaloWeight, Colmez, Certificates, Conjugation, QMF.Weight.Fredholm}`;
`HaloWeight ← {Specialize, Binomial}`; `Quaternionic ← {Seam, QMF.Weight.Quaternionic, AdicCompletionEquiv}`.

## Risks (and their mitigations)

* **B (binomial theorem)** — the longest analytic leaf (Fubini + identity theorem); bounded by the
  explicit estimates in `decomposition.md`; if a sub-step needs its own lemma, spawn it (Tier A).
* **W20 (row decay)** and **W13 (multiplicativity)** — routine but fiddly `exp`/`log` disc
  bookkeeping; every hypothesis was checked against `PadicExpLog.lean`'s signatures.
* **M8 (isometry)** — needs "the sup of a `c₀` family is attained at a largest index"; elementary.
* **S5 (multiplicativity of `specialize`)** — `ℤ × ℤ` Cauchy product by cofinite decay; ~100 lines.
* **Typeclass friction**: `Ring.choose` over `K` needs `[CharZero K]` (added to every section
  using it); `BinomialRing K` resolved in the skeleton build.  `Fact p.1.Prime` for `p : Nat.Primes`
  is a local instance.  `CharZero (Kp p)` is proved, not assumed.
* **Concurrency**: the `tate-riesz` beastmode session is live; if `lake build` ever reports errors
  in its files, that is their in-progress state — do not "fix" it, do not delete its sentinel
  (`beastmode-sentinel-ownership` rule: our sentinel is `.mathlib-quality/lwx-seam/beastmode_active`).

## Conventions (binding; inherited from lwx-halo/lwx-slopes)

`lia` → `omega`; each ticket ends with `lake build PhD.<Module>` clean on its file, no `sorry`,
standard axioms only (`propext`/`Classical.choice`/`Quot.sound`), `lake exe runLinter PhD.<Module>`
clean on the file's own declarations at every CLEANUP; renames and statement changes to
`renames.jsonl`, B2 stops to `b2_log.jsonl` (both in this directory); cleanups run **inline by the
main agent** (no subagent dispatch — user instruction, `cleanup-inline-no-subagents`); never edit
`Halo.lean`, `IntegralModel.lean`, `UpMatrix.lean`, `HaloRing.lean`, `PadicExpLog.lean`,
`UnitsLog.lean`, the QMF layer, the NewtonPolygons library or `PhD/PR'd/`; new helpers go in the
nine board files.  Known traps: `generalize` before `omega`; three-product chains need explicit
`mul_le_mul_of_nonneg_*`; `Finset.range_mono`; `WithBotTop.coe_le_coe` antisymmetry; pin implicit
`(p := p)` on `haloExponent`/`haloRho`/`levelM1`/`mahlerOfPow`.

## ChatGPT validation

Skipped: the `chatgpt-math` MCP server failed to connect this session (cached failure).
