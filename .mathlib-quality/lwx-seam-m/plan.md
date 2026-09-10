# Development Plan: the LWX seam at every analyticity level (Prop 2.17 for all `m`)

**BOARD PATH: `.mathlib-quality/lwx-seam-m/`** — named board.  The default `.mathlib-quality/`
root belongs to the (completed) NewtonPolygons project; the sibling boards
`.mathlib-quality/lwx-halo/`, `lwx-slopes/`, `lwx-seam/` (all complete) are upstream and are *not*
edited here.  **`.mathlib-quality/tate-riesz/` is being executed concurrently by another agent**:
never touch its files — `PhD/LWX/HaloRing.lean`, `HaloTate.lean`, `TateRiesz.lean`,
`PadicExpLog.lean`, `PhD/TateFredholm/{Coleman,Entire,Pr,Resultant,RieszColeman,SlopeFactor}.lean`
— nor the core TateFredholm files it is currently editing (`Tate.lean`, `BlockOp.lean`,
`Fredholm.lean`, `OperatorNorm.lean`, `Riesz.lean`), nor its `beastmode_active` sentinel; never run
`/cleanup` on them; never kill a running `lake build`.  Any exp/log or `HaloInt` lemma this board
needs goes into a **new** file.  Every `/beastmode` invocation for this project must name this path.

Planned 2026-09-05 (Fable 5.1).  Sources: [LWX] = Liu–Wan–Xiao, *The eigencurve over the
boundary of weight space*, arXiv:1412.2584v4 (locators `lwx.txt:N` into
`references/lwx.txt`, the `pypdf` extraction, printed page = PDF page); [Colmez] = P. Colmez,
*Fonctions d'une variable p-adique*, Astérisque 330 (2010) 13–59 (locators `colmez.txt:N` into
`references/colmez.txt`, extracted from `references/colmez_asterisque330.pdf` — the theorem [LWX]
cite as "[Colm10, Théorème 1.29]" is **Théorème 1.4.7** (Amice) in the published numbering, proved
via Lemme 1.4.5, Lemme 1.4.9 and Proposition 1.1.5); [Bu04] = Buzzard, *On p-adic families of
automorphic forms* (Lemma 4, radius independence — cited through [LWX, Def 2.13]); [Buzzard] =
*Eigenvarieties*; mathlib.

## Goal

Extend the `lwx-seam` seam theorem from `m = 1` to every analyticity level, so that the
identification `Char(P)(T₀) = det(1 − X·U_p)` and the spectral reading of [LWX, Def 2.13] hold at
**every** point of the boundary annulus `p⁻¹ < ‖T₀‖ < 1` (and no longer only on `1/2 < v(T₀) < 1`).
Write `h := m − 1` (for odd `p`, `q = p`, [LWX]'s discs `a + q⁻¹pᵐℤ_p` are `a + pʰℤ_p`).

1. **Amice's theorem at level `h`** ([Colmez, Thm 1.4.7] = [LWX, §2.16, "Colm10 Théorème 1.29"]):
   the functions `⌊n/pʰ⌋!·(z choose n)` form an orthonormal basis of `OB_{p^{-h}}`, the space of
   functions analytic on every disc `a + pʰℤ_p` with the max-of-Gauss-norms.  Formalised as an
   isometric continuous linear equivalence `colmezDiscEquiv h : c(ℕ, K) ≃L[K] c(ZMod (p^h) × ℕ, K)`
   from Colmez coordinates to the **disc model** (Taylor coefficients on each disc,
   `z = a + pʰw`, `a ∈ ℤ/pʰ`).  (`h = 0` is `colmezEquiv` of `lwx-seam`.)
2. **The `m`-analytic halo weight** ([LWX, §2.1, §2.7]): `κ_{T₀}` as an `AnalyticWeight` on the
   level `M1K_h ψ = ψ(M_h)`, `M_h = {δ ∈ M₁ : p^{h+1} ∣ c}`, defined through the extension formula
   `κ(a·x) = χ(a)·χ(exp(pᵐ))^{log x/pᵐ}` with `χ(exp(pᵐ)) = (1+T₀)^{pʰ}`, valid when
   `T'_h := (1+T₀)^{pʰ} − 1` lies on the joint `exp/log` disc `‖T'_h‖² < p⁻¹`; and the
   **threshold**: every halo point has such an `h` ([LWX, §2.7]: `[−]_{m₀}` is `m₀`-locally
   analytic on `W_{m₀}`; we prove existence rather than their radius).
3. **The disc model of `S^{D,†,m}`** ([LWX, §2.3 (2.3.4), §2.4]): the value module
   `c(ZMod (p^h) × ℕ, K)` with the right action of `M₁`, `(f|δ)_a = κ(c(a+pʰw)+d)·f_{a'}(möb_{δ'}(w))`
   where `δ t_a = t_{a'} δ'` (`t_a(w) = a + pʰw`, `a' = möb_δ(a) mod pʰ`, `δ' ∈ M_h`) — a block
   operator whose blocks are the single-disc `kappaSlash` of the weight at level `M_h`; the forms
   `S^{D,†,h+1}_κ(U)`, `U_p`, its block operator, compactness, `(2.11.1)` at a neat level, the
   Fredholm determinant and the spectral reading — the disc-model mirror of `QMF/Weight/{Compact,Fredholm}`.
4. **[LWX, Prop 2.17] at level `h`** (**milestone `SH-M`**): `specCharSeries (ofCerts …) ω ψ T₀ =
   discHeckeCharPowerSeries h …` for every `h` with `‖T'_h‖² < p⁻¹`; corollaries: [Bu04, Lemma 4]
   (independence of `h`), coverage of the whole annulus, and the `D/ℚ` spectral reading at every
   halo point (**milestone `QH-M`**).

**Out of scope (recorded so nobody re-litigates):** `p = 2`; the sharp analyticity threshold
`v(T₀) > 1/(pʰ(p−1))` of [LWX, §2.1] (we use the joint-disc form `‖T'_h‖² < p⁻¹`, sharp for `p = 3`,
and an existence statement — `PadicExpLog.lean` is frozen and only supports that disc);
`L`-Banach bases over non-discretely-valued `L` via [Colmez, Prop 1.1.5] (we prove the isometry
directly over any complete ultrametric `K` by the unitriangular-mod-`p` argument, which is what
Colmez's proof reduces to); the rigid-analytic packaging; tame Hecke operators; anything on the
`tate-riesz` board; merging `HaloWeight.lean` (the `h = 0` file of `lwx-seam`) into the new
`h`-parametric file (recorded below as a follow-up — the two are related by a consistency lemma,
not by refactoring, to keep the `lwx-seam` milestones untouched).

## Architecture (planning-time findings)

Verified against the code on 2026-09-05 (every name below was read in its file):

| Need | Have | Where |
|---|---|---|
| Colmez basis at `h = 0`, Mahler ↔ monomial, `Δ^m(evalAt F)(0) = ∑ coeff·mahlerCoeffPow` | `colmezToMonomial`, `norm_colmezToMonomial` (unitriangular isometry), `colmezEquiv`, `monomialToMahler_eq`, `fwdDiff_iter_evalAt_natCast`, `map_fwdDiff_iter`, `exists_norm_apply_eq_of_ne_zero`, `exists_lt_norm_forall_norm_apply_le` | `PhD/LWX/Colmez.lean` |
| the halo weight at `h = 0` and its generic helpers | `intHom`, `norm_intHom`, `norm_natCast_p`, `inv_lt_one_p`, `norm_sub_le_max_norm`, `norm_eq_one_of_norm_sub_le`, `norm_mul_inv_sub_one_le`, `norm_le_inv_iff_toZMod_eq_zero`, `sq_norm_lt_norm_p_of_le`, `norm_coeff_mul_le`, `norm_choose_haloExponent_mul_pow_le` (pattern), `map_padicLog`, `haloCharFun_of_norm_sub_le` (pattern), `M1K`, `mapMatrix_toMonoidHom_apply` | `PhD/LWX/HaloWeight.lean` |
| specialization ring hom, `oneAddPow`, `specialize_univChar` | `HaloInt.specializeHom`, `specialize_mul/_const`, `HasSum.specialize`, `continuous_specialize`, `oneAddPow T₀ u = ∑' C(u,r)T₀^r`, `specialize_oneAddTPow`, `specialize_univChar` | `PhD/LWX/Specialize.lean` |
| binomial theorem on the joint disc | `hasSum_choose_mul_pow h3 hp2 hc hx hex`, `norm_choose_mul_pow_le`, `norm_factorial_inv_le`, `one_le_sqrt_inv_norm_p` | `PhD/LWX/Binomial.lean` |
| the seam at `h = 0`, specialised operators, block assembly | `specEntryOp`, `matrixCoeff_specEntryOp`, `specOp`, `charPowerSeries_specOp`, `thetaK`, `levelMonoidOf_thetaK`, `M1K.ofM1`, `intHom_denUnit`, `intHom_mobiusFun`, `fwdDiff_iter_comp_natCast`, `matrixCoeff_diagFactorialBlock(_comp)` | `PhD/LWX/Seam.lean` |
| certificates, Prop 3.1, `(2.11.1)` | `certM1`, `UpDatum.ofCerts`, `isUpShape_certM1`, `intHeckeOperator`, `intEvalAtReps_intHeckeOperator`, `bijective_intEvalAtReps_of_stabilizer_eq_bot`, `norm_theta_apply_zero_zero_eq_one` | `PhD/LWX/Certificates.lean` |
| `D/ℚ` | `padicPlace`, `Kp`, `padicComparison`, `norm_padicComparison`, `thetaInt`, `thetaK_thetaInt`, `IntFormsQ`, `etaAdelic'_mem_levelM1`, `norm_thetaInt_etaAdelic'_zero_zero`, `norm_natCast_p_Kp` | `PhD/LWX/Quaternionic.lean` |
| diagonal intertwining, block-diagonal equivalences | `charPowerSeries_eq_of_diag_intertwine`, `blockDiag`, `diagBlockEquiv` (same index type on both sides — the disc model needs the **index-changing** `blockMap`, new) | `PhD/TateFredholm/Conjugation.lean` |
| block operators, reindexing, compactness | `blockOp`, `blockOp_comp`, `matrixCoeff_blockOp`, `cSpace.blockIncl/blockProj`, `cSpace.comap (φ) (hφ)`, `reindexOp`, `charPowerSeries_reindexOp`, `isCompactoid_blockOp`, `IsCompactoid.finset_sum/smul` | `PhD/TateFredholm/{BlockOp,Riesz}.lean` (read-only while `tate-riesz` runs) |
| Fredholm determinant, conjugation, spectral reading | `charPowerSeries`, `charPowerSeries_conj (φ : c(I,R) ≃L c(J,R))` (**different `J` allowed**), `evalT_charPowerSeries_eq_zero_iff` | `PhD/TateFredholm/{Fredholm,Riesz}.lean` (read-only) |
| the integral model | `M1`, `M1.toLocalMat`, `LocalMat.mobiusFun/denUnit`, `cfunSlash`, `mahlerON/_apply`, `mahlerCoeffs/_apply`, `seqSlashAction`, `seqSlash_coeff` (`(a∣ₛg) m = ∑' n, a n * entry ω δ m n`), `entry`, `univChar`, `levelM1`, `levelM1ToM1`, `IntForms`, `intEvalAtReps` | `PhD/LWX/{IntegralModel,UpMatrix}.lean` (lwx-halo, frozen) |
| weight layer (single disc) | `AnalyticWeight`, `ExpansionData`, `kappaSlash`, `kappaSlash_one/_mul`, `kappaSlash_apply` (`= ∑' i, coeff j (autFactor·mobius^i) · f i`), `matrixCoeff_kappaSlash`, `isCompactoid_kappaSlash (ha : ‖g₀₀‖ ≤ σ)`, `evalAt_mul/_pow/_linX/_mobius`, `absSummable_autFactor/_mobius`, `LevelBounds`, `SigmaNorm` | `PhD/QMF/Weight/{Char,SlashAction,Series}.lean` |
| ring-generic Hecke layer | `slashFixedPointsOfLE`, `heckeOperatorSlash`, `heckeOperatorSlash_apply_rep`, `evalAtRepsSlash`, `bijective_evalAtRepsSlash`, `stabilizerAtSlash`, `slash_apply_mul`, `RightSlashAction.comap` | `PhD/QMF/Slash/{HeckeMonoid,HeckeMatrix,AutomorphicFunction}.lean`, `Weight/SlashAction.lean` |
| Mahler basis, `appr`, `toZModPow` | `mahler`, `continuous_choose`, `PadicInt.appr/appr_spec/appr_lt`, `toZModPow`, `ker_toZModPow`, `denseRange_natCast`, `DenseRange.equalizer` | mathlib `NumberTheory/Padics/{MahlerBasis,RingHoms}.lean` |
| Legendre, Kummer, counting | `padicValNat_factorial (hnb : log p n < b) : v(n!) = ∑_{i ∈ Ico 1 b} n / p^i`, `Nat.emultiplicity_choose_prime_pow (hkn : k ≤ p^n) (hk0 : k ≠ 0)`, `Nat.Ioc_filter_dvd_card_eq_div`, `norm_natCast_eq_pow_padicValNat` (`PadicExpLog.lean:77`) | mathlib, `PadicExpLog.lean` (read-only) |
| binomial rings | `Ring.choose` on any `ℚ≥0`-module ring (`Binomial.lean:277`), `Ring.map_choose`, `Ring.choose_natCast`, `Ring.add_choose_eq` (Vandermonde), `descPochhammer_eq_factorial_smul_choose` | mathlib |
| polynomial reduction | `Polynomial.map (PadicInt.toZMod)`, `Polynomial.coeff_map`, `natDegree_map_le`, `Monic`, `Polynomial.eval_comp`, `Polynomial.coeff_mul` | mathlib |

**Three design decisions.**

*D1 — the disc model.*  `OB_{p^{-h}} ≅ c(ZMod (p^h) × ℕ, K)`, `f ↦ (Taylor coefficients of
f(a.val + pʰw) in w)_a`; norm = max over discs of the Gauss norm — exactly [LWX]'s
`|·|_{qp^{-m},an}` (`lwx.txt:947–953`).  Index type `ZMod (p^h)` (so `h = 0` is `ZMod 1`, one
disc); the disc of `z ∈ ℤ_p` is `toZModPow h z`, and the *natural* lift `a.val < pʰ` is the centre.
The bijection `discIdx h : ZMod (p^h) × ℕ ≃ ℕ`, `(a, k) ↦ k·pʰ + (pʰ − 1 − a.val)`, is the order
in which Colmez's reduced basis-change matrix is **lower unitriangular** ([Colmez, proof of 1.4.7]:
"block upper triangular … each diagonal block lower triangular with invertible diagonal").

**Two corrections found in the decomposition pass** (both now baked into the skeleton; see
`decomposition.md`, groups A and AB):

1. A **reading trap in the extracted reference text**, not an error in the source.  The `pypdf`
   extraction renders `≤` and `≥` as `<` and `>` throughout (`colmez.txt:616` prints
   `1 ≤ i(n) ≤ pʰ` as "1 < i(n) < ph"), so the third bullet of Lemme 1.4.9(ii) prints as
   "deg(ḡ_{n,j}) < m(n)" where the original reads `≤ m(n)`.  The strict reading is false
   (`p = 3`, `h = 1`, `n = 4`, `j = 1`: `ḡ ≡ 2x − 2`, degree `1 = m(4)`); the non-strict reading is
   true and is what Colmez's own proof of Thm 1.4.7 uses.  Also confirmed by exhaustive check:
   `m(n) = ⌊n/pʰ⌋` for every `n` (an earlier draft of this plan wrongly claimed an off-by-one when
   `pʰ ∣ n` and blamed the source; that was an arithmetic slip on our side, now withdrawn).
2. The diagonal position of `g_n` in the order `discIdx` is `revIdx (pʰ) n = ⌊n/pʰ⌋pʰ + (pʰ − 1 −
   n mod pʰ)`, **not** `n`.  The columns are therefore reindexed by the same involution `revIdx`
   inside `colmezMatrix`, and the two reindexings cancel in `matrixCoeff_colmezToDisc`, so
   `colmezToDisc eₙ` is still the disc model of `g_n`.

*D2 — Amice without discrete valuations.*  Colmez proves orthonormality through the residue field
(Prop 1.1.5, `L` discretely valued) and base change (Cor 1.4.6).  We instead extract from Lemme
1.4.9 the shape `M = M₀ + p·M₁` (`M₀` integral, lower unitriangular in the `discIdx` order, `M₁`
integral, each column finitely supported) and prove a **general** criterion
(`PhD/TateFredholm/Unitriangular.lean`): such an `M` defines an isometry of `c(ℕ, K)` with dense
range, hence a `≃L[K]`, over every complete ultrametric `K` — the `lwx-seam` argument
`norm_colmezToMonomial` (largest index where the norm is attained) plus a `p`-adic successive
approximation for surjectivity.  This is the content of [Colmez, Prop 1.1.5 ⇐] with the residue
field replaced by "mod `p`" estimates; no extra hypothesis on `K`.

*D3 — the action through conjugation, not a new weight theory.*  `δ t_a = t_{a'} δ'` with
`δ' = discConj h δ a ∈ M_h` (`c`-entry `c·pʰ`), so the disc slash is the block operator with the
single-disc `kappaSlash (ψ δ')` at block `(a, a')` — the existing weight machinery at the finer
level `M1K_h ψ` does all the analysis; the cocycle is the matrix identity
`discConj (δ₁δ₂) a = discConj δ₁ (discImage δ₂ a) · discConj δ₂ a`.  The level-`h` halo weight is
the `lwx-seam` construction with `T₀` replaced by `T'_h` in the exponent and residue discs of
radius `p^{−(h+1)}`; the only new analytic input is the **binomial power identity**
`(1+T₀)^{pʰu} = ((1+T₀)^{pʰ})^u` for `u ∈ ψ(ℤ_p)` (both sides continuous in `u`, equal on `ℕ`),
which is [LWX, §2.1]'s extension formula read at `χ(exp(pᵐ)) = (1+T)^{pʰ}`.

## Mathlib inventory (verified 2026-09-05)

| Concept | Status | Action |
|---|---|---|
| Mahler's theorem `C(ℤ_p, E) ≅ c₀` | `PadicInt.mahlerEquiv`, `hasSum_mahler`, `fwdDiff_mahlerSeries` | USE (through `IntegralModel.lean`'s `mahlerON`/`mahlerCoeffs`) |
| Amice's theorem (locally analytic ⇔ scaled Mahler decay / the ON basis `⌊n/pʰ⌋!(x choose n)`) | **not in mathlib** | DEFINE + PROVE at the disc-model level (tranches U, A, AB) |
| `p`-adic valuation of `(pʰ w choose k)`-type products | `padicValNat_factorial`, `emultiplicity_choose_prime_pow`, `Ioc_filter_dvd_card_eq_div` | USE; the count `#{k < n : k ≡ r [pˡ]}` is derived (A-tranche) |
| `x ↦ x^{pʰ}` contracts `1 + 𝔪` | not as a lemma | PROVE (`X`-tranche) from Kummer |
| block operators with index change | `blockOp` (same index), `reindexOp` | DEFINE `blockMap` (BM-tranche) |
| radius independence of `Char(U_p)` ([Bu04, Lemma 4]) | not in repo | COROLLARY of the milestone (both levels equal `Char(P)(T₀)`) |

## File structure (all new; no existing file is edited)

| File | Tranche | Content |
|---|---|---|
| `PhD/TateFredholm/Unitriangular.lean` | U | `IsIntegralUnitriangular`-style criterion: `M = M₀ + q·M₁`, isometry, surjectivity, `≃L` |
| `PhD/TateFredholm/BlockMap.lean` | BM | `blockMap f : c(σ×I,R) →L c(σ×I',R)`, matrix, compositions with `blockOp`/`blockDiag`, `blockMapEquiv` |
| `PhD/LWX/AmiceValuation.lean` | A | `discPoly h n a = ⌊n/pʰ⌋!·((a.val + pʰX) choose n) ∈ ℚ_p[X]` (as `ℚ_[p]`-polynomial via `descPochhammer`), the factorisation `= C c · f`, [Colmez, Lemme 1.4.9] (i) integrality, (ii) the mod-`p` shape in the `discIdx` order |
| `PhD/LWX/AmiceBasis.lean` | AB | `discIdx`, `discCoeff`, `colmezToDisc`, isometry, surjectivity, `colmezDiscEquiv`, `discFactorial`, `discToMahler`, evaluation at integer points, `discToMahler_apply_eq_fwdDiff` |
| `PhD/LWX/PowSubOne.lean` | X | `oneAddPow_pow_natCast_mul` (binomial power identity), `tendsto_pow_prime_pow_sub_one`, `exists_sq_norm_pow_sub_one_lt` (the threshold) |
| `PhD/LWX/HaloWeightH.lean` | WH | `Mh p h`, `M1Kh`, `haloUnitsH`, `repLift`, `haloExponentH`, `haloCharFunH`, `haloCharH`, `haloRhoH`, `haloColH`, `haloExpansionH`, **`haloWeightH`**, `evalAt_autFactor_haloWeightH`, `haloCharFunH_psi` |
| `PhD/LWX/DiscModel.lean` | D | `discImage`, `discConj`, cocycle, `discSlash`, `discSlashAction`, compactness, `discEval`, `discEval_discSlash` |
| `PhD/LWX/DiscForms.lean` | DF | `DiscForms`, `discEvalAtReps`, `discHeckeOperator`, `discHeckeBlockOp`, transport, compactness, bijectivity, `discHeckeCharPowerSeries`, spectral reading |
| `PhD/LWX/SeamH.lean` | SH | `entry` as a forward difference of `[cz+d]·(möb z choose n)`, its specialisation, the seam identity at level `h` (single matrix, blockwise), diagonal intertwining, **milestone `SH-M`**, coverage, [Bu04, Lemma 4] |
| `PhD/LWX/QuaternionicH.lean` | QH | `D/ℚ` at level `h`: Prop 2.17 and the spectral reading at every halo point (**milestone `QH-M`**) |

## Dependency graph (tranche level)

```
U ──┐
A ──┼─→ AB ──┐
X ──┘        ├─→ D ──→ DF ──┐
X ──→ WH ────┘              ├─→ SH ──→ QH
BM ─────────────────────────┘
(lwx-seam: Colmez, HaloWeight, Specialize, Binomial, Seam, Certificates, Quaternionic — imported)
```

Concretely (`import` lines, as compiled): `AmiceBasis` imports `AmiceValuation`, `PowSubOne`,
`Unitriangular`; `HaloWeightH` imports `PowSubOne`; `DiscModel` imports `AmiceBasis`,
`HaloWeightH`; `DiscForms` imports `DiscModel`, `Certificates`, `QMF.Weight.Fredholm`; `SeamH`
imports `DiscForms`, `Seam`, `BlockMap`; `QuaternionicH` imports `SeamH`, `Quaternionic`.
(`PowSubOne` also carries the `NeZero (p ^ h)` instance used by every `ZMod (p ^ h)` below it.)

## Generality decisions

- `K` any complete ultrametric `NontriviallyNormedField` with `CharZero` (as in `lwx-seam`); the
  Amice criterion (U) is stated over any such `K` with an abstract `q < 1` in place of `‖p‖`.
- The disc layer is stated for the **integral level** `M1 p` (ℚ_p-matrices, acting through `ψ`),
  not for an abstract `K`-level: the disc bookkeeping needs `p`-adic integral entries (the
  discs are `ψ(ℤ_p)`-discs).  The weight is abstract: any `κ : AnalyticWeight UK (M1Kh h ψ) ρ`.
- `h : ℕ` arbitrary; `h = 0` reproduces the `lwx-seam` layer (consistency lemma
  `discSlash_zero`, optional ticket).
- `p ≠ 2` throughout (inherited from `PadicExpLog.lean`).

## Deferred (no ticket here)

- Merging `HaloWeight.lean` into `HaloWeightH.lean` (the `h = 0` case uses Teichmüller
  representatives, the `h`-version natural-number lifts; both define `κ_{T₀}`).
- The sharp threshold `v(T₀) > 1/(pʰ(p−1))`; quantitative `h(T₀)`.
- `Cor 1.4.8` (Mahler-decay characterisation of local analyticity) as a stand-alone statement.

## ChatGPT validation

Skipped: the `chatgpt-math` MCP server failed to connect this session (cached failure).
