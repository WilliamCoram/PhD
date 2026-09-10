# Decomposition — `lwx-theta-h2` (Phase 1e artifact, 2026-09-10)

> **Execution outcome (2026-09-10).**  Every leaf below was proved as decomposed; no leaf turned
> out false, no statement was edited, and no B2 was filed.  Two leaves needed a different *tactic
> route* than sketched (A18/A19's `tsum_eq_single` and B23's backwards rewrite — see
> `tickets.md`'s Summary), and Part B needed six private norm helpers that B4's sketch had folded
> into its own proof.  The decomposition itself stands.

**BOARD PATH: `.mathlib-quality/lwx-theta-h2/`.**  Read `plan.md` first, then
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`.

## Skeleton location and status

- `PhD/LWX/ThetaExact.lean` — 25 `sorry` (Part A).  `lake build PhD.LWX.ThetaExact`: sorry
  warnings only.
- `PhD/LWX/TargetPoint.lean` — 23 `sorry` (Part B).  Same.
- `PhD/LWX/DegreeFormula.lean` — 2 `sorry` (assembly).  Same.
- `lake build PhD`: **green**, 3906 jobs (2026-09-10).  Every statement below is transcribed from
  the compiling skeleton and is protected.

## Jacquet–Langlands audit for this board

None of the leaves below imports a result whose source proof uses Jacquet–Langlands.  Part A
replaces [LWX]'s citation of [Jo11] (not a Jacquet–Langlands result either) by a disc-model
argument; Part B is character arithmetic.  See `plan.md` §"Jacquet–Langlands dependencies" and
the 2026-09-10 addendum to `JL-AUDIT.md`.

---

## Part A — Hypothesis H2 from the classical shapes

### Source proof read

[LWX, §3.23 Step III], `lwx.txt:2049–2068` (verbatim, line breaks removed):

> "To compute `n⁺_{k+1} − n_{k+1}`, we recall the following exact sequence (cf. [Jo11])
> `0 → S^D_{k+2}(K^p Iw_{q²}, ψ) → S^{D,†}_{(k,ψ)} —(d/dz)^{k+1}→ S^{D,†}_{(−k−2,ψ)} → 0`.
> This exact sequence is equivariant for the `U_p`-action on the first two spaces, and the
> `p^{k+1}U_p`-action on the third space.  It is clear that `n⁺_{k+1} − n_{k+1}` is equal to the
> codimension of `S^D_{k+2}(K^pIw_{q²}, ψ)` in the slope `≤ k+1` subspace in `S^{D,†}_{(k,ψ)}`.
> The latter in turn is equal to the dimension of slope zero subspace of `S^{D,†}_{(−k−2,ψ)}` by
> the exact sequence."

[Bu04, §7], `bu04.txt:1093–1096`: "it is elementary to check that if `f ∈ S^D_κ(U, 1)` and
`η ∈ D_f^×` with `η_p ∈ M_α`, then `(θ^{1−k}f)|η = |ν(η)|^{k−1}θ^{1−k}(f|η)` and hence that
`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`."  [Bu04, Prop 4 proof], `bu04.txt:1111–1114`: "The
kernel of `θ^{1−k}` is the functions `f ∈ S^D_κ(U; 1)` whose image is contained within the space
of polynomials of degree at most `k − 2`, which is precisely the space of classical forms".

### Plain-English proof (what `StepThree.lean` consumes, and what we prove)

`IsThetaExact` asks for `det(1 − X·U_p∘(1 − π)) = det(1 − p^{k+1}X·U_p')`, where `π` projects onto
the classical coordinates (Taylor degrees `≤ k` in every disc).  On the disc model
`θ^{k+1}c (i,a,j) = (j+1)⋯(j+k+1)·c (i,a,j+k+1)`, i.e. `θ^{k+1} = D∘σ`: `σ` the shift by `k+1`, `D`
the diagonal of falling factorials.  The shift has the section `τ : e_j ↦ e_{j+k+1}` with
`σ∘τ = 1` and `τ∘σ = 1 − π` (Buzzard's kernel characterisation, in coordinates).  The
intertwining `θ∘U = p^{k+1}U'∘θ` (Buzzard's Hecke relation, proved on the board `lwx-theta` from
the classical shapes) composed with `τ` gives `D∘(σUτ) = (p^{k+1}U')∘D`: the two operators
`A := σUτ` and `B := p^{k+1}U'` satisfy `d_x·A_{xy} = B_{xy}·d_y` with `d_x = (j+1)⋯(j+k+1)`
nonzero (characteristic zero), hence every principal minor of `A` equals that of `B`
(`A_S = D_S⁻¹B_S D_S`), hence `det(1 − X·A) = det(1 − X·B)`.  Finally
`det(1 − X·U(1−π)) = det(1 − X·(Uτ)σ) = det(1 − X·σ(Uτ)) = det(1 − X·A)` by the trace property
(`charPowerSeries_comm`, `Uτ` compactoid), and `det(1 − X·(p^{k+1}U')) = det(1 − p^{k+1}X·U')`.

This is the determinant shadow of [LWX]'s sentence "the dimension of slope zero subspace of
`S^{D,†}_{(−k−2,ψ)}`": slopes are read off `det(1 − X·U)`, so the identity of determinants is
what Step III's counting actually uses (it is literally the hypothesis `hH2` of `degX_succ`).
No exactness of spaces is claimed or needed: `D` is not invertible as a bounded operator.

### Leaves

Notation: `I := ι × (ZMod (p^h) × ℕ)`; `x.2.2` is the Taylor degree of `x : I`.

- **A1** `TateFredholm.matrixCoeff_truncation` — `ThetaExact.lean:49`
  `matrixCoeff (truncation S) j i = if j = i ∧ j ∈ S then 1 else 0`.
  Source: definition (`truncation_apply`, `Matrix.lean:260`; `matrixCoeff` = `u (single i 1) j`).
  Discharged by: `truncation_apply`, `cSpace.single_apply_self`, `cSpace.single_apply_of_ne`.
  Attacks: [1] off-diagonal `j ≠ i`: `single i 1 j = 0` so both sides `0` ✓; [2] `j = i ∉ S`:
  LHS `0` by `if_neg`, RHS `0` ✓; [3] `j = i ∈ S`: `1 = 1` ✓; [4] hypothesis test: no `IsTate`,
  no compactness — `omit` at cleanup.  SURVIVED.

- **A2** `TateFredholm.charPowerSeries_smul` — `ThetaExact.lean:56`
  `charPowerSeries (a • u) = PowerSeries.rescale a (charPowerSeries u)` (`hu : IsCompactoid u`).
  Source: `charCoeff_smul` (`Riesz.lean:1514`): `charCoeff (a • u) n = a^n * charCoeff u n`;
  `PowerSeries.coeff_rescale : coeff n (rescale a f) = a^n * coeff n f`.
  Attacks: [1] `a = 0`: `charPowerSeries 0 = 1`, `rescale 0 f = C (coeff 0 f) = 1` ✓ (`charCoeff_zero`);
  [2] is `IsCompactoid u` needed? `charCoeff_smul` uses `summable_minor u hu n` — yes, keep;
  [3] type of `rescale`: `rescale a : R⟦X⟧ →+* R⟦X⟧`, applied ✓ (skeleton compiles).  SURVIVED.

- **A3–A5** `LWX.shiftOne`, `LWX.insertOne`, `LWX.diagOne` — `ThetaExact.lean:73–95`
  `ofCoeffs` with matrices `if i = j + r then 1 else 0`, `if j = i + r then 1 else 0`,
  `if i = j then descFactorial (j+r) r else 0`; obligations `‖·‖ ≤ 1` and column-finiteness.
  Source: `thetaOne` (`Theta.lean:72`) is the product of the last two, `matrixCoeff_thetaOne`.
  Attacks: [1] column of `shiftOne`: rows `j` with `i = j + r`: at most `{i − r}` ✓; of
  `insertOne`: `{i + r}` ✓; of `diagOne`: `{i}` ✓ — all finite; [2] norms: `1`, `0`, and
  `‖(n : K)‖ ≤ 1` (`IsUltrametricDist.norm_natCast_le_one`) ✓; [3] does `insertOne` need `r ≤ i`
  anywhere? No — `e_i ↦ e_{i+r}` is total ✓.  SURVIVED (the bound obligations of A3/A4 are
  already discharged in the skeleton).

- **A6–A8** `matrixCoeff_shiftOne/insertOne/diagOne` — `ThetaExact.lean:97–107`: `matrixCoeff_ofCoeffs`.
  Attacks: definitional; the only risk is index order (`matrixCoeff u j i = (u e_i)_j`, row `j`
  first, matching `ofCoeffs`' `M j i`) — checked against `matrixCoeff_thetaOne` ✓.  SURVIVED.

- **A9** `thetaOne_eq_diagOne_comp_shiftOne` — `ThetaExact.lean:110`: `thetaOne K r = (diagOne K r).comp (shiftOne K r)`.
  Source: `thetaOne`'s matrix is `if i = j + r then descFactorial (j+r) r else 0`; the product
  `(D σ)_{ji} = ∑_l σ_{li} D_{jl} = D_{jj} σ_{ji}`.
  Discharged by: `ext_matrixCoeff`, `matrixCoeff_comp`, `tsum_eq_single j`, A6, A8, `matrixCoeff_thetaOne`.
  Attacks: [1] `r = 0`: `D = 1`, `σ = 1`, `θ^0 = 1` ✓; [2] order of composition: `θ = D∘σ`
  (shift first, then scale by the *target* index `j`): `(θ c) j = descFactorial (j+r) r · c(j+r)`
  and `(D(σ c)) j = descFactorial (j+r) r · (σc) j = … · c (j+r)` ✓ (the other order `σ∘D` would
  give `descFactorial (j+2r) r`, wrong); [3] `matrixCoeff_comp`'s `tsum` over `l` collapses at
  `l = j` because `D_{jl} = 0` for `l ≠ j` ✓.  SURVIVED.

- **A10** `shiftOne_comp_insertOne : (shiftOne K r).comp (insertOne K r) = 1` — `ThetaExact.lean:114`.
  `(στ)_{ji} = ∑_l τ_{li} σ_{jl} = [i + r = j + r] = [j = i]` ✓.  Attacks: [1] `r = 0` ✓;
  [2] `matrixCoeff_one j i = if j = i then 1 else 0` (`Riesz.lean:729`) — orientation `j = i` ✓;
  [3] `tsum` collapses at `l = i + r` ✓.  SURVIVED.

- **A11** `insertOne_comp_shiftOne : (insertOne K r).comp (shiftOne K r) = 1 - truncation (Finset.range r)` — `ThetaExact.lean:120`.
  `(τσ)_{ji} = ∑_l σ_{li} τ_{jl} = ∑_l [i = l + r][j = l + r]`: for `r ≤ i` it is `[j = i]`, for
  `i < r` it is `0`; `(1 − π_{<r})_{ji} = [j = i] − [j = i ∧ j < r]` ✓ both cases.
  Attacks: [1] `r = 0`: `range 0 = ∅`, `1 − 0 = 1` ✓; [2] `i < r`, `j = i`: LHS `0`, RHS
  `1 − 1 = 0` ✓; [3] sign/orientation of `truncation`'s matrix from A1 (`j = i ∧ j ∈ S`) ✓.
  SURVIVED.

- **A12–A14** `matrixCoeff_shiftBlock/insertBlock/diagBlock` — `ThetaExact.lean:143–156`:
  `matrixCoeff_blockMap` twice (`BlockMap.lean:82`) then A6–A8; the block conditions
  `i = i' ∧ a = a'` are folded into one `Prod` equality.
  Attacks: [1] `matrixCoeff_blockMap f a b j i` has the block index *first* in each pair, and
  our index is `(i, (a, j))` — nested pairs match `blockMap (σ := ι) (blockMap (σ := ZMod _) f)` ✓;
  [2] the `Prod` equality direction (`y = (x.1, …)` for the shift, `x = (y.1, …)` for the
  section) — transcribed from A6/A7's `i = j + r` / `j = i + r` with `x` the row ✓; [3] `DecidableEq`
  on `ι × (ZMod (p^h) × ℕ)` for the `if` — available ✓ (skeleton compiles).  SURVIVED.

- **A15** `thetaBlock_eq_diagBlock_comp_shiftBlock` — `ThetaExact.lean:159`: `blockMap_comp` twice + A9.
  Attacks: [1] `blockMap_comp : (blockMap g).comp (blockMap f) = blockMap (g.comp f)` — rewrite
  direction left-to-right on the RHS of our goal ✓; [2] `thetaBlock = blockMap (thetaDisc)`,
  `thetaDisc = blockMap (thetaOne)` — both `def`s, unfold by `rw` ✓; [3] nothing else.  SURVIVED.

- **A16** `shiftBlock_comp_insertBlock … = 1` — `ThetaExact.lean:165`: `blockMap_comp` twice, A10,
  `ContinuousLinearMap.one_def`, `blockMap_id` twice.  Attacks: [1] `1` vs `id`: `one_def : 1 = id` ✓;
  [2] `blockMap_id` is stated with `ContinuousLinearMap.id R c(I, R)` ✓.  SURVIVED.

- **A17** `insertBlock_comp_shiftBlock (h k) : … (k+1) … = 1 - truncation (classicalSupport p ι h k)` — `ThetaExact.lean:171`.
  Direct `ext_matrixCoeff` with A12, A13, `matrixCoeff_sub`, `matrixCoeff_one`, A1,
  `mem_classicalSupport_iff` (`x ∈ classicalSupport ↔ x.2.2 ≤ k`), split on `k + 1 ≤ y.2.2`.
  Attacks: [1] the degree bound: `range (k+1) = {j < k+1} = {j ≤ k}` = `classicalSupport`'s
  condition ✓; [2] could a mismatch of the block indices give a nonzero off-block term?  Both
  factors force `z.1 = y.1 = x.1`, `z.2.1 = y.2.1 = x.2.1` ✓; [3] `tsum_eq_single` needs the
  single index `(y.1, (y.2.1, y.2.2 − (k+1)))` and `y.2.2 − (k+1) + (k+1) = y.2.2` under
  `k+1 ≤ y.2.2` (`omega`) ✓.  SURVIVED.

- **A18, A19** `matrixCoeff_diagBlock_comp`, `matrixCoeff_comp_diagBlock` — `ThetaExact.lean:184–199`:
  `matrixCoeff_comp` + `tsum_eq_single` at `x` (resp. `y`) + A14.
  Attacks: [1] `matrixCoeff_comp u v l i = ∑' j, matrixCoeff v j i * matrixCoeff u l j`
  (`Matrix.lean:84`): for `D.comp T` the inner operator is `T`, outer `D`, so the sum is over
  `z` of `T_{zy}·D_{xz}`, single at `z = x` ✓; for `T.comp D`: `D_{zy}·T_{xz}`, single at `z = y` ✓;
  [2] `mul_comm` needed to match the stated order ✓; [3] none.  SURVIVED.

- **A20** `diagBlock_comp_eq_of_intertwine` — `ThetaExact.lean:207`.
  From `hint : θ∘U = c • (U'∘θ)`: compose on the right with `τ`; `θ = D∘σ` (A15);
  `((D∘σ)∘U)∘τ = D∘(σ∘(U∘τ))` (`comp_assoc`); `(c • (U'∘θ))∘τ = c • (U'∘(θ∘τ))`
  (`smul_comp`, `comp_assoc`); `θ∘τ = D∘(σ∘τ) = D` (A16, `one_def`, `comp_id`);
  `c • (U'∘D) = (c • U')∘D` (`smul_comp`).
  Attacks: [1] is `smul_comp` the right lemma: `(c • f).comp g = c • f.comp g` ✓ (mathlib
  `ContinuousLinearMap.smul_comp`); [2] associativity direction ✓; [3] does the argument use
  `σ∘τ = 1` only — yes; `τ∘σ = 1 − π` is *not* used here ✓.  SURVIVED.

- **A21** `charPowerSeries_shiftBlock_comp_eq_of_intertwine` — `ThetaExact.lean:219`:
  `charPowerSeries (σ∘(U∘τ)) = charPowerSeries (c • U')`.
  Discharged by: `charPowerSeries_eq_of_diag_intertwine d hd hcoef` (`Conjugation.lean:85`) with
  `d x := descFactorial (x.2.2 + (k+1)) (k+1)`, `hd` from `Nat.descFactorial_pos`,
  `Nat.cast_ne_zero`, `isUnit_iff_ne_zero` (`CharZero K`), `hcoef x y` from A20 at `(x, y)`
  through A18 (left) and A19 (right).
  Attacks: [1] the hypothesis shape of `charPowerSeries_eq_of_diag_intertwine` is
  `∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j` and concludes
  `charPowerSeries v = charPowerSeries u`: with `v := σUτ`, `u := c • U'` this is exactly A20's
  coefficient form ✓ (verified by `#check`); [2] units: `descFactorial (n + r) r > 0` since
  `r ≤ n + r` (`Nat.le_add_left`) ✓, and a positive natural is nonzero in `K` by `CharZero` ✓;
  [3] no compactness needed here (the lemma's docstring says so) ✓.  SURVIVED.

- **A22** `charPowerSeries_comp_one_sub_truncation_eq` — `ThetaExact.lean:229`:
  `charPowerSeries (U∘(1 − π)) = charPowerSeries (σ∘(U∘τ))`.
  `1 − π = τ∘σ` (A17), `U∘(τ∘σ) = (U∘τ)∘σ`, `charPowerSeries_comm (U∘τ) σ (hU.comp_right τ)`,
  `comp_assoc`.
  Attacks: [1] `charPowerSeries_comm (u) (v) (hu : IsCompactoid u) : charPowerSeries (u.comp v)
  = charPowerSeries (v.comp u)` — with `u = U∘τ` (compactoid by `IsCompactoid.comp_right`,
  `Matrix.lean:550`) ✓; [2] `[IsTate K]` needed by `charPowerSeries_comm` — `K` a
  `NontriviallyNormedField` has it (`Tate.lean:265`) ✓; [3] we do **not** need `σ` compactoid
  (it is not) ✓.  SURVIVED.

- **A23** `charPowerSeries_comp_one_sub_truncation_eq_rescale` — `ThetaExact.lean:240`: A22, A21, A2.
  Attacks: [1] `hU'` is needed only by A2 ✓; [2] the rescale constant is `c` on the nose ✓;
  [3] composition: `charPowerSeries (U(1−π)) = cPS(σUτ) = cPS(c•U') = rescale c (cPS U')` ✓.
  SURVIVED.

- **A24** `isThetaExact_of_isClassicalShape` — `ThetaExact.lean:265`.
  `unfold IsThetaExact`; `exact charPowerSeries_comp_one_sub_truncation_eq_rescale h k hU hU'
  (ψ p ^ (k+1)) hint` with `hU := isCompactoid_discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu hρ
  hσ hshape`, `hU'` likewise at `κ'`, `hint := thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape
  θG h ψ U hU vRep hvΔ idx uu κ κ' hcl hcl' hdet`.
  Source: [LWX] `lwx.txt:2049–2056` (the equivariant sequence), [Bu04] `bu04.txt:1093–1096`.
  Attacks: [1] `IsThetaExact`'s RHS is `rescale (ψ p ^ (k+1)) (discHeckeCharPowerSeries …)` and
  `discHeckeCharPowerSeries` is a `def` equal to `charPowerSeries (discHeckeBlockOp …)` — `exact`
  sees through it (defeq), `rw` would not (recorded trap) ✓; [2] the constant in
  `thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape` is `ψ p ^ (k + 1)` with `p : ℚ_[p]`
  cast — same spelling as `IsThetaExact` ✓ (both in `StepThree.lean`); [3] hypothesis audit:
  `hρ hσ hρ' hσ'` are what `isCompactoid_discHeckeBlockOp` takes; `hshape` is needed for
  compactness; `hdet` for the intertwining.  Nothing hidden ✓.  SURVIVED.

- **A25** `isThetaExact_classicalData` — `ThetaExact.lean:281`: A24 at `κ = c.weight`,
  `κ' = d.weight`, `hcl = c.shape`, `hcl' = d.shape`, radii `haloRhoH_nonneg 1 T`,
  `max_lt (haloRhoH_lt_one 1 T hT) inv_lt_one_p`.
  Attacks: [1] `c.weight` unfolds (`ClassicalData.weight` is a `def`) to
  `haloWeightH 1 ψ T₀ ω hp2 hψ c.h0 c.h1 c.hT`, the weight in `c.shape` ✓; [2] `d.shape` has the
  *same* constants `c.u` by the definition of `TargetData` ✓; [3] `hσ` needs
  `haloRhoH p 1 T < 1` — `haloRhoH_lt_one 1 T c.hT` ✓ and `p⁻¹ < 1` ✓.  SURVIVED.

### Composition attack (Part A)

Could all leaves hold and `IsThetaExact` still fail?  The chain is a sequence of equalities of
power series, each a leaf; the only place a hidden hypothesis could enter is compactness (A22 and
A2), both supplied at the Hecke operators by `isCompactoid_discHeckeBlockOp`.  Edge case `k`
arbitrary, `h` arbitrary: nothing is specialised to `h = 1` before A25.  Edge case `ι` empty:
all operators are `0`, both determinants `1` ✓.

---

## Part B — the theta target at the classical points

### Source proof read

[LWX, Notation 2.1], `lwx.txt:413–418`: "We write `ℤ_p^×` as `Δ × (1+qℤ_p)^×` with
`Δ ≅ (ℤ/qℤ)^×`.  We identify `(1+qℤ_p)^×` with `ℤ_p` via `(1/q) log(−)`. … `T` corresponds to
`[exp(q)] − 1`.  Here, for `a ∈ ℤ_p^×`, we use `[a]` to denote its image in `Λ^×`; so
`[−] : ℤ_p^× → Λ^×` is the universal character".  `lwx.txt:431–433`: "For each (`ℂ_p`-valued)
continuous character `χ` of `ℤ_p^×`, we write `T_χ := χ(exp(q)) − 1` for the `T`-coordinate of
the associated point on weight space."

[LWX, §2.1], `lwx.txt:456–463`: "χ extends to a continuous homomorphism
`κ : (ℤ_p + p^m A°⟨z⟩)^× = ℤ_p^× · (1 + p^m A°⟨z⟩) → (A°⟨z⟩)^×`,
`a·x ↦ χ(a)·χ(exp(p^m))^{(log x)/p^m}`."  `lwx.txt:467–470`: "We say a continuous character `χ`
of `ℤ_p^×` is classical if it sends `x` to `x^k ψ(x)` for an integer `k ≥ 0` and a finite
character `ψ` of conductor `p^m`.  We write `(k, ψ)` for such a character".

[LWX, §3.23], `lwx.txt:1794–1798`: "We consider the classical weights `χ_k = (k, ψ)` of conductor
`q²` with `k ∈ ℤ_{≥0}`, such that `χ_k|_Δ = ω`.  The corresponding `T`-coordinates `T_{χ_k}` have
valuation `q/ϕ(q²) = p/(q(p−1)) < 1`."  [LWX, §3.23 Step III], `lwx.txt:2070–2076`: "Using
Corollary 3.21, we thus obtain `n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ · ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})`."

### Plain-English proof

The target weight `(−k−2, ψ)` sends `x ↦ x^{−k−2}ψ(x)`.  Its `T`-coordinate is
`T₁ = χ(exp p) − 1 = ζ·exp(−p(k+2)) − 1` with `ζ = ψ(exp p)`; the classical point of `(k, ψ)` is
`T₀ = ζ·exp(pk) − 1`.  Both have `‖T‖ = ‖ζ − 1‖` (the exponential factor is a `1`-unit closer to
`1` than `ζ`), so `p⁻¹ < ‖T‖ < 1`, and `(1+T)^p − 1 = exp(p²s) − 1` (as `ζ^p = 1`), so the
level-`1` halo exponent is `s_1 = log(exp(p²s))/p² = s`.  At `s = −(k+2)` the binomial series in
the automorphy factor is `∑ C(−(k+2), m)(c/d)^m z^m = (1 + (c/d)z)^{−(k+2)}` — the inverse of a
polynomial — so `autFactor · (cz+d)^{k+2} = κ(d)·d^{k+2}`: the target shape with constants
`κ(d)d^{k+2}`.  The classical datum's constants are `κ₀(d)·d^{−k}` with `κ₀` the halo character
at `T₀`.  Write `d = ψ(a)`, `a = ω₀(ā)·⟨a⟩`, `⟨a⟩ = exp(p·ℓ⟨a⟩)`.  The halo characters are
`κ(ψa) = ψ(ω₁(ā))·(1+T₁)^{ψℓ}` and `κ₀(ψa) = ψ(ω(ā))·(1+T₀)^{ψℓ}` (the extension formula, in
the form `specialize_univChar`).  Since `(1+T₀)^{y}·exp(−p(2k+2)y) = (1+T₁)^{y}` for `y ∈ ℤ_p`
(true at `y = n ∈ ℕ` as an identity of powers, and both sides are continuous), the constants
agree exactly when `ω₁(ā)·ω₀(ā)^{k+2} = ω(ā)·ω₀(ā)^{−k}`, i.e. `ω₁ = ω·ω₀^{−2k−2}`.  That is
[LWX]'s `ωω₀^{−2k−2}`, and it is `targetChar ω k`.

### Leaves

- **B1** `teichChar_unitsMap_toZMod` — `TargetPoint.lean:64`: `teichChar p (Units.map toZMod a)
  = teichmuller a`.  Discharged by `teichRes_toZMod` (`HaloWeight.lean:154`).  Attacks:
  [1] `teichChar_apply` is `rfl` ✓; [2] the `Units.map (PadicInt.toZMod).toMonoidHom` spelling
  matches `teichRes_toZMod`'s ✓ (skeleton compiles against it); [3] none.  SURVIVED.

- **B2** `targetChar_apply` — `TargetPoint.lean:76`: `targetChar p ω k r = ω r * (teichRes r ^ (2k+2))⁻¹`.
  `MonoidHom.mul_apply`, `MonoidHom.inv_apply`, `MonoidHom.pow_apply`, `teichChar_apply`.
  Attacks: [1] the group structure on `(ZMod p)ˣ →* ℤ_[p]ˣ` is the pointwise `CommGroup`
  (`MonoidHom.commGroup`), so `(f⁻¹) r = (f r)⁻¹` and `(f^n) r = (f r)^n` ✓; [2] is
  `ω·ω₀^{−2k−2}` the right exponent?  Re-derived in the plain-English proof above: yes ✓;
  [3] `2 * k + 2` vs `2 * (k + 1)`: kept as `2 * k + 2`, `ring_nf` if needed ✓.  SURVIVED.

- **B3** `weightPoint_natCast` — `TargetPoint.lean:90`: `weightPoint p (k : ℤ) ζ = classicalPoint p k ζ`.
  `Int.cast_natCast` ✓.  Attacks: [1] both are `ζ * padicExp (p * s) − 1` with `s = ((k:ℤ):K)`
  vs `(k:K)` — `Int.cast_natCast : ((n : ℤ) : R) = n` ✓; [2] none; [3] none.  SURVIVED.

- **B4–B7** `norm_weightPoint`, `norm_weightPoint_pow`, `inv_lt_norm_weightPoint`,
  `norm_weightPoint_lt_one` — `TargetPoint.lean:94–115`.
  Source: [LWX] `lwx.txt:1796–1798` (valuation `p/(q(p−1)) = 1/(p−1)` at `q = p`).  Mirrors of
  `norm_classicalPoint` and its three corollaries (`ClassicalPoint.lean:231–265`) with
  `IsUltrametricDist.norm_intCast_le_one` in place of `norm_natCast_le_one`; the private helpers
  `norm_p_mul_natCast_sq_lt`, `norm_padicExp_p_mul_sub_one_le` are re-stated for `‖x‖ ≤ 1`
  (one helper `norm_p_mul_sq_lt (hpK) (hx : ‖x‖ ≤ 1) : ‖p * x‖^2 < ‖p‖`).
  Attacks: [1] negative `s`: `‖(s : K)‖ ≤ 1` for every integer ✓ (ultrametric); [2] `p = 2` is
  excluded (`hp2`) exactly as for `classicalPoint`, since `p⁻¹ < ‖ζ − 1‖` fails at `p = 2` ✓;
  [3] `s = 0`: `weightPoint p 0 ζ = ζ − 1`, all four statements are the root-of-unity lemmas ✓.
  SURVIVED.

- **B8** `TH_one_weightPoint` — `TargetPoint.lean:118`: `TH p 1 (weightPoint p s ζ) = padicExp (p^2 * s) − 1`.
  Mirror of `TH_one_classicalPoint` (`ClassicalPoint.lean:293`) with `padicExp_natCast_mul`
  (public) in place of the private `padicExp_pow`.  Attacks: [1] `ζ^p = 1` (`hζ.pow_eq_one`) ✓;
  [2] `exp(ps)^p = exp(p·(ps))` needs `‖ps‖² < ‖p‖` ✓ (helper); [3] `p^1` in `TH` — `pow_one` ✓.
  SURVIVED.

- **B9** `norm_TH_one_weightPoint_sq_lt` — `TargetPoint.lean:124`: mirror of
  `norm_TH_one_classicalPoint_sq_lt` (`ClassicalPoint.lean:305`).  Attacks: as B4; the bound
  `‖exp(p²s) − 1‖ ≤ ‖p²s‖ ≤ p⁻²` and `p⁻⁴ < p⁻¹` ✓.  SURVIVED.

- **B10** `haloExponentH_one_weightPoint` — `TargetPoint.lean:130`: `haloExponentH p 1 (weightPoint p s ζ) = s`.
  Mirror of `haloExponentH_one_classicalPoint` (`ClassicalPoint.lean:360`): `haloExponentH`,
  B8, `padicLog_padicExp`, `field_simp`.  Attacks: [1] `padicLog_padicExp` needs
  `‖p²s‖² < ‖p‖` ✓; [2] `p^(1+1)` in the denominator vs `p^2`: `field_simp; ring` ✓;
  [3] `s` negative changes nothing ✓.  SURVIVED.

- **B11** `mk_choose_mul_mk_choose` — `TargetPoint.lean:140`: Vandermonde as formal series.
  Discharged by `PowerSeries.coeff_mul`, `PowerSeries.coeff_mk`, `Ring.add_choose_eq m (Commute.all a b)`,
  `Finset.sum_mul`, `pow_add`.  Attacks: [1] `Ring.add_choose_eq [Ring R] [BinomialRing R] {r s} (k)
  (h : Commute r s) : choose (r+s) k = ∑ ij ∈ antidiagonal k, choose r ij.1 * choose s ij.2`
  (verified in mathlib source) — `K` has `BinomialRing` (the skeleton's `Ring.choose (a : K)`
  elaborates) ✓; [2] `x^{i}·x^{j} = x^{i+j}` with `i + j = m` from `mem_antidiagonal` ✓;
  [3] commutativity of `K` ✓.  SURVIVED.

- **B12** `mk_choose_zero` — `TargetPoint.lean:147`: `Ring.choose_zero_ite`, `PowerSeries.coeff_one`.
  Attacks: [1] `choose 0 k = if k = 0 then 1 else 0` ✓ (mathlib `choose_zero_ite`, verified);
  [2] `x^0 = 1` ✓; [3] none.  SURVIVED.

- **B13** `mk_choose_neg_natCast_mul_pow` — `TargetPoint.lean:153`: `mk(choose (−n) m x^m) * (1 + C x X)^n = 1`.
  `← mk_choose_natCast_mul_pow`, B11, `neg_add_cancel`, B12.  Attacks: [1] `n = 0`: `1 * 1 = 1` ✓;
  [2] this is an identity in `K⟦X⟧`, no convergence question ✓; [3] `Ring.choose (-(n:K))` vs
  `Ring.choose ((-n : ℤ) : K)` — B14 must `push_cast` to this form ✓.  SURVIVED.

- **B14** `autFactor_haloWeightH_weightPoint_neg` — `TargetPoint.lean:167`.
  Source: `autFactor_haloWeightH` (`HaloWeightH.lean:1098`): `autFactor g = C(κ(d)) * mk(choose s_1 m (c/d)^m)`;
  B10 at `s = −(k+2)`; `hlin : 1 + C(c/d)X = C d⁻¹ * linX g` (as `autFactor_haloWeightH_classicalPoint`,
  `ClassicalPoint.lean:414`); B13 at `n = k+2`, `x = c/d`.
  Attacks: [1] `d ≠ 0`: `(levelBounds_M1Kh 1 ψ T₁ hψ hT).d_ne_zero g.2` ✓ (same as C6.12);
  [2] the exponent: `linX^{k+2} = C(d^{k+2})·(1 + C(c/d)X)^{k+2}` and
  `mk · (1 + C(c/d)X)^{k+2} = 1` ⇒ `autFactor · linX^{k+2} = C(κ(d)·d^{k+2})` ✓ — matches the
  statement's constant `haloCharFunH … (g 1 1) * (g 1 1)^(k+2)` ✓; [3] `haloExponentH p 1 T₁ =
  ((−(k+2) : ℤ) : K)`, `push_cast` gives `-((k : K) + 2)` = `-(((k+2 : ℕ)) : K)` after
  `Nat.cast_add`/`Nat.cast_ofNat` ✓.  SURVIVED.

- **B15** `isClassicalShape'_haloWeightH_weightPoint_neg` — `TargetPoint.lean:187`: B14 at
  `g = discConjK 1 (certM1 …) a ψ`, exactly as `isClassicalShape_haloWeightH_classicalPoint`.
  Attacks: [1] `IsClassicalShape'`'s form `autFactor (certConj …) * linX (certConj …)^(k+2) = C (u i t a)`
  and `certConj … = ((discConjK …) : Matrix)` = `g.1` ✓ (definitional); [2] none; [3] none.
  SURVIVED.

- **B16** `certConj_apply_one_one` — `TargetPoint.lean:201`: `certConj … i t a 1 1 = intHom ψ (d : ℤ_p)`.
  `certConj` (`Touching.lean:162`), `coe_discConjK` (`DiscModel.lean:333`), `RingHom.mapMatrix_apply`,
  `Matrix.map_apply`, `M1.coe_toLocalMat_d` (`IntegralModel.lean:308`), `intHom_apply`.
  Attacks: [1] `M1.coe_toLocalMat_d g : ((toLocalMat g).d : ℤ_p) : ℚ_p) = (g : Matrix) 1 1` — applied
  to `g = discConj h δ a` ✓; [2] `(discConj h δ a).1` vs the coercion — same term (`Subtype.val`) ✓;
  [3] general `h`, not just `h = 1` ✓.  SURVIVED.

- **B17** `coe_eq_teichRes_mul_oneUnitPart` — `TargetPoint.lean:207`: `a = ω₀(ā)·⟨a⟩`.
  `teichRes_toZMod`, `oneUnitPart` (`UnitsLog.lean:193`: `((x * (teichmuller x)⁻¹ : ℤ_pˣ) : ℤ_p)`),
  `Units.val_mul`, `mul_comm`, `mul_inv_cancel_left`.  Source: [LWX, Notation 2.1],
  `lwx.txt:413–414`.  Attacks: [1] `ℤ_[p]ˣ` is commutative ✓; [2] the product is taken in `ℤ_p`
  after coercion, `Units.val_mul` ✓; [3] none.  SURVIVED.

- **B18** `continuous_padicExp_mul_intHom` — `TargetPoint.lean:216`: `y ↦ exp(c·ψy)` continuous
  for `‖c‖ ≤ p⁻¹`.  `LipschitzWith.of_dist_le_mul`: `‖exp w − exp w'‖ = ‖exp w'‖·‖exp(w − w') − 1‖
  ≤ ‖w − w'‖` (`padicExp_add`, `norm_padicExp_sub_one_le`, `norm_eq_one_of_norm_sub_le`),
  `norm_intHom`.  Attacks: [1] disc: `‖cψy‖ ≤ p⁻¹`, squared `≤ p⁻² < p⁻¹ = ‖p‖` ✓ (`norm_natCast_p`);
  [2] `w − w' = cψ(y − y')` by `map_sub`, `mul_sub` ✓; [3] `‖exp w'‖ = 1` from
  `‖exp w' − 1‖ ≤ ‖w'‖ ≤ p⁻¹ < 1` ✓.  SURVIVED.

- **B19** `intHom_oneUnitPart_eq_padicExp` — `TargetPoint.lean:223`: `ψ⟨a⟩ = exp(p·ψℓ⟨a⟩)`.
  Source: [LWX, Notation 2.1], `lwx.txt:415–416` ("identify `(1+qℤ_p)^×` with `ℤ_p` via
  `(1/q)log(−)`").  `coe_logQuot` (`ℓ = qlog⟨a⟩/p`), `qlog` (`= padicLog`), `map_div₀`,
  `map_natCast`, `map_padicLog ψ hp2 hψ (hy : ‖⟨a⟩ − 1‖ ≤ p⁻¹)`, `padicExp_padicLog`.
  Attacks: [1] `map_padicLog` needs the `p⁻¹`-disc — `norm_oneUnitPart_sub_one_le` ✓;
  [2] `padicExp_padicLog` needs `‖ψ⟨a⟩ − 1‖² < ‖p‖`: `≤ p⁻²` ✓; [3] the `p` cancels:
  `p · (padicLog(⟨a⟩)/p)` with `((p:ℕ):K) = ψ p ≠ 0` ✓.  SURVIVED.

- **B20** `oneAddPow_weightPoint_mul_padicExp` — `TargetPoint.lean:235`.
  Source: [LWX, §2.1] `lwx.txt:463` (`χ(exp(p^m))^{(log x)/p^m}`), and the existing proof of
  `oneAddPow_pow_mul` (`PowSubOne.lean:98`, density pattern).  `PadicInt.denseRange_natCast.equalizer`
  (`RingHoms.lean:501`; `DenseRange.equalizer (hf) (hg) (h : f ∘ e = g ∘ e) : f = g`), continuity
  from `continuous_oneAddPow_intHom` (B7 for `‖T‖ < 1`) and B18 (`c = p(t−s)`, `‖c‖ ≤ p⁻¹`);
  at `n`: `map_natCast`, `oneAddPow_natCast`, `add_sub_cancel`, `mul_pow`, `padicExp_natCast_mul`,
  `← padicExp_add`, `congr 1; push_cast; ring`.
  Attacks: [1] is the identity true at `n`?  `(ζ e^{ps})^n e^{p(t−s)n} = ζ^n e^{psn + p(t−s)n}
  = ζ^n e^{ptn} = (ζ e^{pt})^n` ✓; [2] all exponentials on the disc: `‖p·(anything of norm ≤ 1)‖²
  < ‖p‖` ✓; [3] `K` Hausdorff (`T2Space`) for `equalizer` ✓; [4] `s = t`: `exp 0 = 1` ✓.
  SURVIVED.

- **B21** `specialize_univChar_targetChar` — `TargetPoint.lean:246`.
  `specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0 h1 ω a` at both points, B2, B3, B1, B17
  (mapped by `intHom ψ`: `ψa = x·e` with `x = ψ(teichmuller a)`, `e = exp(pψℓ)` by B19),
  B20 at `(s, t) = (−(k+2), k)` (`t − s = 2k+2`), `padicExp_natCast_mul` (`e^{2k+2}`),
  `map_units_inv`/`Units.val_pow_eq_pow_val` for `ψ((ω₀ā^{2k+2})⁻¹) = x^{-(2k+2)}`, then
  `field_simp; ring` with `x ≠ 0`, `e ≠ 0`.
  Attacks: [1] re-derivation of the exponent (plain-English proof above): LHS
  `ψ(ωā)·x^{−(2k+2)}·(1+T₁)^{ψℓ}·(xe)^{k+2}`, RHS `ψ(ωā)·(1+T₁)^{ψℓ}·e^{2k+2}·(xe)^{−k}`;
  ratio `x^{−2k−2+k+2+k} · e^{k+2−2k−2+k} = 1` ✓; [2] `x ≠ 0`: image of a unit under an
  injective ring hom ✓; `e ≠ 0`: `‖e − 1‖ < 1` ✓; [3] the halo bounds at both points come from
  B6/B7 (with B3 to rewrite `classicalPoint`) ✓.  SURVIVED.

- **B22** `targetConst_eq_classicalData_u` — `TargetPoint.lean:257`: B16 (both sides), then
  `haloCharFunH_psi 1 ψ T ω' hp2 hψ h0 h1 hT d` at both points (`HaloWeightH.lean:731`), then B21.
  Attacks: [1] `(classicalData …).u i t a` unfolds by `rfl` to `haloCharFunH 1 ψ (classicalPoint p
  k ζ) ω (certConj … 1 1) * (certConj … 1 1)⁻¹ ^ k` ✓ (`show`); [2] `haloCharFunH_psi` wants the
  argument as `intHom ψ (a : ℤ_p)` for `a : ℤ_pˣ` — B16 provides exactly that with `a = d` ✓;
  [3] the `h0 h1 hT` at `T₀ = classicalPoint` are `ClassicalPoint.lean`'s, at `T₁` are B6/B7/B9 ✓.
  SURVIVED.

- **B23** `targetData_classicalPoint` — `TargetPoint.lean:271`: fields `h0 h1 hT` from B6, B7, B9
  (already in the skeleton); `shape := fun i t a => by rw [← targetConst_eq_classicalData_u …];
  exact isClassicalShape'_haloWeightH_weightPoint_neg … i t a`.
  Attacks: [1] `TargetData` is `Prop`-valued (Lean warned "use theorem") — hence a `theorem` ✓;
  [2] the `rw` rewrites `C ((classicalData …).u i t a)` to the target constant, whose form is
  B15's conclusion at `i t a` ✓; [3] none.  SURVIVED.

### Composition attack (Part B)

Could the leaves hold and `TargetData` fail?  `TargetData` has four fields; three are the halo
bounds (B6, B7, B9) and the fourth is B15 with B22 substituted.  The only cross-leaf interface
is the *constant*: B14/B15 produce `κ(d)d^{k+2}`, B22 shows it equals `c.u`.  Edge case `k = 0`:
target weight `(−2, ψ)`, `targetChar ω 0 = ω·ω₀^{−2}` ✓ ([LWX]'s formula at `k = 0`).

---

## Assembly

- **D1** `degX_succ_of_targetData` — `DegreeFormula.lean:36`: `degX_succ idx hp2 hψ hshape hdet c c' d d'
  hAL (isThetaExact_classicalData idx hshape hdet c d)`.  Attacks: [1] `degX_succ`'s argument order
  (explicit `idx` first; `θG h ψ U hU vRep hvΔ uu` implicit after `StepThree.lean:350`) — as used
  in `degXint_zero` ✓; [2] `hH2`'s type is `IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight
  d.weight k`, A25's conclusion verbatim ✓; [3] none.  SURVIVED.

- **D2** `degX_succ_classicalPoint` — `DegreeFormula.lean:54` **(milestone)**: D1 at
  `c = classicalData ψ ω …`, `c' = classicalData ψ ω' …`, `d = targetData_classicalPoint ψ ω …`,
  `d' = targetData_classicalPoint ψ ω' …`, `hpK := norm_natCast_p ψ hψ`.
  Attacks: [1] statement vs [LWX] (`lwx.txt:2074–2076` and the theorem statement `lwx.txt:152–155`):
  `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`; ours has `ω'` (the partner's
  nebentypus, whatever H1 is asserted for) in place of `ω⁻¹ω₀^{2k}` and `targetChar ω k` for the
  second — faithful, with the identification of `ω'` explicitly out of scope ✓; [2] `hζ'`
  independent of `hζ`: H1's partner point may use a different root of unity (`ζ⁻¹` in truth);
  the statement does not force a relation, which is the more general form ✓; [3] `[Nonempty ι]
  [IsAlgClosed K]` are `degX_succ`'s ✓.  SURVIVED.

## Prior-B2 log consultation

`.mathlib-quality/lwx-theta/b2_log.jsonl` (5 entries: the `ν`-family) and
`.mathlib-quality/b2_log.jsonl` (same, plus S7.10): no leaf above shares a statement with a
retired one.  The intertwining is consumed only through `IsClassicalShape`/`IsClassicalShape'`
(the repaired interface); no statement quantifies over slopes past a degree.

## Confidence gate

1. Every leaf has a source locator or is marked as definitional/API ✓.
2. Every mathlib/project discharge was verified by `#check` (2026-09-10) ✓.
3. Skeleton builds, sorries only ✓.  4. No leaf false or needing an unsourced hypothesis ✓.
5. No substantial missing mathlib infrastructure ✓.  6. Attacks recorded per leaf ✓.
7. Composition attacks recorded per part ✓.
