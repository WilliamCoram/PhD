# Ticket Board — lwx-seam ([LWX] Prop 2.17 at `m = 1`; Prop 3.1 in full; `D/ℚ` instance)

**BOARD PATH: `.mathlib-quality/lwx-seam/`** (see `plan.md`; `decomposition.md` has the verbatim
source quotes and attack logs per leaf; `renames.jsonl` / `b2_log.jsonl` live here).
**Concurrent board**: `.mathlib-quality/tate-riesz/` — never touch its files or sentinel.

## Summary
- Total: 143 tickets — 104 proof/def tickets + 39 cleanup tickets
- Open: 0 | In Progress: 0 | Done: 143
- Milestones: **E18** (Prop 2.17 at `m = 1`, abstract `G`), **Q9** (Prop 2.17 for `D/ℚ`),
  **Q10** (spectral reading: zeros of `Char(P)(T₀)` = reciprocal `U_p`-eigenvalues on `S^D_{κ_{T₀}}(U)`)
- Parallel capacity at start: 6 (C ∥ S ∥ B ∥ M ∥ H ∥ F); W after S9+B10; E after C+S+M+W+H; Q last

## Conventions (binding)
- Statements below are **verbatim from the skeleton**; `/beastmode` fills the `sorry` at the cited
  `file:line` (line numbers as of 2026-09-05; search by name if they drift).
- `lia` → `omega`; every ticket: `lake build PhD.<Module>` clean, no `sorry`, standard axioms;
  `lake exe runLinter PhD.<Module>` clean on the file's own declarations at every CLEANUP;
  renames/statement-fixes to `renames.jsonl`, B2 stops to `b2_log.jsonl` (this directory).
- Cleanups are run **inline by the main agent** (no subagent dispatch).
- Never edit `Halo.lean`, `IntegralModel.lean`, `UpMatrix.lean`, `HaloRing.lean`,
  `PadicExpLog.lean`, `UnitsLog.lean`, the QMF layer, or any `tate-riesz` file; helpers go in the
  nine board files.
- Common hypotheses: `HYP` = `(hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
  (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)`; `hpK : ‖((p:ℕ):K)‖ < 1` and `‖((p:ℕ):K)‖ = p⁻¹` come from `hψ`
  (`norm_natCast_p`, W1).  `κ` = `haloWeight ψ T₀ ω hp2 hψ h0 h1`; `χ` = `haloCharFun ψ T₀ ω`;
  `s` = `haloExponent T₀`; `ρ` = `haloRho T₀`.

## Dependency chains
```
C1 → C2 → C3 ; C4, C5, C6, C7 independent ; C4+C5 → C8                    [Conjugation.lean]
S1, S3, S4 independent ; S2, S5, S6 independent ; S1+S2+S6 → S7 ; S8 ; S3+S5+S8 → S9   [Specialize.lean]
B1 → B2 ; B3, B4, B5, B6, B8 independent ; B1+B6 → B7 ; B3+B4+B5+B6+B7+B8 → B9 ; B2+B7+B8+B9 → B10  [Binomial.lean]
M1, M2, M3, M4, M5 independent ; M3 → M6 ; M7 → M8, M9 ; M8+M9 → M10 ; M8+M10 → M11 ;
M12, M13 independent ; M4+M7+M12+M13 → M14 ; M11+M13+M14 → M15 ; M16 independent   [Colmez.lean]
W1 ; W2 → W3 → W4, W7 ; W4 → W5 ; W3+W4 → W6 ; W1 → W8 ; W5+W7+W8 → W9 ; W1 → W10 ; W7 → W11 → W12 ;
W6+W9+W10+W11 → W13 ; W10+W11 → W14 ; S9+B10+W4+W5+W11 → W15 ; W12+W13+W14 → W16 ; W17 ;
W1+W17 → W18 ; W1+W8 → W19 ; W10+W14+W17+W18 → W20 ; B10+W10+W11+W13+W19 → W21 ; W16+W21 → W22 ;
W22 → W23 → W24                                                            [HaloWeight.lean]
H1 → H2 ; H3 → H4 ; H5 ; H6 independent                                    [Certificates.lean]
S6 → E1 → E2 → E3 (S5) → E4 (S7) → E5 ; E6 ; M6 → E7 → E8 ; E9 → E10 ; E11 ;
S3+S5+W15+W24+E9+E10 → E12 ; M5+M16+E1+E8+E11+E12 → E13 ; M15+C5+C8 → E14 ;
C5+C6+E2+E13 → E15 ; W17 → E16 ; E14+E15+C8 → E17 ; C3+E5+E16+E17 → E18 (MILESTONE)   [Seam.lean]
F1 → F2 → F3                                                               [AdicCompletionEquiv.lean]
Q1 ; Q2 ; F3 → Q3 ; Q1+Q3 → Q4 ; Q2 → Q5 ; E6+Q5 → Q6 ; Q2+Q4 → Q7 → Q8 ;
E18+Q5+Q6 → Q9 (MILESTONE) ; H4+H6+E16+Q8+Q9 → Q10 (MILESTONE)              [Quaternionic.lean]
Cleanup cadence: CL-C1 after C3, CL-C2 after C6, CL-C3 after C8 ; CL-S1 after S3, CL-S2 after S6,
CL-S3 after S9 ; CL-B1 after B3, CL-B2 after B6, CL-B3 after B9, CL-B4 after B10 ;
CL-M1..M5 after M3/M6/M9/M12/M15, CL-M6 after M16 ; CL-W1..W7 after W3/W6/W9/W12/W15/W18/W21,
CL-W8 after W24 ; CL-H1 after H3, CL-H2 after H6 ; CL-E1..E5 after E3/E6/E9/E12/E15,
CL-E6 after E18 ; CL-F1 after F3 ; CL-Q1 after Q3, CL-Q2 after Q6, CL-Q3 after Q10 ;
CLEANUP-ALL-1 before E18 ; CLEANUP-ALL-2 before Q10 ; CLEANUP-FINAL last.
```

---

## Tranche C — `PhD/TateFredholm/Conjugation.lean` (general TateFredholm)

### [C1] Diagonal intertwining preserves principal minors
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:55 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem minor_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) (S : Finset I) :
    minor v S = minor u S
```
#### Proof sketch
`minor u S = det (Matrix.of fun j i : S => matrixCoeff u j i)` (Fredholm.lean:33).  Set
`Dm : Matrix S S R := Matrix.diagonal fun i => d i`.  From `h`: `Dm * Mv = Mu * Dm` entrywise
(`Matrix.diagonal_mul`, `Matrix.mul_diagonal`, `Matrix.ext`).  Take `det`: `det Dm * det Mv = det Mu * det Dm`
(`Matrix.det_mul`); `det Dm = ∏ i : S, d i` (`Matrix.det_diagonal`) is a unit
(`IsUnit.prod`/`Finset.prod_isUnit`... e.g. `isUnit_of_mul_eq_one` via `Finset.prod` of units, or
`Units` product); cancel with `IsUnit.mul_left_cancel` after `mul_comm`.
#### Sources
[LWX, Prop 2.17, proof] (lwx.txt:990–1016): "P and P′ are conjugated by an infinite diagonal
matrix … taking the limit of the characteristic polynomial of the first r×r-minors".

### [C2] Diagonal intertwining preserves `charCoeff`
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:63 | **Depends on**: C1
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem charCoeff_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) (n : ℕ) :
    charCoeff v n = charCoeff u n
```
#### Proof sketch
`unfold charCoeff`; `congr 1`; `tsum_congr fun S => minor_eq_of_diag_intertwine d hd h S`.  No
summability needed (termwise equality of the defining `tsum`).
#### Sources
As C1; `charCoeff` definition Fredholm.lean:148.

### [C3] `det(I − XP′) = det(I − XP)` for diagonally intertwined operators
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:71 | **Depends on**: C2
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem charPowerSeries_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) :
    charPowerSeries v = charPowerSeries u
```
#### Proof sketch
`PowerSeries.ext fun n => by simp only [charPowerSeries_coeff]; exact charCoeff_eq_of_diag_intertwine d hd h n`.
#### Sources
As C1.

### [CL-C1] /cleanup Conjugation.lean (after C3)
- **Status**: done (inline cleanup 2026-09-05T14:40Z: header, omits, runLinter clean) | **File**: PhD/TateFredholm/Conjugation.lean | **Depends on**: C3
- **Type**: cleanup — inline; runLinter `PhD.TateFredholm.Conjugation`.

### [C4] `blockDiag id = id`
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:86 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem blockDiag_id : blockDiag (σ := σ) (ContinuousLinearMap.id R c(I, R))
    = ContinuousLinearMap.id R c(σ × I, R)
```
#### Proof sketch
`ext_matrixCoeff`; `matrixCoeff_blockOp` (BlockOp.lean:654) gives `if a = b then matrixCoeff id j i else 0`;
`matrixCoeff (id) (a,j) (b,i) = if (a,j) = (b,i) then 1 else 0` (unfold `matrixCoeff`,
`cSpace.single_apply_self/_of_ne`); `Prod.ext_iff`, `split_ifs`.
#### Sources
Block-diagonal reading of (2.11.1); BlockOp.lean:630–660.

### [C5] `blockDiag f ∘ blockOp T = blockOp (f ∘ T a b)`
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:92 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem blockDiag_comp_blockOp (f : c(I, R) →L[R] c(I, R))
    (T : σ → σ → (c(I, R) →L[R] c(I, R))) :
    (blockDiag f).comp (blockOp T) = blockOp fun a b => f.comp (T a b)
```
#### Proof sketch
`unfold blockDiag`; `rw [blockOp_comp]` (BlockOp.lean:699: `blockOp (fun a c => ∑ b, (T a b).comp (S b c))`);
`congr 1; funext a c`; `simp [Finset.sum_ite_eq, ContinuousLinearMap.zero_comp]` — the sum
`∑ b, (if a = b then f else 0).comp (T b c)` collapses to `f.comp (T a c)`.
#### Sources
BlockOp.lean:699 (`blockOp_comp`); mirror of the private scalar `diagBlock_comp_blockOp` (:833).

### [C6] `blockOp T ∘ blockDiag f = blockOp (T a b ∘ f)`
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:98 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem blockOp_comp_blockDiag (T : σ → σ → (c(I, R) →L[R] c(I, R)))
    (f : c(I, R) →L[R] c(I, R)) :
    (blockOp T).comp (blockDiag f) = blockOp fun a b => (T a b).comp f
```
#### Proof sketch
As C5 with `Finset.sum_ite_eq'` and `ContinuousLinearMap.comp_zero`.
#### Sources
As C5.

### [CL-C2] /cleanup Conjugation.lean (after C6)
- **Status**: done (inline cleanup 2026-09-05T14:40Z: header, omits, runLinter clean) | **File**: PhD/TateFredholm/Conjugation.lean | **Depends on**: C6
- **Type**: cleanup — inline.

### [C7] Matrix of `blockDiag`
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:103 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem matrixCoeff_blockDiag (f : c(I, R) →L[R] c(I, R)) (a b : σ) (j i : I) :
    matrixCoeff (blockDiag f) (a, j) (b, i) = if a = b then matrixCoeff f j i else 0
```
#### Proof sketch
`unfold blockDiag; rw [matrixCoeff_blockOp]; split_ifs <;> simp [matrixCoeff_zero]`.
#### Sources
BlockOp.lean:654.

### [C8] `diagBlockEquiv` is an equivalence
- **Status**: done (finished 2026-09-05T14:40Z) | **File**: PhD/TateFredholm/Conjugation.lean:109 | **Depends on**: C4, C5
- **Parallel**: no | **Type**: def (two proof obligations)
#### Statement
```lean
def diagBlockEquiv (e : c(I, R) ≃L[R] c(I, R)) : c(σ × I, R) ≃L[R] c(σ × I, R) :=
  ContinuousLinearEquiv.equivOfInverse (blockDiag (e : c(I, R) →L[R] c(I, R)))
    (blockDiag (e.symm : c(I, R) →L[R] c(I, R))) (by sorry) (by sorry)
```
**Progress**: 2026-09-05T14:40Z DONE — added public `blockDiag_comp` (g ∘ f blockwise); both
inverse obligations via `blockDiag_comp` + `blockDiag_id`; `DFunLike.congr_fun` (not
`ContinuousLinearMap.congr_fun`).  All of C1–C8 proven in one pass; axioms standard.
#### Proof sketch
Both obligations are `Function.LeftInverse`: for `x`, `blockDiag e.symm (blockDiag e x) = x`.
Prove the operator identity `(blockDiag e.symm).comp (blockDiag e) = id` by
`unfold blockDiag; rw [blockDiag_comp_blockOp]`-style (C5 with `T := fun a b => if a = b then e else 0`),
then `funext`/`simp [ContinuousLinearEquiv.symm_comp_self, ite_comp]` to reach
`blockDiag id = id` (C4); apply to `x` via `ContinuousLinearMap.congr_fun`.  Symmetric for the other.
#### Sources
`ContinuousLinearEquiv.equivOfInverse` (Mathlib/Topology/Algebra/Module/Equiv.lean:626).

### [CL-C3] /cleanup Conjugation.lean — final (after C8)
- **Status**: done (inline cleanup 2026-09-05T14:40Z: header, omits, runLinter clean) | **File**: PhD/TateFredholm/Conjugation.lean | **Depends on**: C8
- **Type**: cleanup — inline; also `omit [DecidableEq I] in` for `coe_diagBlockEquiv(_symm)`
  (linter finding at skeleton time).

---

## Tranche S — `PhD/LWX/Specialize.lean`

Section variables: `(ψ : ℤ_[p] →+* K) (hψ) {T₀} (h0 : p⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)`; the
theorems that need summability carry `include hψ h0 h1 in`.

### [S1] `specialize_zero`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:52 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_zero : specialize ψ T₀ (0 : HaloInt p) = 0
```
#### Proof sketch
`unfold specialize`; `(0 : HaloInt p) j = 0` (`rfl`/`HaloInt.coe_zero`?), `map_zero`, `zero_mul`,
`tsum_zero`.
#### Sources
HaloRing.lean:594.

### [S2] `specialize_add`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:48 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_add (f g : HaloInt p) :
    specialize ψ T₀ (f + g) = specialize ψ T₀ f + specialize ψ T₀ g
```
#### Proof sketch
`(f + g) j = f j + g j` (pointwise addition, `rfl`), `map_add`, `add_mul`, then
`(summable_specialize ψ hψ h0 h1 f).tsum_add (summable_specialize ψ hψ h0 h1 g)` (HaloRing.lean:652).
#### Sources
HaloRing.lean:652 (`summable_specialize`).

### [S3] `specialize_const`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:75 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_const (x : ℤ_[p]) : specialize ψ T₀ (const x) = ψ x
```
#### Proof sketch
`const x` has coefficients `if j = 0 then x else 0` (HaloRing.lean:528; check the exact form, e.g.
`HaloInt.coeff_const`); `tsum_eq_single 0` then `simp [zpow_zero]`.
#### Sources
HaloRing.lean:528–545.

### [CL-S1] /cleanup Specialize.lean (after S3)
- **Status**: done (inline cleanup 2026-09-05T15:20Z: header, omits, deprecated names, runLinter clean) | **File**: PhD/LWX/Specialize.lean | **Depends on**: S3 — inline.

### [S4] `specialize_T`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:79 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_T : specialize ψ T₀ (T : HaloInt p) = T₀
```
#### Proof sketch
`T = δ₁` (HaloRing.lean:447: coefficient `1` at `j = 1`, else `0`); `tsum_eq_single 1`; `zpow_one`.
#### Sources
HaloRing.lean:447–461.

### [S5] `specialize_mul` (Cauchy product over `ℤ × ℤ`)
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:59 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_mul (f g : HaloInt p) :
    specialize ψ T₀ (f * g) = specialize ψ T₀ f * specialize ψ T₀ g
```
#### Proof sketch
1. Let `a i := ψ (f i) * T₀ ^ i`, `b j := ψ (g j) * T₀ ^ j`; both `Tendsto · cofinite (𝓝 0)`
   (the private `tendsto_spec_cofinite` in HaloRing.lean is not exported — re-derive from
   `summable_specialize` via `Summable.tendsto_cofinite_zero`).
2. The product family `q : ℤ × ℤ → K`, `q (i, j) = a i * b j`, tends to `0` cofinitely: given
   `ε`, bound `A := ⨆ ‖a i‖`, `B := ⨆ ‖b j‖` (finite: `≤ 1`... use `norm_spec_term`-type bound
   `‖a i‖ ≤ 1` for `i ≥ 0` and `≤ (p‖T₀‖)^i`-decay for `i < 0`; simplest: both families are
   bounded since they tend to `0`), and the finite sets `{i : ‖a i‖ ≥ ε/B}`, `{j : ‖b j‖ ≥ ε/A}`;
   outside `F₁ × ℤ ∪ ℤ × F₂` the product is `< ε`.  Hence `Summable q`
   (`TateFredholm.summable_of_tendsto_cofinite`).
3. `tsum_mul_tsum (hf) (hg) (hq)`: `(∑' i, a i) * (∑' j, b j) = ∑' x : ℤ × ℤ, a x.1 * b x.2`.
4. Reindex by the equiv `(i, k) ↦ (i, k - i)` (`Equiv.tsum_eq`), then `tsum_prod'` (summability of
   the reindexed family and of each fibre `i ↦ a i * b (k − i)` — the latter from
   `HaloRing.summable_mul_coeff f g k` mapped by `ψ` and multiplied by `T₀^k`), and `tsum_comm'`
   to get `∑' k, ∑' i, ψ (f i) ψ (g (k − i)) T₀^k` (`zpow_add₀ (T₀ ≠ 0)`, `T₀ ≠ 0` from `h0`).
5. `HaloInt.coeff_mul f g k = ∑' i, f i * g (k - i)` (HaloRing.lean:159); `ψ` is continuous
   (isometric: `AddMonoidHomClass.continuous_of_bound ψ 1`), so `map_tsum`; assemble.
**Progress**: 2026-09-05T15:20Z DONE — as sketched; new public helper
`norm_specialize_term_le_one` (every term of the series has norm ≤ 1 on the annulus, which is what
makes the `ℤ × ℤ` cofinite argument one-line); `Summable.tsum_prod'`/`Equiv.tsum_eq`/
`Summable.tsum_mul_tsum` are dot-notation lemmas in this mathlib.
#### Sources
HaloRing.lean:119 (`summable_mul_coeff`), :159 (`coeff_mul`); [LWX, Cor 3.18] evaluation.

### [S6] `continuous_specialize`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:85 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem continuous_specialize : Continuous (specialize ψ T₀ : HaloInt p → K)
```
#### Proof sketch
Build `specializeAddHom : HaloInt p →+ K` from S1/S2 (or use `specializeHom`'s `toAddMonoidHom` —
note the def needs `hψ h0 h1`, available).  `continuous_of_continuousAt_zero`; at `0`:
`Metric.continuousAt_iff`; given `ε > 0` pick `k` with `‖T₀‖ ^ k < ε` (`exists_pow_lt_of_lt_one`),
`δ := (p:ℝ)^(-(k:ℤ))`; for `dist f 0 < δ`, `‖f‖ ≤ p^{-k}` so `norm_specialize_le ψ hψ h0 h1 hf`
gives `‖specialize f‖ ≤ ‖T₀‖^k < ε`; `specialize 0 = 0` (S1).
#### Sources
HaloRing.lean:660 (`norm_specialize_le`).

### [CL-S2] /cleanup Specialize.lean (after S6)
- **Status**: done (inline cleanup 2026-09-05T15:20Z: header, omits, deprecated names, runLinter clean) | **File**: PhD/LWX/Specialize.lean | **Depends on**: S6 — inline.

### [S7] `HasSum.specialize`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:91 | **Depends on**: S1, S2, S6
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem HasSum.specialize {ι : Type*} {f : ι → HaloInt p} {a : HaloInt p}
    (hf : HasSum f a) : HasSum (fun i => specialize ψ T₀ (f i)) (specialize ψ T₀ a)
```
#### Proof sketch
`hf.map (specializeHom ψ hψ h0 h1).toAddMonoidHom (continuous_specialize ψ hψ h0 h1)`
(`HasSum.map`), then `simpa [Function.comp]`.
#### Sources
mathlib `HasSum.map`.

### [S8] `specialize_oneAddTPow`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:111 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem specialize_oneAddTPow (s : ℤ_[p]) :
    HaloInt.specialize ψ T₀ (oneAddTPow p s) = oneAddPow T₀ (ψ s)
```
#### Proof sketch
`unfold specialize oneAddPow`; `coeff_oneAddTPow`: term `j` is `ψ (if 0 ≤ j then Ring.choose s j.toNat else 0) * T₀^j`.
Reindex `ℤ ← ℕ` along `Nat.cast` (injective; terms at `j < 0` vanish):
`tsum_eq_tsum_of_ne_zero_bij` or `Function.Injective.tsum_eq` with support condition; `Int.toNat_natCast`,
`zpow_natCast`.  Then `ψ (Ring.choose s r) = Ring.choose (ψ s) r`: from
`Ring.descPochhammer_eq_factorial_smul_choose` on both sides (`(r ! • choose s r) = (descPochhammer ℤ_[p] r).smeval s`),
map by `ψ` (`Polynomial.smeval` commutes with ring homs: `Polynomial.smeval_map`/`descPochhammer_map`),
and cancel `(r ! : K) ≠ 0` (`Nat.cast_ne_zero`, `CharZero K`); `nsmul_eq_mul`.  Consider a
standalone `map_ringChoose` lemma (private) for reuse in S9/W15.
#### Sources
IntegralModel.lean:62–80 (`oneAddTPow`, `coeff_oneAddTPow`); [LWX, Notation 2.1].

### [S9] `specialize_univChar`
- **Status**: done (finished 2026-09-05T15:20Z) | **File**: PhD/LWX/Specialize.lean:119 | **Depends on**: S3, S5, S8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem specialize_univChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a : ℤ_[p]ˣ) :
    HaloInt.specialize ψ T₀ (univChar ω a)
      = ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * oneAddPow T₀ (ψ (logQuot a))
```
#### Proof sketch
`unfold univChar` (IntegralModel.lean:159: `const (ω ā) * oneAddTPow p (logQuot a)`);
`specialize_mul`, `specialize_const`, `specialize_oneAddTPow`.
#### Sources
IntegralModel.lean:159; [LWX, Notation 2.1].

### [CL-S3] /cleanup Specialize.lean — final (after S9)
- **Status**: done (inline cleanup 2026-09-05T15:20Z: header, omits, deprecated names, runLinter clean) | **File**: PhD/LWX/Specialize.lean | **Depends on**: S9 — inline.

---

## Tranche B — `PhD/LWX/Binomial.lean` (`namespace LWX.PadicExpLog`)

Section variables `(h3 : ‖((p:ℕ):K)‖ < 1) (hp2 : p ≠ 2)`, `include`d; `[CharZero K]`.
Write `q := Real.sqrt (‖((p:ℕ):K)‖⁻¹)` in sketches (so `‖1/r!‖ ≤ q^(r−1)` from
`sq_norm_factorial_ge h3 hp2 : ‖p‖^(n−1) ≤ ‖n!‖^2`, PadicExpLog.lean:89).

### [B1] Termwise bound for the binomial series
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:56 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_choose_mul_pow_le (e x : K) (r : ℕ) :
    ‖Ring.choose e r * x ^ r‖ ≤ max ‖x‖ (‖e‖ * ‖x‖) ^ r * ‖((r ! : ℕ) : K)‖⁻¹
```
#### Proof sketch
`Ring.choose e r = (descPochhammer K r).eval e / r!` — from `Ring.descPochhammer_eq_factorial_smul_choose`
(`r ! • choose e r = (descPochhammer K r).smeval e`, `smeval` = `eval` over `K`,
`Polynomial.descPochhammer_eval_eq_prod_range : (descPochhammer R r).eval e = ∏ k ∈ range r, (e - k)`).
Then `‖∏ (e − k)‖ = ∏ ‖e − k‖ ≤ max ‖e‖ 1 ^ r` (`IsUltrametricDist.norm_sub_le_max`, `norm_natCast_le_one`);
so `‖choose e r * x^r‖ ≤ max ‖e‖ 1 ^ r * ‖x‖^r * ‖r!‖⁻¹ = max ‖x‖ (‖e‖‖x‖) ^ r * ‖r!‖⁻¹`
(`max_mul_of_nonneg`).  `norm_div`, `norm_inv`.
#### Sources
[Koblitz, IV §2]; mathlib `RingTheory/Binomial.lean:390`.

### [B2] Summability of the binomial series
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:63 | **Depends on**: B1
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem summable_choose_mul_pow {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖) {e x : K}
    (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    Summable fun r : ℕ => Ring.choose e r * x ^ r
```
#### Proof sketch
`TateFredholm.summable_of_tendsto_cofinite` + `Nat.cofinite_eq_atTop`; `squeeze_zero_norm` with
the majorant `c ^ r * q ^ (r - 1)` (for `r ≥ 1`; treat `r = 0` separately or use `q^r * q⁻¹`):
from B1, `max ‖x‖ (‖e‖‖x‖) ≤ c`, and `‖r!‖⁻¹ ≤ q^(r−1)` (`sq_norm_factorial_ge`, `Real.sqrt` algebra:
`‖r!‖ ≥ ‖p‖^((r−1)/2)`).  `(c*q)^r → 0` since `c * q < 1 ⇔ c^2 < ‖p‖` (`Real.sqrt_lt'`, `Real.mul_self_sqrt`).
#### Sources
PadicExpLog.lean:89 (`sq_norm_factorial_ge`).

### [B3] The finite binomial theorem as a series
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:69 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem tsum_choose_natCast_mul_pow (n : ℕ) (x : K) :
    ∑' r : ℕ, Ring.choose (n : K) r * x ^ r = (1 + x) ^ n
```
#### Proof sketch
`Ring.choose_natCast : Ring.choose (n : K) r = n.choose r`; terms vanish for `r > n`
(`Nat.choose_eq_zero_of_lt`); `tsum_eq_sum` over `range (n+1)`; `add_pow` (`(1+x)^n = ∑ 1^k x^{n−k} …`
— use `add_comm` and `Commute`-free `add_pow` then reindex, or `(x + 1)^n` form `add_pow x 1`).
#### Sources
mathlib `Ring.choose_natCast` (Binomial.lean:399), `add_pow`.

### [CL-B1] /cleanup Binomial.lean (after B3)
- **Status**: done (inline cleanup 2026-09-05T16:05Z: header, omits, runLinter clean) | **File**: PhD/LWX/Binomial.lean | **Depends on**: B3 — inline.

### [B4] `exp(n·log(1+x)) = (1+x)^n`
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:74 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem padicExp_natCast_mul_padicLog (n : ℕ) {x : K} (hx : ‖x‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    padicExp ((n : K) * padicLog (1 + x)) = (1 + x) ^ n
```
#### Proof sketch
`padicExp_natCast_mul h3 hp2 (hw : ‖padicLog (1+x)‖^2 < ‖p‖) n` (PadicExpLog.lean:578) with
`‖padicLog (1 + x)‖ = ‖x‖` (`norm_padicLog_eq h3 hp2`, :753, hypothesis `‖(1+x) − 1‖^2 < ‖p‖`),
then `padicExp_padicLog h3 hp2 (hu : ‖(1+x) − 1‖^2 < ‖p‖)` (:839).
#### Sources
PadicExpLog.lean:578, :753, :839.

### [B5] The identity theorem on `ℕ`
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:83 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem eq_zero_of_forall_tsum_natCast_eq_zero {a : ℕ → K} {C q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < 1) (ha : ∀ j, ‖a j‖ ≤ C * q ^ j) (h : ∀ n : ℕ, ∑' j, a j * (n : K) ^ j = 0) :
    ∀ j, a j = 0
```
(`hq0` added at execution — `renames.jsonl`.)
#### Proof sketch
By contradiction: let `j₀ := Nat.find (∃ j, a j ≠ 0)`.  `‖p‖ < 1` gives `‖(p^k : K)‖ = ‖p‖^k`
(`norm_pow`, `Nat.cast_pow`) `→ 0`.  For each `k`, split the sum: `∑' j, a j (p^k)^j =
∑_{j<j₀} 0 + a j₀ (p^k)^{j₀} + ∑'_{j>j₀} a j (p^k)^j` (`tsum_eq_add_tsum_ite`/`sum_add_tsum_nat_add`);
the tail has norm `≤ sup_{j>j₀} C q^j ‖p‖^{kj} ≤ C q^{j₀+1} ‖p‖^{k(j₀+1)}` (`TateFredholm.norm_tsum_le_iSup`
— the ultrametric sup bound) `< ‖a j₀‖ ‖p‖^{k j₀}` for `k` large (since `‖p‖^k → 0` and
`q ≤ 1`... note `q` may be `≤ 0`; use `max q 0` or note `‖a j‖ ≤ C q^j` forces… — handle `q ≤ 0`
trivially: then `a j = 0` for `j ≥ 1` hmm, `C q^j` alternates; assume WLOG replace `q` by `|q|`
via `‖a j‖ ≤ C * |q|^j`).  Then `‖∑'‖ = ‖a j₀‖‖p‖^{kj₀} ≠ 0` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`),
contradicting `h (p^k)`.  Summability of `j ↦ a j (p^k)^j`: geometric majorant.
**Progress**: 2026-09-05T16:05Z DONE.  Traps: keep `j₀ = Nat.find …` and `z = ↑(p^k)` *opaque*
(`obtain ⟨j₀, …⟩ : ∃ j₀, …` / `obtain ⟨z, hz⟩ : ∃ z, z = …`) — `set` versions made `whnf` time out;
give `Summable.sum_add_tsum_nat_add'` its `(f := …) (k := …)` explicitly (HO-unification timeout
otherwise); no `by`-blocks inside `rw […]` lists (parse errors reported many lines later).
#### Sources
Strassman's theorem, elementary form ([Koblitz, IV §4]); the QMF `TendstoCoeff.eq_zero_of_forall_evalAt_eq_zero`
(Char.lean:133) is the same argument at all `‖z‖ ≤ 1` — mirror its structure with `z := p^k`.

### [B6] Coefficient bound for `chooseCoeff`
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:95 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_chooseCoeff_le {x : K} (hx : ‖x‖ ^ 2 < ‖((p : ℕ) : K)‖) (j : ℕ) :
    ‖chooseCoeff x j‖ ≤ (‖x‖ * Real.sqrt (‖((p : ℕ) : K)‖⁻¹)) ^ j
```
#### Proof sketch
`chooseCoeff x j = ∑' r, ((descPochhammer ℤ r).coeff j : K) / r! * x^r`; terms vanish for `r < j`
(`Polynomial.coeff_eq_zero_of_natDegree_lt`, `descPochhammer_natDegree`); for `r ≥ j`:
`‖coeff‖ ≤ 1` (integer: `IsUltrametricDist.norm_intCast_le_one` or `norm_natCast_le_one` + `norm_neg`),
`‖1/r!‖ ≤ q^(r−1)`, so term `≤ ‖x‖^r q^(r−1) = ‖x‖^j q^(j−1) (‖x‖ q)^(r−j) ≤ (‖x‖ q)^j`
(as `‖x‖ q < 1` and `q ≥ 1`... careful: `q ≥ 1` since `‖p‖ ≤ 1`; then `‖x‖^j q^{j−1} ≤ (‖x‖q)^j`).
`TateFredholm.norm_tsum_le_iSup` (or `norm_tsum_le_of_forall_le` in the ultrametric library) with
the uniform bound; summability by the same majorant.  Case `j = 0`: `chooseCoeff x 0 = 1`
(`descPochhammer` has zero constant term for `r ≥ 1`: `descPochhammer_eval_zero`).
#### Sources
PadicExpLog.lean:89; mathlib `descPochhammer_natDegree`, `descPochhammer_eval_zero`.

### [CL-B2] /cleanup Binomial.lean (after B6)
- **Status**: done (inline cleanup 2026-09-05T16:05Z: header, omits, runLinter clean) | **File**: PhD/LWX/Binomial.lean | **Depends on**: B6 — inline.

### [B7] The binomial series as a power series in the exponent (Fubini)
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:102 | **Depends on**: B1, B6
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem tsum_choose_mul_pow_eq_tsum_chooseCoeff {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖)
    {e x : K} (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    ∑' r : ℕ, Ring.choose e r * x ^ r = ∑' j : ℕ, chooseCoeff x j * e ^ j
```
#### Proof sketch
`Ring.choose e r = ∑_{j ≤ r} (descPochhammer ℤ r).coeff j * e^j / r!`
(`Polynomial.eval_eq_sum_range` on `descPochhammer K r = (descPochhammer ℤ r).map (Int.castRingHom K)`,
`descPochhammer_map`, `Polynomial.coeff_map`; `Ring.descPochhammer_eq_factorial_smul_choose`).
Define `F : ℕ × ℕ → K`, `F (r, j) = ((descPochhammer ℤ r).coeff j : K) / r! * x^r * e^j`
(zero for `j > r`).  `Summable F` on `ℕ × ℕ` by cofinite decay: `‖F (r,j)‖ ≤ max ‖x‖ (‖e‖‖x‖)^r q^(r−1) ≤ c^r q^(r−1)`
uniformly in `j ≤ r` (for `j ≤ r`, `‖e‖^j ‖x‖^r ≤ max(‖x‖, ‖e‖‖x‖)^r`), and only finitely many `j`
per `r`; `TateFredholm.summable_of_tendsto_cofinite`.  Then `tsum_prod'` twice (fibre summabilities
from the same bound) / `tsum_comm'`: `∑' r, ∑' j, F = ∑' j, ∑' r, F`; the inner sums are
`Ring.choose e r * x^r` (finite sum, `tsum_eq_sum`) and `chooseCoeff x j * e^j` (`tsum_mul_right`).
**Progress**: 2026-09-05T16:05Z DONE — via `Summable.tsum_comm'` with `Summable.prod_factor` /
`prod_symm.prod_factor`; the `ℕ × ℕ` cofinite argument uses `Set.Finite.prod` of two `Finset.range`s.
New public helpers in Binomial.lean: `choose_mul_factorial`, `norm_factorial_inv_le`,
`one_le_sqrt_inv_norm_p`, `mul_sqrt_inv_norm_p_lt_one`.
#### Sources
[Koblitz, IV §2]; mathlib `Summable.tsum_prod'`, `Summable.tsum_comm'`.

### [B8] `exp(e·L)` as a power series in `e`
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:109 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem padicExp_mul_eq_tsum (e x : K) :
    padicExp (e * padicLog (1 + x))
      = ∑' j : ℕ, padicLog (1 + x) ^ j / ((j ! : ℕ) : K) * e ^ j
```
(unused disc hypotheses dropped at execution — `renames.jsonl`.)
#### Proof sketch
`padicExp w = ∑' j, w^j / j!` (PadicExpLog.lean:174, definitional); `tsum_congr`: `(e*L)^j / j! = L^j/j! * e^j`
(`mul_pow`, `ring`).  No convergence hypotheses needed for the identity of `tsum`s (termwise equal).
#### Sources
PadicExpLog.lean:174.

### [B9] The exponent coefficients agree
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:116 | **Depends on**: B3, B4, B5, B6, B7, B8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem chooseCoeff_eq_padicLog_pow_div_factorial {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖)
    {x : K} (hx : ‖x‖ ≤ c) (j : ℕ) :
    chooseCoeff x j = padicLog (1 + x) ^ j / ((j ! : ℕ) : K)
```
#### Proof sketch
Let `L := padicLog (1 + x)`, `‖L‖ = ‖x‖` (`norm_padicLog_eq`; `‖x‖² ≤ c² < ‖p‖`), and
`a j := chooseCoeff x j − L^j / j!`.  Bound: `‖a j‖ ≤ (‖x‖ q)^j` (B6 and `‖L^j/j!‖ ≤ ‖x‖^j q^(j−1) ≤ (‖x‖q)^j`),
with `‖x‖ q < 1` (`hx`, `hc`).  Vanishing on `ℕ`: for `n : ℕ`, `∑' j, a j n^j = ∑' j, chooseCoeff x j n^j − ∑' j, (L^j/j!) n^j`
(`tsum_sub`, summable by the geometric bound) `= ∑' r, choose n r x^r − padicExp (n L)`
(B7 at `e = n` — hypotheses `‖n‖‖x‖ ≤ ‖x‖ ≤ c` since `‖(n:K)‖ ≤ 1`; B8) `= (1+x)^n − (1+x)^n = 0`
(B3, B4).  Conclude by B5 (`C = 1`, `q' = ‖x‖ q`): `a j = 0`, so `sub_eq_zero`.
#### Sources
[Koblitz, IV §2] (the argument "both sides are analytic in the exponent and agree on `ℕ`").

### [CL-B3] /cleanup Binomial.lean (after B9)
- **Status**: done (inline cleanup 2026-09-05T16:05Z: header, omits, runLinter clean) | **File**: PhD/LWX/Binomial.lean | **Depends on**: B9 — inline.

### [B10] **The `p`-adic binomial theorem for an arbitrary exponent**
- **Status**: done (finished 2026-09-05T16:05Z) | **File**: PhD/LWX/Binomial.lean:124 | **Depends on**: B2, B7, B8, B9
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem hasSum_choose_mul_pow {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖) {e x : K}
    (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    HasSum (fun r : ℕ => Ring.choose e r * x ^ r) (padicExp (e * padicLog (1 + x)))
```
#### Proof sketch
`(summable_choose_mul_pow …).hasSum` (B2) has sum `∑' r, …` `= ∑' j, chooseCoeff x j e^j` (B7)
`= ∑' j, L^j/j! e^j` (B9, `tsum_congr`) `= padicExp (e L)` (B8).  `HasSum.congr`/rewrite the sum.
#### Sources
[Koblitz, IV §2]; [LWX, Notation 2.1] (`(1+T)^s`), §2.3 ("χ m-locally analytic … so that (2.3.2) is well defined").

### [CL-B4] /cleanup Binomial.lean — final (after B10)
- **Status**: done (inline cleanup 2026-09-05T16:05Z: header, omits, runLinter clean) | **File**: PhD/LWX/Binomial.lean | **Depends on**: B10 — inline.

---

## Tranche M — `PhD/LWX/Colmez.lean` (Mahler coordinates of monomials; the Colmez basis)

`open scoped fwdDiff` gives `Δ_[h]`; `mahlerCoeffPow m k := Δ_[1]^[m] (fun n : ℤ => n ^ k) 0`.

### [M1] `mahlerCoeffPow_eq_zero_of_lt`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:58 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem mahlerCoeffPow_eq_zero_of_lt {m k : ℕ} (h : k < m) : mahlerCoeffPow m k = 0
```
#### Proof sketch
`unfold mahlerCoeffPow`; `rw [fwdDiff_iter_pow_eq_zero_of_lt h]` (mathlib ForwardDiff.lean:237,
`Δ_[1]^[n] (fun r : R => r^j) = 0` for `j < n`, `R = ℤ`); `Pi.zero_apply`.
#### Sources
[LWX, §2.16 (2.16.1)]; mathlib ForwardDiff.lean:237.

### [M2] `mahlerCoeffPow_self`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:62 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem mahlerCoeffPow_self (k : ℕ) : mahlerCoeffPow k k = (k ! : ℤ)
```
#### Proof sketch
`fwdDiff_iter_eq_factorial` (ForwardDiff.lean:252: `Δ_[1]^[n] (fun r : R => r^n) = n !` as a
constant function); evaluate at `0`.
#### Sources
mathlib ForwardDiff.lean:252.

### [M3] Newton's formula on `ℕ`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:69 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem natCast_pow_eq_sum_choose_mul_mahlerCoeffPow (n k : ℕ) :
    (n : ℤ) ^ k = ∑ m ∈ Finset.range (k + 1), (n.choose m : ℤ) * mahlerCoeffPow m k
```
#### Proof sketch
`shift_eq_sum_fwdDiff_iter (f := fun x : ℤ => x ^ k) n 0` (ForwardDiff.lean:175):
`f (0 + n • 1) = ∑ m ∈ range (n+1), n.choose m • Δ_[1]^[m] f 0`; `zero_add`, `nsmul_eq_mul`,
`smul_eq_mul`.  The range is `n + 1`, not `k + 1`: split by `Finset.sum_subset`/`Finset.sum_range_add`
using M1 (`Δ^m = 0` for `m > k`) and `Nat.choose_eq_zero_of_lt` (for `m > n`) to move to
`range (k+1)` in both directions.
#### Sources
mathlib ForwardDiff.lean:175 (`shift_eq_sum_fwdDiff_iter`).

### [CL-M1] /cleanup Colmez.lean (after M3)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M3 — inline.

### [M4] Forward differences of `descPochhammer` at `0`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:77 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem fwdDiff_iter_descPochhammer_eval_zero (j m : ℕ) :
    Δ_[1]^[j] (fun n : ℤ => (descPochhammer ℤ m).eval n) 0
      = if j = m then (m ! : ℤ) else 0
```
#### Proof sketch
Both sides via `fwdDiff_iter_eq_sum_shift` (ForwardDiff.lean:147): `Δ^j f 0 = ∑_{i ≤ j} ((-1)^(j−i) * C(j,i)) • f (0 + i • 1)`;
for `f = eval (descPochhammer ℤ m)` at `(i : ℤ)`: `descPochhammer_eval_eq_descFactorial ℤ i m`
(`= i.descFactorial m`) and `Nat.descFactorial_eq_factorial_mul_choose : i.descFactorial m = m! * i.choose m`.
So `Δ^j f 0 = m! * Δ_[1]^[j] (fun i : ℕ => (i.choose m : ℤ)) 0` (the same finite sum, domain `ℕ`),
and `fwdDiff_iter_choose_zero j m` (ForwardDiff.lean:197) gives `if j = m then 1 else 0`.
#### Sources
[LWX, §2.16]; mathlib ForwardDiff.lean:147, :197; Pochhammer.lean.

### [M5] Forward differences commute with additive maps
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:84 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem map_fwdDiff_iter {M N A : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommMonoid A] (e : M →+ N) (f : A → M) (h : A) (m : ℕ) (y : A) :
    Δ_[h]^[m] (fun a => e (f a)) y = e (Δ_[h]^[m] f y)
```
#### Proof sketch
`rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]`; `Finset.sum_congr rfl`;
`map_zsmul`.  (This is IntegralModel.lean's private `addMonoidHom_fwdDiff_iter`, generalised.)
#### Sources
IntegralModel.lean:1131 (private); mathlib ForwardDiff.lean:147.

### [M6] Newton's formula on `ℤ_p`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:97 | **Depends on**: M3
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem pow_eq_sum_choose_mul_mahlerCoeffPow (z : ℤ_[p]) (k : ℕ) :
    z ^ k = ∑ m ∈ Finset.range (k + 1), Ring.choose z m * (mahlerCoeffPow m k : ℤ_[p])
```
#### Proof sketch
Both sides are continuous in `z` (LHS `continuous_pow`; RHS `continuous_finset_sum` of
`(PadicInt.mahler m).continuous.mul continuous_const` — `Ring.choose z m = PadicInt.mahler m z`,
mathlib MahlerBasis.lean `mahler_apply`); `PadicInt.denseRange_natCast.equalizer`
(`DenseRange.equalizer` with `Continuous` hypotheses) reduces to `z = (n : ℤ_[p])`, where
`Ring.choose (n : ℤ_[p]) m = n.choose m` (`Ring.choose_natCast`) and M3 cast along `Int.cast : ℤ → ℤ_[p]`
(`push_cast`; `Int.cast_sum`, `Int.cast_mul`).
#### Sources
[LWX, §2.16 (2.16.1)]; mathlib `PadicInt.denseRange_natCast` (RingHoms.lean:501).

### [CL-M2] /cleanup Colmez.lean (after M6)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M6 — inline.

### [M7] `colmezToMonomial`: bounds, column decay, matrix
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:108–113 | **Depends on**: none
- **Parallel**: yes | **Type**: def obligations (2) + lemma `matrixCoeff_colmezToMonomial`
#### Statement
```lean
def colmezToMonomial : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun k m => (((descPochhammer ℤ m).coeff k : ℤ) : K)) ⟨1, by sorry⟩ (by sorry)
theorem matrixCoeff_colmezToMonomial (k m : ℕ) :
    matrixCoeff (colmezToMonomial K) k m = (((descPochhammer ℤ m).coeff k : ℤ) : K)
```
#### Proof sketch
Bound: `‖((z : ℤ) : K)‖ ≤ 1` (`IsUltrametricDist.norm_intCast_le_one`; if absent, `Int.cast` =
`± Nat.cast` and `IsUltrametricDist.norm_natCast_le_one` + `norm_neg`).  Column decay: for fixed
`m`, `coeff k = 0` for `k > m` (`Polynomial.coeff_eq_zero_of_natDegree_lt`, `descPochhammer_natDegree ℤ m = m`),
so `Tendsto … cofinite (𝓝 0)` via `tendsto_nhds_of_eventually_eq`/`Filter.eventually_cofinite` with
the finite set `range (m+1)`.  Matrix: `matrixCoeff_ofCoeffs` (GenFun.lean:191).
#### Sources
[LWX, §2.16] / [Colmez, Thm 1.29]; GenFun.lean:178–195.

### [M8] **The Colmez basis is orthonormal**: `colmezToMonomial` is an isometry
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:120 | **Depends on**: M7
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem norm_colmezToMonomial (a : c(ℕ, K)) : ‖colmezToMonomial K a‖ = ‖a‖
```
#### Proof sketch
`≤`: `cSpace.norm_eq_iSup`, each coordinate `(Ψ⁻¹ a) k = ∑' m, coeff_k(descPoch_m) * a m`
(`ofCoeffs_apply`) has norm `≤ sup_m ‖a m‖ = ‖a‖` (`TateFredholm.norm_tsum_le_iSup`, integer
coefficients).  `≥`: if `a = 0` trivial; else `‖a‖ > 0` and the set `{n | ‖a n‖ = ‖a‖}` is nonempty
(the sup of a cofinitely-null family is attained: `{n | ‖a n‖ ≥ ‖a‖/2}` is finite by
`cSpace.tendsto_cofinite`, so the sup over it is a max — or use `TateFredholm`'s existing "norm
attained" lemma if present: grep `exists_norm_apply_eq`/`norm_eq_iSup` users) and finite, so has a
largest element `n₀` (`Finset.max'`).  Then `(Ψ⁻¹ a) n₀ = a n₀ + ∑'_{m > n₀} coeff_{n₀}(descPoch_m) a m`
(`coeff_{n₀}(descPoch_{n₀}) = 1`: `monic_descPochhammer` + `descPochhammer_natDegree`; terms with
`m < n₀` vanish), and the tail has norm `< ‖a‖` (each `‖a m‖ < ‖a‖` for `m > n₀`, ultrametric sup),
so `‖(Ψ⁻¹ a) n₀‖ = ‖a n₀‖ = ‖a‖` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), hence
`‖Ψ⁻¹ a‖ ≥ ‖a‖` (`cSpace.norm_apply_le`).
#### Sources
[Colmez, Thm 1.29] at `m = 1` ([LWX, §2.16 lwx.txt:947–953]); ModelSpace.lean:53–57.

### [M9] The monomials lie in the range
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:126 | **Depends on**: M7
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem single_mem_range_colmezToMonomial (k : ℕ) :
    cSpace.single k (1 : K) ∈ LinearMap.range (colmezToMonomial K).toLinearMap
```
#### Proof sketch
Strong induction on `k`.  `Ψ⁻¹ (single k 1)` is the coefficient sequence of `descPochhammer ℤ k`
mapped to `K` (`ofCoeffs_apply` + `tsum_eq_single`), i.e. `single k 1 + ∑_{m < k} c_m • single m 1`
with `c_m = coeff_m(descPoch_k)` (monic, degree `k`).  So `single k 1 = Ψ⁻¹ (single k 1) − ∑_{m<k} c_m • single m 1`,
and each `single m 1` (`m < k`) is in the range by induction; `Submodule.sub_mem`, `Submodule.sum_mem`,
`Submodule.smul_mem`.  Express "coefficient sequence" via `cSpace` ext (`DFunLike.ext`) and
`cSpace.single_apply_*`.
#### Sources
[Colmez, Thm 1.29]; mathlib `monic_descPochhammer`, `descPochhammer_natDegree`.

### [CL-M3] /cleanup Colmez.lean (after M9)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M9 — inline.

### [M10] Surjectivity of `colmezToMonomial`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:131 | **Depends on**: M8, M9
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem surjective_colmezToMonomial : Function.Surjective (colmezToMonomial K)
```
#### Proof sketch
The range `R := LinearMap.range …` is closed: an isometry has closed range (`Isometry.isClosedEmbedding`
via `AddMonoidHomClass.isometry_of_norm` + `IsClosedEmbedding.isClosed_range`).  It is dense:
every `f` is `∑' i, f i • single i 1` (`cSpace.hasSum_single`), whose partial sums lie in `R`
(M9), so `f ∈ closure R` (`HasSum` gives `Tendsto` of partial sums; `mem_closure_of_tendsto`).
Hence `R = ⊤` (`IsClosed.closure_eq`, `Dense.closure_eq`), i.e. surjective (`LinearMap.range_eq_top`).
#### Sources
Standard.

### [M11] `colmezEquiv`: bijectivity and continuity of the inverse
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:137–143 | **Depends on**: M8, M10
- **Parallel**: no | **Type**: def obligations (2) + `coe_colmezEquiv`
#### Statement
```lean
def colmezEquiv : c(ℕ, K) ≃L[K] c(ℕ, K) :=
  { LinearEquiv.ofBijective (colmezToMonomial K).toLinearMap (by sorry) with
    continuous_toFun := (colmezToMonomial K).continuous
    continuous_invFun := by sorry }
@[simp] theorem coe_colmezEquiv :
    (colmezEquiv K : c(ℕ, K) →L[K] c(ℕ, K)) = colmezToMonomial K
```
#### Proof sketch
Bijective: injective from the isometry (`‖Ψ⁻¹ a‖ = ‖a‖`, `norm_eq_zero`), surjective M10.
`continuous_invFun`: the inverse `g` of the `LinearEquiv` is a linear map with `‖g b‖ = ‖b‖`
(`b = Ψ⁻¹ (g b)`, M8), so `LinearMap.continuous_of_bound g 1`.  `coe_colmezEquiv`: `rfl`
(`ContinuousLinearEquiv.coe_mk`/`ext`).
#### Sources
Standard.

### [M12] `monomialToMahler`: bounds, column decay, matrix
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:148–153 | **Depends on**: none
- **Parallel**: yes | **Type**: def obligations (2) + lemma
#### Statement
```lean
def monomialToMahler : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m k => (mahlerCoeffPow m k : K)) ⟨1, by sorry⟩ (by sorry)
theorem matrixCoeff_monomialToMahler (m k : ℕ) :
    matrixCoeff (monomialToMahler K) m k = (mahlerCoeffPow m k : K)
```
#### Proof sketch
Bound: integer cast (as M7).  Column decay: `mahlerCoeffPow m k = 0` for `m > k` (M1), finite
support in `m`.  Matrix: `matrixCoeff_ofCoeffs`.
#### Sources
GenFun.lean:178–195.

### [CL-M4] /cleanup Colmez.lean (after M12)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M12 — inline.

### [M13] `diagFactorial`: bounds, column decay, matrix
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:158–163 | **Depends on**: none
- **Parallel**: yes | **Type**: def obligations (2) + lemma
#### Statement
```lean
def diagFactorial : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m k => if m = k then ((m ! : ℕ) : K) else 0) ⟨1, by sorry⟩ (by sorry)
theorem matrixCoeff_diagFactorial (m k : ℕ) :
    matrixCoeff (diagFactorial K) m k = if m = k then ((m ! : ℕ) : K) else 0
```
#### Proof sketch
`‖(m! : K)‖ ≤ 1` (`IsUltrametricDist.norm_natCast_le_one`); columns have one nonzero entry;
`matrixCoeff_ofCoeffs`.
#### Sources
[LWX, Prop 2.17 proof] ("infinite diagonal matrix with diagonal entries … ⌊n/(q⁻¹pᵐ)⌋!").

### [M14] `monomialToMahler ∘ colmezToMonomial = diagFactorial`
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:170 | **Depends on**: M4, M7, M12, M13
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem monomialToMahler_comp_colmezToMonomial :
    (monomialToMahler K).comp (colmezToMonomial K) = diagFactorial K
```
#### Proof sketch
`ext_matrixCoeff` (Matrix.lean:66); `matrixCoeff_comp` (:84):
`∑' k, matrixCoeff Ψ⁻¹ k m * matrixCoeff Φ j k = ∑' k, (coeff_k descPoch_m : K) * (mahlerCoeffPow j k : K)`;
finite (`k ≤ m`), `tsum_eq_sum`; this is `Int.cast` of `∑_{k ≤ m} coeff_k(descPoch_m) * Δ^j(nᵏ)(0)`
`= Δ^j (fun n => ∑_k coeff_k n^k) 0 = Δ^j (eval (descPoch_m)) 0` (`Polynomial.eval_eq_sum_range`
with `natDegree = m`; linearity of `Δ^j` over finite sums: `fwdDiff_iter_eq_sum_shift` + `Finset.sum_comm`,
or `map_fwdDiff_iter`-style with `fwdDiffₗ`) `= if j = m then m! else 0` (M4) `= matrixCoeff_diagFactorial`
(`Nat.cast` vs `Int.cast` of `m!`: `Int.cast_natCast`).
#### Sources
[LWX, Prop 2.17 proof].

### [M15] **`monomialToMahler = diagFactorial ∘ colmezEquiv.symm`**
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:177 | **Depends on**: M11, M13, M14
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem monomialToMahler_eq :
    monomialToMahler K = (diagFactorial K).comp ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K))
```
#### Proof sketch
From M14 compose on the right with `(colmezEquiv K).symm`: `Φ ∘ Ψ⁻¹ ∘ Ψ = Δ ∘ Ψ` and
`Ψ⁻¹ ∘ Ψ = id` (`ContinuousLinearEquiv.self_comp_symm`/`coe_colmezEquiv`); `ContinuousLinearMap.comp_assoc`,
`comp_id`.
#### Sources
[LWX, Prop 2.17 proof].

### [CL-M5] /cleanup Colmez.lean (after M15)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M15 — inline.

### [M16] Mahler coordinates of an evaluated series at `ℕ`-points
- **Status**: done (finished 2026-09-05 15:26) | **File**: PhD/LWX/Colmez.lean:185 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem fwdDiff_iter_evalAt_natCast {F : PowerSeries K} (hF : QMF.TendstoCoeff F) (m : ℕ) :
    Δ_[1]^[m] (fun n : ℕ => QMF.evalAt F (n : K)) 0
      = ∑' k, PowerSeries.coeff k F * (mahlerCoeffPow m k : K)
```
#### Proof sketch
`fwdDiff_iter_eq_sum_shift`: LHS `= ∑_{i ≤ m} ((-1)^(m−i) * C(m,i)) • evalAt F (i : K)`, and
`evalAt F i = ∑' k, coeff k F * i^k` (`hF.hasSum_evalAt (norm_natCast_le_one)`, Char.lean:128).
Swap: `∑_i c_i • ∑' k, … = ∑' k, coeff k F * ∑_i c_i • (i:K)^k` (`tsum_finset_sum`/`HasSum.sum`,
`tsum_mul_left`), and `∑_i c_i • (i : K)^k = ((Δ_[1]^[m] (fun n : ℤ => n^k) 0 : ℤ) : K)`
(`fwdDiff_iter_eq_sum_shift` again on `ℤ`, cast along `Int.castRingHom K`: `Int.cast_sum`,
`Int.cast_mul`, `Int.cast_pow`, `zsmul_eq_mul`).
#### Sources
[LWX, §2.16 (2.16.1)]; Char.lean:110–130 (`TendstoCoeff`, `hasSum_evalAt`).

### [CL-M6] /cleanup Colmez.lean — final (after M16)
- **Status**: done (inline cleanup 2026-09-05 15:26: show→change, narrative comments stripped, β-bound extracted as exists_lt_norm_forall_norm_apply_le, docstrings, header) | **File**: PhD/LWX/Colmez.lean | **Depends on**: M16 — inline.

---

## Tranche W — `PhD/LWX/HaloWeight.lean` (the halo weight as an `AnalyticWeight`)

### [W1] The norm dictionary (`norm_intHom`, `norm_natCast_p`, `norm_lt_one_of_sq_lt`)
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:62, :67, :71 | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas (3, each ≤ 5 lines)
#### Statement
```lean
theorem norm_intHom (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : ℤ_[p]) :
    ‖intHom ψ x‖ = ‖x‖
theorem norm_natCast_p (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹
theorem norm_lt_one_of_sq_lt {T₀ : K} (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : ‖T₀‖ < 1
```
#### Proof sketch
`intHom_apply`, `hψ`, `PadicInt.norm_def` (`‖(x : ℚ_[p])‖ = ‖x‖`).  `(p : K) = ψ (p : ℚ_[p])`
(`map_natCast`), `hψ`, `padicNormE.norm_p`.  `‖T₀‖² < p⁻¹ ≤ 1` ⇒ `‖T₀‖ < 1` (`pow_lt_one_iff`/`nlinarith`).
#### Sources
—

### [W2] `isUnit_natCast_val`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:77 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem isUnit_natCast_val (r : (ZMod p)ˣ) : IsUnit ((((r : ZMod p).val : ℕ)) : ℤ_[p])
```
#### Proof sketch
`PadicInt.isUnit_iff : IsUnit x ↔ ‖x‖ = 1`; `PadicInt.norm_eq_one_iff`/`PadicInt.toZMod`-based:
`toZMod ((r.val : ℕ) : ℤ_[p]) = ((r.val : ℕ) : ZMod p) = r ≠ 0` (`map_natCast`, `ZMod.natCast_zmod_val`,
`Units.ne_zero`), and `PadicInt.norm_lt_one_iff_dvd`/`PadicInt.toZMod_eq_zero_iff`-type lemma
(`x ∈ ker toZMod ↔ ‖x‖ < 1`: `PadicInt.ker_toZMod`, `PadicInt.mem_nonunits`).
#### Sources
mathlib PadicIntegers/RingHoms.

### [W3] `toZMod_teichRes`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:85 | **Depends on**: W2
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem toZMod_teichRes (r : (ZMod p)ˣ) :
    Units.map (PadicInt.toZMod (p := p)).toMonoidHom (teichRes r) = r
```
#### Proof sketch
`teichmuller x ≡ x mod p` (`norm_mul_teichmuller_inv_sub_one_le`, UnitsLog.lean:134, or the
underlying `norm_teichAux_sub_self_le`): so `toZMod (teichmuller u) = toZMod u`
(`PadicInt.toZMod` kills `‖·‖ ≤ p⁻¹`, `PadicInt.ker_toZMod`); with `u = (r.val : ℤ_p)`,
`toZMod u = r` (`map_natCast`, `ZMod.natCast_zmod_val`).  `Units.ext`.
#### Sources
UnitsLog.lean:134.

### [CL-W1] /cleanup HaloWeight.lean (after W3)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W3 — inline.

### [W4] `teichRes_toZMod`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:94 | **Depends on**: W3
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem teichRes_toZMod (a : ℤ_[p]ˣ) :
    teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) = teichmuller a
```
#### Proof sketch
`teichmuller_eq_of_norm_sub_le` (UnitsLog.lean:157): the lift `((toZMod a).val : ℤ_p)` and `a` have
the same residue, so `‖lift − a‖ ≤ p⁻¹` (`PadicInt.norm_le_pow_iff_mem_span_pow`/`ker_toZMod` at
`toZMod (lift − a) = 0`).
#### Sources
UnitsLog.lean:157.

### [W5] `norm_sub_teichRes_le`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:100 | **Depends on**: W4
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem norm_sub_teichRes_le (a : ℤ_[p]ˣ) :
    ‖(a : ℤ_[p]) - (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖
      ≤ (p : ℝ)⁻¹
```
#### Proof sketch
`rw [teichRes_toZMod]`; from `norm_mul_teichmuller_inv_sub_one_le a` (UnitsLog.lean:134):
`a − τ = (a τ⁻¹ − 1) τ` with `‖τ‖ = 1`.
#### Sources
UnitsLog.lean:134.

### [W6] `teichRes_mul`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:89 | **Depends on**: W3, W4
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem teichRes_mul (r r' : (ZMod p)ˣ) : teichRes (r * r') = teichRes r * teichRes r'
```
#### Proof sketch
`teichRes r * teichRes r' = teichmuller (teichRes r * teichRes r')` (Teichmüller is idempotent:
`teichmuller (teichmuller x) = teichmuller x` — derive from `teichmuller_eq_of_norm_sub_le` and
`‖x − τx‖ ≤ p⁻¹`... simpler: `teichmuller_mul` gives `teichmuller (u u') = teichmuller u * teichmuller u'`
with `u, u'` the lifts; and `teichRes (r r') = teichmuller (lift (r r'))` where `lift (r r')` and
`u u'` have the same residue, so `teichmuller_eq_of_norm_sub_le` (via `toZMod`-equality ⇒ `‖·‖ ≤ p⁻¹`)
identifies them.  Use W3 for residues.
#### Sources
UnitsLog.lean:105, :157.

### [CL-W2] /cleanup HaloWeight.lean (after W6)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W6 — inline.

### [W7] `teichRes_injective`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:104 | **Depends on**: W3
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem teichRes_injective : Function.Injective (teichRes (p := p))
```
#### Proof sketch
`Function.Injective` via left inverse: `Units.map toZMod ∘ teichRes = id` (W3),
`Function.LeftInverse.injective`.
#### Sources
—

### [W8] `haloUnits` is a subgroup
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:119–121 | **Depends on**: none
- **Parallel**: yes | **Type**: def obligations (3)
#### Statement
```lean
def haloUnits : Subgroup Kˣ where
  carrier := {x | ∃ a : ℤ_[p]ˣ, ‖ψ ((a : ℤ_[p]) : ℚ_[p])‖ = 1 ∧
    ‖(x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry
```
#### Proof sketch
(The carrier carries `‖ψ a‖ = 1` so that no hypothesis on `ψ` is needed; for isometric `ψ` it is
automatic — W9/W19 supply it from `hψ`.)  `one_mem'`: `a = 1`, `map_one`, `norm_one`, `sub_self`.
`mul_mem'`: witnesses `a, b` give `ab` (`map_mul`, `norm_mul`); `‖x‖ = 1` from `‖x − ψa‖ ≤ p⁻¹ < 1 = ‖ψa‖`
(`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` on `x = (x − ψa) + ψa`, `p⁻¹ < 1`);
`xy − ψ(ab) = x (y − ψb) + (x − ψa) ψb`, both terms of norm `≤ p⁻¹`, ultrametric `norm_add_le_max`.
`inv_mem'`: witness `a⁻¹` (`map_units_inv`, `norm_inv`); `x⁻¹ − (ψa)⁻¹ = x⁻¹ (ψa − x) (ψa)⁻¹`
(`Units.val_inv_eq_inv_val`, `field_simp`), norms `1 · ‖x − ψa‖ · 1` (`norm_sub_rev`).
#### Sources
[LWX, §2.3]; `QMF.oneUnits` (Char.lean:516) for the pattern.

### [W9] `exists_unique_teichRes_of_mem_haloUnits`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:132 | **Depends on**: W5, W7, W8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem exists_unique_teichRes_of_mem_haloUnits (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : Kˣ}
    (hx : x ∈ haloUnits ψ) :
    ∃! r : (ZMod p)ˣ, ‖(x : K) - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹
```
#### Proof sketch
Existence: `a` from `hx` (its `‖ψ a‖ = 1` clause is unused), `r := Units.map toZMod a`;
`‖x − ψ(τ r)‖ ≤ max (‖x − ψ a‖) (‖ψ (a − τ r)‖)` with W5 and `norm_intHom`.  Uniqueness: `‖ψ(τ r) − ψ(τ r')‖ ≤ p⁻¹` ⇒ `‖τ r − τ r'‖ ≤ p⁻¹` (W1) ⇒
`teichmuller (τ r) = teichmuller (τ r')` (`teichmuller_eq_of_norm_sub_le`) and `teichmuller (τ r) = τ r`
(idempotence, as in W6) ⇒ `τ r = τ r'` ⇒ `r = r'` (W7).
#### Sources
UnitsLog.lean:157.

### [CL-W3] /cleanup HaloWeight.lean (after W9)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W9 — inline.

### [W10] `norm_haloExponent`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:146 | **Depends on**: W1
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_haloExponent (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    ‖haloExponent (p := p) T₀‖ = p * ‖T₀‖
```
#### Proof sketch
`norm_div`, `norm_natCast_p` (W1), `norm_padicLog_eq h3 hp2 (hu : ‖(1 + T₀) − 1‖^2 < ‖p‖)`
(PadicExpLog.lean:753; `h3 : ‖(p:K)‖ < 1` from W1), `add_sub_cancel_left`, `div_inv_eq_mul`.
#### Sources
PadicExpLog.lean:753.

### [W11] `haloCharFun_of_norm_sub_le`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:166 | **Depends on**: W7
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem haloCharFun_of_norm_sub_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : K} {r : (ZMod p)ˣ}
    (h : ‖x - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹) :
    haloCharFun ψ T₀ ω x
      = intHom ψ (ω r : ℤ_[p])
        * PadicExpLog.padicExp (haloExponent (p := p) T₀
            * PadicExpLog.padicLog (x * (intHom ψ (teichRes r : ℤ_[p]))⁻¹))
```
#### Proof sketch
`unfold haloCharFun`; `Finset.sum_eq_single r`: for `r' ≠ r`, the condition fails — if
`‖x − ψτr'‖ ≤ p⁻¹` too then `‖ψτr − ψτr'‖ ≤ p⁻¹`, contradicting distinct residues (as in W9's
uniqueness; factor that argument into a private lemma `teichRes_eq_of_norm_sub_le` used by W9 and
W11); `if_pos h`.
#### Sources
—

### [W12] `haloCharFun_one`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:170 | **Depends on**: W11
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem haloCharFun_one (hψ : ∀ x, ‖ψ x‖ = ‖x‖) : haloCharFun ψ T₀ ω 1 = 1
```
#### Proof sketch
W11 at `r = 1`: `teichRes 1 = 1` (W3 + `teichmuller 1 = 1`, or `teichRes_mul` + cancellation),
`‖1 − ψ 1‖ = 0 ≤ p⁻¹`; then `map_one`, `inv_one`, `mul_one`, `padicLog 1 = 0` (series of `(1−1)^{n+1} = 0`;
`PadicExpLog.padicLog` def :169 — add a private `padicLog_one` if absent), `mul_zero`, `padicExp 0 = 1`
(`padicExp` def :174, `tsum_eq_single 0`), `mul_one`.
#### Sources
—

### [CL-W4] /cleanup HaloWeight.lean (after W12)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W12 — inline.

### [W13] **Multiplicativity of `χ` on the halo units**
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:177 | **Depends on**: W6, W9, W10, W11
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem haloCharFun_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {x y : Kˣ} (hx : x ∈ haloUnits ψ) (hy : y ∈ haloUnits ψ) :
    haloCharFun ψ T₀ ω ((x * y : Kˣ) : K) = haloCharFun ψ T₀ ω x * haloCharFun ψ T₀ ω y
```
#### Proof sketch
Residues `r, r'` for `x, y` (W9); `xy` has residue `r r'`: `‖xy − ψτ(rr')‖ ≤ p⁻¹` (W6, `‖x‖ = ‖ψτr'‖ = 1`,
ultrametric as in W8).  Rewrite all three by W11.  `ω (r r') = ω r * ω r'` (`map_mul`).  Exponent:
`u := x (ψτr)⁻¹`, `v := y (ψτr')⁻¹` are `1`-units with `‖u − 1‖ ≤ p⁻¹`, so `‖u − 1‖^2 < ‖p‖`
(`p⁻² < p⁻¹`, W1); `xy (ψτ(rr'))⁻¹ = u v` (W6, `map_mul`, `mul_inv`); `padicLog_mul h3 hp2 hu hv`
(PadicExpLog.lean:848); `mul_add`; `padicExp_add h3 hp2 ha hb` (:410) with `‖s·padicLog u‖² < ‖p‖`:
`‖s‖ = p‖T₀‖` (W10), `‖padicLog u‖ = ‖u − 1‖ ≤ p⁻¹` (`norm_padicLog_eq`), product `≤ ‖T₀‖`, squared `< p⁻¹` (h1).
Then `ring`.
#### Sources
PadicExpLog.lean:410, :753, :848; [LWX, Notation 2.1] (multiplicativity of `[−]`).

### [W14] `norm_haloCharFun`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:183 | **Depends on**: W10, W11
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem norm_haloCharFun (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : Kˣ} (hx : x ∈ haloUnits ψ) :
    ‖haloCharFun ψ T₀ ω x‖ = 1
```
#### Proof sketch
W9 → W11; `‖ψ(ω r)‖ = ‖ω r‖ = 1` (units of `ℤ_p`, `PadicInt.norm_units`? or `PadicInt.isUnit_iff`);
`‖padicExp w‖ = 1` for `‖w‖² < ‖p‖`: from `norm_padicExp_sub_one_le` (PadicExpLog.lean:361,
`‖exp w − 1‖ ≤ ‖w‖ < 1`) and `norm_eq_one_of_norm_sub_one_lt_one` (:192).
#### Sources
PadicExpLog.lean:192, :361.

### [W15] **`χ ∘ ψ = spec ∘ [−]` on `ℤ_p^×`**
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:191 | **Depends on**: S9, B10, W4, W5, W11
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem haloCharFun_psi (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    haloCharFun ψ T₀ ω (intHom ψ (a : ℤ_[p])) = HaloInt.specialize (intHom ψ) T₀ (univChar ω a)
```
#### Proof sketch
RHS: `specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0 (norm_lt_one_of_sq_lt h1) ω a`
`= ψ(ω ā) * oneAddPow T₀ (ψ (logQuot a))`, and `oneAddPow T₀ u = ∑' r, C(u,r) T₀^r = padicExp (u * padicLog (1+T₀))`
by B10 (`hasSum_choose_mul_pow h3 hp2 (c := ‖T₀‖) (hc : ‖T₀‖^2 < ‖p‖ = p⁻¹) (hx : ‖T₀‖ ≤ ‖T₀‖) (hex : ‖u‖ * ‖T₀‖ ≤ ‖T₀‖)`
with `‖u‖ ≤ 1`, `u = ψ (logQuot a)`, `PadicInt.norm_le_one`).  LHS: W11 with `r := Units.map toZMod a`
(`‖ψa − ψ τr‖ ≤ p⁻¹` by W5 + `norm_intHom`): `ψ(ω r) * padicExp (s * padicLog (ψ a * (ψ τ r)⁻¹))`.
Match exponents: `ψ a (ψ τr)⁻¹ = ψ (oneUnitPart a)` (W4, `oneUnitPart` def UnitsLog.lean:193,
`map_units_inv`), and `ψ (logQuot a) = padicLog (ψ ⟨a⟩) / p`: `coe_logQuot` (`logQuot a = qlog ⟨a⟩ / p` in `ℚ_p`),
`qlog u = padicLog (u : ℚ_p)` (UnitsLog.lean:203), and `ψ (padicLog y) = padicLog (ψ y)`
(`padicLog` is a `tsum` of `(y−1)^{n+1}/(n+1)` — `map_tsum` for the continuous ring hom `ψ`,
`ψ` continuous from `hψ`; `map_div₀`, `map_pow`, `map_natCast`).  Then
`u * padicLog (1+T₀) = s * padicLog (ψ⟨a⟩)` by `ring` (`haloExponent` def, `div_mul_eq_mul_div`).
#### Sources
[LWX, Notation 2.1]: "each continuous ring homomorphism χ : Λ→ Cp defines a continuous character
χ◦ [−]"; UnitsLog.lean:193–210; IntegralModel.lean:147–162.

### [CL-W5] /cleanup HaloWeight.lean (after W15)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W15 — inline.

### [W16] `haloChar` is a monoid hom; `coe_haloChar_apply`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:197–204 | **Depends on**: W12, W13, W14
- **Parallel**: no | **Type**: def obligations (3) + lemma
#### Statement
```lean
def haloChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloUnits ψ →* Kˣ where
  toFun x := Units.mk0 (((x : Kˣ) : K) ^ 2 * haloCharFun ψ T₀ ω ((x : Kˣ) : K)) (by sorry)
  map_one' := by sorry
  map_mul' := by sorry
theorem coe_haloChar_apply … : (haloChar ψ T₀ ω hp2 hψ h0 h1 x : K)
    = ((x : Kˣ) : K) ^ 2 * haloCharFun ψ T₀ ω ((x : Kˣ) : K)
```
#### Proof sketch
Nonzero: `pow_ne_zero` (`Units.ne_zero`) and `norm_haloCharFun … = 1 ≠ 0` (W14).  `map_one'`:
`Units.ext`, `Units.val_mk0`, `one_pow`, W12.  `map_mul'`: `Units.ext`, `Units.val_mul`, `mul_pow`,
W13, `ring`.  `coe_haloChar_apply`: `rfl`/`Units.val_mk0`.
#### Sources
[Jacobs, Def 1.27] normalisation (`κ(cz+d)/(cz+d)²`); README §3 (`algWeight n : κ(u) = u^{n+2}`).

### [W17] `haloRho` lemmas (`haloRho_nonneg`, `haloRho_lt_one`, `inv_le_haloRho`)
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:224, :227, :230 | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas (3)
#### Statement
```lean
theorem haloRho_nonneg : 0 ≤ haloRho (p := p) T₀
theorem haloRho_lt_one (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloRho (p := p) T₀ < 1
theorem inv_le_haloRho (h0 : (p : ℝ)⁻¹ < ‖T₀‖) : (p : ℝ)⁻¹ ≤ haloRho (p := p) T₀
```
#### Proof sketch
`mul_nonneg`, `Real.sqrt_nonneg`.  `ρ < 1 ⇔ ρ² < 1` (`ρ ≥ 0`): `ρ² = ‖T₀‖² p < p⁻¹ p = 1`
(`mul_pow`, `Real.sq_sqrt`, `pow_lt_one_iff_of_nonneg`).  `p⁻¹ ≤ ‖T₀‖ √p`: `p⁻¹ < ‖T₀‖ ≤ ‖T₀‖ √p`
since `√p ≥ 1` (`Real.one_le_sqrt`, `p ≥ 2`).
#### Sources
—

### [W18] `levelBounds_M1K`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:236 | **Depends on**: W1, W17
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem levelBounds_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : LevelBounds (M1K ψ) (haloRho (p := p) T₀)
```
#### Proof sketch
Fields (Series.lean:97): `rho_nonneg`, `rho_lt_one` (W17); for `g ∈ M1K ψ` obtain `δ ∈ M1 p`
with `g = mapMatrix ψ δ` (`mem_M1K_iff`); `integral`: `(mapMatrix ψ δ) i j = ψ (δ i j)`
(`RingHom.mapMatrix_apply`, `Matrix.map_apply`), `hψ`, `δ.2.1 i j`; `c_le`: `‖ψ (δ 1 0)‖ = ‖δ 1 0‖ ≤ p⁻¹ ≤ ρ`
(`δ.2.2.1`, W17); `d_unit`: `δ.2.2.2.1`.
#### Sources
IntegralModel.lean:226 (`M1`), Series.lean:97 (`LevelBounds`).

### [CL-W6] /cleanup HaloWeight.lean (after W18)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W18 — inline.

### [W19] `mem_haloUnits_of_mem_M1K`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:242 | **Depends on**: W1, W8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem mem_haloUnits_of_mem_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1K ψ) {z : K} (hz : ‖z‖ ≤ 1) (hu : IsUnit (g 1 0 * z + g 1 1)) :
    hu.unit ∈ haloUnits ψ
```
#### Proof sketch
`g = mapMatrix ψ δ`, `d := δ 1 1` with `‖d‖ = 1` so `d = (u : ℤ_p)` for a unit `u`
(`PadicInt.isUnit_iff`, `IsUnit.unit`; `δ 1 1 ∈ ℤ_p` via `‖·‖ ≤ 1`: `PadicInt` subtype `⟨δ 1 1, _⟩`).
Witness `a := u` (`‖ψ u‖ = 1` by `hψ`): `‖(cz + d) − ψ d‖ = ‖c z‖ ≤ ‖c‖ ≤ p⁻¹`.  `IsUnit.unit_spec`.
#### Sources
[LWX, §2.3]; Char.lean:554 (`levelUnit_mem_oneUnits`) for the pattern.

### [W20] **Row decay of the halo column**
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:263 | **Depends on**: W10, W14, W17, W18
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem norm_coeff_haloCol_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) (m : ℕ) :
    ‖PowerSeries.coeff m (haloCol ψ T₀ ω (g 1 0) (g 1 1))‖ ≤ haloRho (p := p) T₀ ^ m
```
#### Proof sketch
Let `c = g 1 0`, `d = g 1 1` (`‖c‖ ≤ p⁻¹`, `‖d‖ = 1`), `w = c/d` (`‖w‖ ≤ p⁻¹`), `a_m := C(s,m) w^m`.
(1) `‖a_m‖ ≤ ρ^m`: for `m ≥ 1`, `‖C(s,m)‖ ≤ ‖s‖^m ‖m!‖⁻¹` (as B1, all `‖s − k‖ ≤ ‖s‖` since `‖s‖ = p‖T₀‖ > 1`
by W10, `h0`), `‖m!‖⁻¹ ≤ √p^{m−1}` (`sq_norm_factorial_ge`), so `‖a_m‖ ≤ (p‖T₀‖)^m √p^{m−1} p^{−m} ≤ (‖T₀‖√p)^m`;
`m = 0`: `1 ≤ 1`.  (2) `PowerSeries.coeff` of the product: `(C d + C c X)^2 = C (d^2) + C (2cd) X + C (c^2) X^2`
(`sq`, `add_pow_two`/`ring`), so `coeff m (haloCol) = χ(d) (d² a_m + 2cd a_{m−1} + c² a_{m−2})`
(`PowerSeries.coeff_mul`, `coeff_C_mul`, `coeff_X_pow_mul'`; cases `m = 0, 1, ≥ 2`).  `‖χ(d)‖ = 1`
(W14 via W19-type membership, or directly: `d = ψ(unit)`, W11 + `norm_haloCharFun`).  Ultrametric
max of `‖d²‖‖a_m‖ ≤ ρ^m`, `‖2cd‖‖a_{m−1}‖ ≤ p⁻¹ ρ^{m−1} ≤ ρ^m` (W17), `‖c²‖‖a_{m−2}‖ ≤ p⁻² ρ^{m−2} ≤ ρ^m`.
#### Sources
[LWX, §2.3] ("χ m-locally analytic … (2.3.2) well defined"); [Jacobs, p. 29]; PadicExpLog.lean:89.

### [W21] **Evaluation of the halo column**
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:273 | **Depends on**: B10, W10, W11, W13, W19
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem evalAt_haloCol (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) {z : K}
    (hz : ‖z‖ ≤ 1) :
    evalAt (haloCol ψ T₀ ω (g 1 0) (g 1 1)) z
      = (g 1 0 * z + g 1 1) ^ 2 * haloCharFun ψ T₀ ω (g 1 0 * z + g 1 1)
```
#### Proof sketch
`evalAt_mul` twice (Char.lean:92; `AbsSummable` of `(C d + C c X)^2` (polynomial: `absSummable_C`,
`absSummable_X`, `absSummable_mul`, `absSummable_pow` as used in SlashAction.lean:711) and of the
`mk` series (geometric: from W20's bound (1) and `summable_geometric_of_lt_one`)); `evalAt` of the
polynomial is `(cz + d)^2` (`evalAt_linX`-style: Char.lean:333 pattern, `evalAt_pow`); `evalAt (C x) = x`;
`evalAt (mk (a_m)) z = ∑' m, C(s,m) (w z)^m = padicExp (s * padicLog (1 + w z))` by B10 with
`c := ‖T₀‖`: `hx : ‖wz‖ ≤ p⁻¹ ≤ ‖T₀‖` (`h0.le`), `hex : ‖s‖ ‖wz‖ ≤ p‖T₀‖ p⁻¹ = ‖T₀‖` (W10),
`hc : ‖T₀‖^2 < ‖p‖ = p⁻¹` (W1).  Then `padicExp (s * padicLog (1 + wz)) = χ (1 + wz)` (W11 at
`r = 1`: `teichRes 1 = 1`, `‖(1+wz) − 1‖ ≤ p⁻¹`, `map_one`, `inv_one`, `mul_one`) and
`χ(d) χ(1 + wz) = χ(d (1 + wz)) = χ(cz + d)` (W13 on the units `d`, `1 + wz` ∈ `haloUnits`:
W19-type memberships; `d * (1 + c/d z) = cz + d` by `field_simp`, `d ≠ 0`).
#### Sources
[Jacobs, Def 1.27]; [Koblitz, IV §2]; [LWX, (2.3.2)].

### [CL-W7] /cleanup HaloWeight.lean (after W21)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W21 — inline.

### [W22] `haloExpansion.eval`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:283 | **Depends on**: W16, W21
- **Parallel**: no | **Type**: def obligation
#### Statement
```lean
def haloExpansion … : ExpansionData (M1K ψ) (haloRho (p := p) T₀) (haloUnits ψ) (haloChar ψ T₀ ω hp2 hψ h0 h1) where
  … eval hg z hz hu := by sorry
```
#### Proof sketch
Goal: `evalAt (haloCol ψ T₀ ω (g 1 0) (g 1 1)) z = (haloChar … ⟨hu.unit, _⟩ : K)`; `rw [coe_haloChar_apply, evalAt_haloCol …]`;
`IsUnit.unit_spec`.
#### Sources
Char.lean:569–588 (`ExpansionData.eval`).

### [W23] `autFactor_haloWeight`
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:301 | **Depends on**: W22
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem autFactor_haloWeight … (g : M1K ψ) :
    (haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1
      = PowerSeries.C (haloCharFun ψ T₀ ω (g.1 1 1))
        * PowerSeries.mk fun m => Ring.choose (haloExponent (p := p) T₀) m
            * (g.1 1 0 / g.1 1 1) ^ m
```
#### Proof sketch
`autFactor W γ = W.col (γ 1 0) (γ 1 1) * ((linX γ)⁻¹)^2` (SlashAction.lean:356); `W.col = haloCol`
(`AnalyticWeight.toWeightSeries_col`, `ExpansionData.toWeightSeries` col is the datum's `col` — check
Char.lean:695); `linX γ = C d + C c X` (Series.lean:167) equals the polynomial factor of `haloCol`;
`(linX γ)^2 * ((linX γ)⁻¹)^2 = 1` since `linX γ` is a unit in `K⟦X⟧` (constant coefficient `d ≠ 0`:
`PowerSeries.mul_inv_cancel`, `constantCoeff_linX`); `mul_pow`, `mul_assoc`, `mul_comm`.
#### Sources
SlashAction.lean:356; Series.lean:167.

### [W24] **The automorphy factor evaluates to `χ(cz + d)`**
- **Status**: done (finished 2026-09-05 17:12) | **File**: PhD/LWX/HaloWeight.lean:308 | **Depends on**: W23
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem evalAt_autFactor_haloWeight … (g : M1K ψ) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1) z
      = haloCharFun ψ T₀ ω (g.1 1 0 * z + g.1 1 1)
```
#### Proof sketch
Either from W23 and the last two steps of W21's sketch (B10 + W11 + W13), or from W21 and
`evalAt_mul`/`evalAt_linX_inv` (Char.lean:359: `evalAt (linX γ)⁻¹ z = (cz + d)⁻¹`, needs
`‖c‖ < ‖d‖`): `evalAt (col * linX⁻¹^2) z = (cz+d)² χ(cz+d) (cz+d)^{−2}` and cancel (`cz + d ≠ 0`
since `‖cz + d‖ = 1`).  The second route reuses W21 and is shorter.
#### Sources
[LWX, (2.3.2)]; Char.lean:359.

### [CL-W8] /cleanup HaloWeight.lean — final (after W24)
- **Status**: done (inline cleanup 2026-09-05 17:12: omits, docstrings, helper extraction norm_coeff_linX_le, explicit Units.val_mul args, ≤100 cols) | **File**: PhD/LWX/HaloWeight.lean | **Depends on**: W24 — inline.

---

## Tranche H — `PhD/LWX/Certificates.lean` ([LWX, Prop 3.1] in full)

### [H1] `norm_det_theta_eq_one`
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:86 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem norm_det_theta_eq_one (x : U) : ‖(θ x).det‖ = 1
```
#### Proof sketch
`θ x ∈ M1 p` and `θ x⁻¹ ∈ M1 p` (`hU x.2`, `hU x⁻¹.2`); `det (θ x) * det (θ x⁻¹) = det (θ (x x⁻¹)) = 1`
(`map_mul`, `Matrix.det_mul`, `mul_inv_cancel`, `map_one`, `Matrix.det_one`); `‖det g‖ ≤ 1` for `g ∈ M1`
(`Matrix.det_fin_two`, entries `≤ 1`, ultrametric — mirror `LevelBounds.norm_det_le_one`, Series.lean:136);
`‖a‖‖b‖ = 1` with both `≤ 1` forces `‖a‖ = 1`.
#### Sources
[LWX, §2.2] (`Iw_q ⊂ GL₂(ℤ_p)`).

### [H2] `norm_theta_apply_zero_zero_eq_one`
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:91 | **Depends on**: H1
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem norm_theta_apply_zero_zero_eq_one (x : U) : ‖θ x 0 0‖ = 1
```
#### Proof sketch
`a d = det + b c` (`Matrix.det_fin_two`); `‖d‖ = 1`, `‖bc‖ ≤ ‖c‖ ≤ p⁻¹ < 1 = ‖det‖` (H1), so
`‖ad‖ = ‖det + bc‖ = 1` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), `‖a‖ = 1`.
Mirror of `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le` (Series.lean:149).
#### Sources
[LWX, Prop 3.1 proof] (`Iw_q`); Series.lean:149.

### [H3] **`Iw·η·Iw ⊆ (pℤ_p ℤ_p; pℤ_p ℤ_p^×)`**
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:100 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem isUpShape_toLocalMat_mul_mul (x y : U) {η : G} (hη : η ∈ levelM1 (p := p) θ)
    (hηa : ‖θ η 0 0‖ ≤ (p : ℝ)⁻¹) :
    (M1.toLocalMat (⟨θ ((x : G) * η * y),
      mul_mem (mul_mem (hU x.2) hη) (hU y.2)⟩ : M1 p)).IsUpShape
```
#### Proof sketch
`IsUpShape δ := ‖δ.a‖ ≤ p⁻¹` (UpMatrix.lean:61); `M1.coe_toLocalMat_a` gives `‖a‖ = ‖(θ (xηy)) 0 0‖`
(`PadicInt.norm_def`).  `θ (x η y) = θx * θη * θy` (`map_mul`); `(A * B * C) 0 0 = ∑_{i,j} A 0 i * B i j * C j 0`
(`Matrix.mul_apply`, `Fin.sum_univ_two`, expand to four terms).  Each term `≤ p⁻¹`: `‖A 0 i‖ ≤ 1`;
`i = 0, j = 0`: `‖B 0 0‖ ≤ p⁻¹` (`hηa`); `i = 0, j = 1`: `‖C 1 0‖ ≤ p⁻¹` (`y ∈ M1`); `i = 1, j = 0`:
`‖B 1 0‖ ≤ p⁻¹` (`η ∈ M1`); `i = 1, j = 1`: `‖C 1 0‖ ≤ p⁻¹`.  Ultrametric sum bound
(`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`).  Mirror of `exists_localMat_iwahori_mul`
(Halo.lean:264) without the explicit `v_j`.
#### Sources
[LWX, Prop 3.1 proof, lwx.txt:1094–1101]: "δi,j,p = ui,j,p vj ∈ Iwq (p 0; 0 1) Iwq ⊆ (pZp Zp; qZp Z×p)".

### [CL-H1] /cleanup Certificates.lean (after H3)
- **Status**: done (inline cleanup 2026-09-05 17:22: omits, imports sorted, header) | **File**: PhD/LWX/Certificates.lean | **Depends on**: H3 — inline.

### [H4] **[LWX, Prop 3.1(3)]**: certificate matrices have the `U_p`-shape
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:109 | **Depends on**: H3
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem isUpShape_certM1 {η : G} (hη : η ∈ levelM1 (p := p) θ) (hηa : ‖θ η 0 0‖ ≤ (p : ℝ)⁻¹)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
    (i : ι) (t : Fin p) : (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape
```
#### Proof sketch
`QMF.Weight.exists_mul_eta_mul_of_bijOn hv t : ∃ u₁ ∈ U, ∃ u₂ ∈ U, vRep t = u₁ * η * u₂`
(Compact.lean:221); then `u i t * vRep t = (u i t * u₁) * η * u₂` (`mul_assoc`), and H3 with
`x := ⟨u i t * u₁, mul_mem …⟩`, `y := ⟨u₂, _⟩`; transport along the equality of `M1`-elements
(`Subtype.ext`, `certM1` is `⟨θ (u * vRep t), _⟩`) — `IsUpShape` is a Prop on `M1.toLocalMat` of a
subtype element, so `congrArg`/`▸` after rewriting the underlying element.
#### Sources
[LWX, Prop 3.1(3)]; Compact.lean:221.

### [H5] **[LWX, Prop 3.1] in full**: `intEvalAtReps ∘ U_p = (ofCerts).op ω ∘ intEvalAtReps`
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:143 | **Depends on**: none
- **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem intEvalAtReps_intHeckeOperator (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {η : G}
    (hη : η ∈ levelM1 (p := p) θ) (h : …Finite) (c : ι → G) (hv : Set.BijOn …)
    (hvinj : Function.Injective vRep) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape)
    (φ : IntForms (Γ := Γ) θ hp2 ω U hU) :
    intEvalAtReps θ hp2 ω U hU c (intHeckeOperator θ U hU hp2 ω hη h φ)
      = (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape).op ω
          (intEvalAtReps θ hp2 ω U hU c φ)
```
#### Proof sketch
`intEvalAtReps_comm θ hp2 ω U hU c D (g := fun i t => certM1 θ U hU vRep hvΔ u i t) (hg := fun i t => rfl)
(Φ := intHeckeOperator …) hΦ φ` (IntegralModel.lean:1458) with `D := ofCerts …` (`ofCerts_tgt`,
`ofCerts_mat` are `rfl`).  `hΦ φ i`: `letI := seqLevelSlashAction θ hp2 ω; haveI := seqLevelSMulSlash θ hp2 ω`;
`AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) (HaloInt p) hU hη h φ vRep hvΔ hv hvinj
(c i) (fun t => c (idx i t)) (d i) (hd i) (u i) (hfact i) (fun t => mul_mem (hU (u i t).2) (hvΔ t))`
(Slash/HeckeMatrix.lean:57) gives `(Φ φ)(c i) = ∑ t, φ(c (idx i t)) ∣ₛ ⟨u i t * vRep t, _⟩` in the
level action; unfold the level slash (`seqLevelSlashAction`, IntegralModel.lean:1369:
`slash a u = seqSlashAction.slash a (levelM1ToM1 θ u)`, and `levelM1ToM1 θ ⟨g, hg⟩ = ⟨θ g, hg⟩`, :1360)
to match `RightSlashAction.slash (self := seqSlashAction hp2 ω) _ (certM1 …)` — `rfl` up to
`Finset.sum_congr`.  Mirror `QMF.Weight.heckeOperator_apply_rep` (Compact.lean:166).
#### Sources
[LWX, Prop 3.1 + proof, lwx.txt:1035–1101]; IntegralModel.lean:1451–1547; Slash/HeckeMatrix.lean:57.

### [H6] **[LWX, (2.11.1)] at a neat level**
- **Status**: done (finished 2026-09-05 17:22) | **File**: PhD/LWX/Certificates.lean:154 | **Depends on**: none
- **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem bijective_intEvalAtReps_of_stabilizer_eq_bot (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (c : ι → G) (hc : Function.Bijective (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    Function.Bijective (intEvalAtReps (Γ := Γ) θ hp2 ω U hU c)
```
#### Proof sketch
Transcribe `QMF.Weight.bijective_evalAtReps` + `bijective_evalAtReps_of_stabilizer_eq_bot`
(Compact.lean:297–380) with `K ↦ HaloInt p`, `c(ℕ, K) ↦ c(ℕ, HaloInt p)`, `Forms ↦ IntForms`,
`evalAtReps ↦ intEvalAtReps`, `blockProj_evalAtReps ↦ blockProj_intEvalAtReps` (IntegralModel.lean:1435),
`kappaSlash ↦ seqSlashAction.slash`: injectivity from an `ext_of_forall_rep` mirror (the
`AutomorphicFunction.slash_apply_mul`/`left_invt'` argument, Compact.lean:108, is ring-generic);
surjectivity from `AutomorphicFunction.bijective_evalAtRepsSlash (A := c(ℕ, HaloInt p)) (HaloInt p) hU
(fun q => c (e.symm q)) hσ` with the invariance condition trivial at `w = 1` (`hstab`, `Subgroup.mem_bot`,
`map_one`, `slash_one`).
#### Sources
[LWX, (2.11.1), Hypothesis 2.10]; Compact.lean:297–380; Slash/HeckeMatrix.lean:181.

### [CL-H2] /cleanup Certificates.lean — final (after H6)
- **Status**: done (inline cleanup 2026-09-05 17:22: omits, imports sorted, header) | **File**: PhD/LWX/Certificates.lean | **Depends on**: H6 — inline.

---

## Tranche E — `PhD/LWX/Seam.lean` ([LWX, Prop 2.17] at `m = 1`)

### [E1] `specEntryOp`: bounds, column decay, matrix
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:77–83 | **Depends on**: S6
- **Parallel**: no | **Type**: def obligations (2) + lemma
#### Statement
```lean
def specEntryOp (hp2 : p ≠ 2) (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m n => HaloInt.specialize (intHom ψ) T₀ (entry ω δ m n)) ⟨1, by sorry⟩ (by sorry)
-- (the other declarations of the section take `(hp2) (ψ) (hψ) {T₀} (h0) (h1 : ‖T₀‖ < 1) (ω)` as section variables)
theorem matrixCoeff_specEntryOp (δ : LocalMat p) (m n : ℕ) :
    matrixCoeff (specEntryOp hp2 ψ hψ h0 h1 ω δ) m n
      = HaloInt.specialize (intHom ψ) T₀ (entry ω δ m n)
```
#### Proof sketch
(The def takes `hp2 hψ h0 h1` explicitly, so both obligations may use `norm_specialize_le`;
downstream callers with the sub-annulus hypothesis pass `(norm_lt_one_of_sq_lt h1)`.)
Bound: `‖spec (entry)‖ ≤ ‖T₀‖^0 = 1` from `norm_specialize_le` with `k = 0` (`HaloInt.norm_le_one`).
Column decay: for fixed `n`, `‖entry ω δ m n‖ ≤ p^{-(m − n/p)}` needs `hp2` and `δ.IsUpShape`
(`norm_entry_le`, UpMatrix.lean:505) — **or** use the `M₁`-shape bound `norm_entry_le_M1`
(UpMatrix.lean:522, `hp2`, any `δ`); either way `norm_specialize_le` gives `‖spec(entry m n)‖ ≤ ‖T₀‖^{k(m)}`
with `k(m) → ∞`, so `Tendsto … cofinite (𝓝 0)` (`Nat.cofinite_eq_atTop`, `squeeze_zero_norm`,
`tendsto_pow_atTop_nhds_zero_of_lt_one`).  Matrix: `matrixCoeff_ofCoeffs`.
#### Sources
UpMatrix.lean:505/522, HaloRing.lean:660; [LWX, Prop 3.4].

### [E2] `matrixCoeff_specOp`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:99 | **Depends on**: E1
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem matrixCoeff_specOp (D : UpDatum p ι) (a b : ι × ℕ) :
    matrixCoeff (specOp hp2 ψ hψ h0 h1 ω D) a b
      = HaloInt.specialize (intHom ψ) T₀ (D.matrix ω a b)
```
#### Proof sketch
`obtain ⟨i, m⟩ := a; ⟨j, n⟩ := b`; `specOp` = `blockOp`; `matrixCoeff_blockOp` (BlockOp.lean:654),
`matrixCoeff_sum` (:117), `matrixCoeff_specEntryOp`; `UpDatum.matrix` (UpMatrix.lean:544) is the
same filtered sum; `map_sum` for `specializeHom` (S2/S1 — or `specialize_add`/`_zero` via `Finset.sum_induction`).
#### Sources
UpMatrix.lean:544; BlockOp.lean:654.

### [E3] `minor_specOp`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:105 | **Depends on**: E2, S5
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem minor_specOp (D : UpDatum p ι) (S : Finset (ι × ℕ)) :
    minor (specOp hp2 ψ hψ h0 h1 ω D) S
      = HaloInt.specialize (intHom ψ) T₀ (minor (D.op ω) S)
```
#### Proof sketch
`unfold minor`; `RingHom.map_det (specializeHom (intHom ψ) (norm_intHom ψ hψ) h0 h1)`; `Matrix.ext`
(`RingHom.mapMatrix_apply`, `Matrix.map_apply`, `Matrix.of_apply`); entrywise
`matrixCoeff_specOp` and `UpDatum.matrixCoeff_op hp2` (UpMatrix.lean:705).
#### Sources
Fredholm.lean:33; UpMatrix.lean:705.

### [CL-E1] /cleanup Seam.lean (after E3)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E3 — inline.

### [E4] **`c_n(P(T₀)) = c_n(P)(T₀)`**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:113 | **Depends on**: E3, S7
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem charCoeff_specOp (D : UpDatum p ι) (n : ℕ) :
    charCoeff (specOp hp2 ψ hψ h0 h1 ω D) n
      = HaloInt.specialize (intHom ψ) T₀ (charCoeff (D.op ω) n)
```
#### Proof sketch
`unfold charCoeff`; `map_mul`, `map_pow`, `map_neg`, `map_one` for `specializeHom`; the `tsum`:
`((summable_minor_upOp hp2 D ω n).hasSum.specialize …).tsum_eq` (S7; Halo.lean:113) after
rewriting the summand by E3 (`tsum_congr`).
#### Sources
[LWX, Thm 3.16] ("well defined"), Cor 3.18; Halo.lean:113, :157.

### [E5] `charPowerSeries_specOp`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:119 | **Depends on**: E4
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem charPowerSeries_specOp (D : UpDatum p ι) :
    charPowerSeries (specOp hp2 ψ hψ h0 h1 ω D) = specCharSeries D ω (intHom ψ) T₀
```
#### Proof sketch
`PowerSeries.ext fun n => by rw [charPowerSeries_coeff, specCharSeries, PowerSeries.coeff_mk, charCoeff_specOp …]`.
#### Sources
Halo.lean:157.

### [E6] `levelMonoidOf_thetaK` (+ `subset_…`, `mem_…`)
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:136, :140, :144 | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas (3)
#### Statement
```lean
theorem levelMonoidOf_thetaK : levelMonoidOf (thetaK ψ θ) (M1K ψ) = levelM1 (p := p) θ
theorem subset_levelMonoidOf_thetaK (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ) :
    (U : Set G) ⊆ levelMonoidOf (thetaK ψ θ) (M1K ψ)
theorem mem_levelMonoidOf_thetaK {g : G} (hg : g ∈ levelM1 (p := p) θ) :
    g ∈ levelMonoidOf (thetaK ψ θ) (M1K ψ)
```
#### Proof sketch
`Submonoid.ext`; `levelMonoidOf θ S = S.comap θ` (Forms.lean:87), `levelM1 θ = (M1 p).comap θ`
(IntegralModel.lean:1355), `M1K ψ = (M1 p).map (mapMatrix ψ)`; `Submonoid.mem_comap`, `Submonoid.mem_map`;
`←`: witness `θ g`; `→`: `mapMatrix ψ δ = mapMatrix ψ (θ g)` ⇒ `δ = θ g` by injectivity
(`RingHom.injective ψ` — `ℚ_[p]` a field, `K` nontrivial — and `Matrix.map_injective`).  The other
two follow (`rw [levelMonoidOf_thetaK]`).
#### Sources
Forms.lean:87; IntegralModel.lean:1355.

### [CL-E2] /cleanup Seam.lean (after E6)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E6 — inline.

### [E7] `mahlerOfPow` and `mahlerON_mahlerOfPow`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:161–167 | **Depends on**: M6
- **Parallel**: no | **Type**: def obligation + lemma
#### Statement
```lean
def mahlerOfPow (n : ℕ) : c(ℕ, HaloInt p) :=
  cSpace.ofTendsto (fun k => HaloInt.const (mahlerCoeffPow k n : ℤ_[p])) (by sorry)
theorem mahlerON_mahlerOfPow (n : ℕ) (z : ℤ_[p]) :
    mahlerON (mahlerOfPow (p := p) n) z = HaloInt.const (z ^ n)
```
#### Proof sketch
Decay: finitely supported (`mahlerCoeffPow_eq_zero_of_lt`, M1; `Int.cast_zero`, `HaloInt.const` of `0`
is `0` — `map_zero (constRingHom)`), `tendsto_nhds_of_eventually_eq`.  Evaluation: `mahlerON_apply`
(IntegralModel.lean:1044): `∑' k, a k * const (Ring.choose z k)`; `tsum_eq_sum` over `range (n+1)`;
`const_mul`/`constRingHom` pulls out: `= const (∑_k mahlerCoeffPow k n * Ring.choose z k) = const (z^n)`
by M6 (`mul_comm`).  (`cSpace.ofTendsto` apply-lemma: BlockOp.lean:68 — check its `@[simp]` name.)
#### Sources
[LWX, §2.16 (2.16.1)]; IntegralModel.lean:1044.

### [E8] **Integral Mahler coordinates of `[cz+d]·möb(z)ⁿ`** ([LWX, Prop 3.4] specialised to monomials)
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:177 | **Depends on**: E7
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem fwdDiff_iter_cfunSlash_pow (hp2 : p ≠ 2) (δ : M1 p) (n m : ℕ) :
    Δ_[1]^[m] (fun z : ℤ_[p] => univChar ω ((M1.toLocalMat δ).denUnit z)
        * HaloInt.const ((M1.toLocalMat δ).mobiusFun z ^ n)) 0
      = ∑ k ∈ Finset.range (n + 1),
          (mahlerCoeffPow k n : HaloInt p) * entry ω (M1.toLocalMat δ) m k
```
#### Proof sketch
The function is `⇑(cfunSlash hp2 ω (mahlerON (mahlerOfPow n)) δ)` (IntegralModel.lean:533 + E7,
`ContinuousMap.ext`/`funext`).  `mahlerCoeffs_apply` (:1075) turns the LHS into
`mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) δ) m` with `a = mahlerOfPow n`, which is
`(RightSlashAction.slash (self := seqSlashAction hp2 ω) a δ) m` by definition of `seqSlashAction`
(:1284, `rfl`), `= ∑' k, a k * entry ω (M1.toLocalMat δ) m k` (`seqSlash_coeff`, :1414);
`tsum_eq_sum` over `range (n+1)` (M1); `a k = const (mahlerCoeffPow k n)` and
`(mahlerCoeffPow k n : HaloInt p) = const (…)` (`Int.cast` into `HaloInt p` vs `const`: via
`map_intCast constRingHom` — check `HaloInt.constRingHom` :559).
#### Sources
[LWX, Prop 3.4 (3.4.1), lwx.txt:1144–1150]; IntegralModel.lean:1272–1284, :1414.

### [E9] `intHom_denUnit`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:183 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem intHom_denUnit (δ : M1 p) (z : ℤ_[p]) :
    intHom ψ ((M1.toLocalMat δ).denUnit z : ℤ_[p])
      = (RingHom.mapMatrix ψ) δ.1 1 0 * intHom ψ z + (RingHom.mapMatrix ψ) δ.1 1 1
```
#### Proof sketch
`LocalMat.denUnit δ z = (isUnit_c_mul_add δ z).unit` (IntegralModel.lean:314), `IsUnit.unit_spec`:
value `δ.c * z + δ.d`; `map_add`, `map_mul`; `M1.coe_toLocalMat_c/_d` (:300–310) and
`RingHom.mapMatrix_apply`/`Matrix.map_apply`; `intHom_apply`.
#### Sources
IntegralModel.lean:286–318.

### [CL-E3] /cleanup Seam.lean (after E9)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E9 — inline.

### [E10] `intHom_mobiusFun`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:190 | **Depends on**: E9
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem intHom_mobiusFun (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (δ : M1 p) (z : ℤ_[p]) :
    intHom ψ ((M1.toLocalMat δ).mobiusFun z)
      = evalAt (mobius ((RingHom.mapMatrix ψ) δ.1)) (intHom ψ z)
```
#### Proof sketch
`mobiusFun δ z = (δ.a * z + δ.b) * Ring.inverse (δ.c * z + δ.d)` (UpMatrix.lean:65); `map_mul`,
`map_add`; `intHom ψ (Ring.inverse u) = (intHom ψ u)⁻¹` for the unit `u = cz + d`
(`Ring.inverse_unit`, `map_units_inv`, `Units.val_inv_eq_inv_val`; `ψ` into a field: `map_inv₀`).
RHS: `evalAt_mobius (hd : g 1 1 ≠ 0) (hlt : ‖g 1 0‖ < ‖g 1 1‖) (hz : ‖ψ z‖ ≤ 1)` (Char.lean:368):
`(g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1)`; `hlt`: `‖ψ c‖ ≤ p⁻¹ < 1 = ‖ψ d‖` (`hψ`, `δ.2`);
`div_eq_mul_inv`, `M1.coe_toLocalMat_*`.
#### Sources
UpMatrix.lean:65; Char.lean:368.

### [E11] `mk_kappaSlash_single`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:198 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem mk_kappaSlash_single … (g : M1K ψ) (n : ℕ) :
    PowerSeries.mk (fun j => (haloWeight ψ T₀ ω hp2 hψ h0 h1).kappaSlash g (cSpace.single n 1) j)
      = (haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1 * mobius g.1 ^ n
```
#### Proof sketch
`PowerSeries.ext fun j`; `PowerSeries.coeff_mk`; `AnalyticWeight.kappaSlash_def` + `WeightSeries.kappaSlash_apply`
(SlashAction.lean:462): `∑' i, coeff j (autFactor * mobius^i) * single n 1 i`; `tsum_eq_single n`
(`cSpace.single_apply_of_ne`, `cSpace.single_apply_self`), `mul_one`.
#### Sources
SlashAction.lean:462.

### [E12] **Pointwise agreement at `ℕ`-points**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:209 | **Depends on**: S3, S5, W15, W24, E9, E10
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem specialize_cfunSlash_pow_natCast … (δ : M1 p) (n k : ℕ) :
    HaloInt.specialize (intHom ψ) T₀ (univChar ω ((M1.toLocalMat δ).denUnit k)
        * HaloInt.const ((M1.toLocalMat δ).mobiusFun k ^ n))
      = evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor
          ((RingHom.mapMatrix ψ) δ.1) * mobius ((RingHom.mapMatrix ψ) δ.1) ^ n) (k : K)
```
#### Proof sketch
LHS: `specialize_mul` (S5), `specialize_const` (S3), `map_pow`; `haloCharFun_psi` (W15) at
`a := denUnit k`: `spec (univChar ω (denUnit k)) = χ (intHom ψ (denUnit k)) = χ (c' k + d')` (E9,
`map_natCast`); `intHom ψ (mobiusFun k) = evalAt (mobius g) k` (E10).  RHS: `evalAt_mul`
(`absSummable_autFactor`, `absSummable_pow (absSummable_mobius)`; `g := mapMatrix ψ δ ∈ M1K ψ`),
`evalAt_pow` (Char.lean:286), `evalAt_autFactor_haloWeight` (W24) with `⟨g, M1K.ofM1 …⟩`.
#### Sources
[LWX, (2.3.2), lwx.txt:596–603]; Char.lean:92, :286.

### [CL-E4] /cleanup Seam.lean (after E12)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E12 — inline.

### [E13] **The seam identity for one certificate matrix**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:220 | **Depends on**: M5, M16, E1, E8, E11, E12
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem monomialToMahler_comp_kappaSlash … (δ : M1 p) :
    (monomialToMahler K).comp ((haloWeight ψ T₀ ω hp2 hψ h0 h1).kappaSlash (M1K.ofM1 ψ δ))
      = (specEntryOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω (M1.toLocalMat δ)).comp
          (monomialToMahler K)
```
#### Proof sketch
`ext_matrixCoeff fun m n`; `matrixCoeff_comp` both sides (Matrix.lean:84).  LHS
`= ∑' k, matrixCoeff (kappaSlash g) k n * mahlerCoeffPow m k` and `matrixCoeff (kappaSlash g) k n
= (kappaSlash g (single n 1)) k = coeff k (autFactor * mobius^n)` (E11, `matrixCoeff` def), so LHS
`= Δ^m (fun j : ℕ => evalAt (autFactor * mobius^n) j) 0` (M16 with `TendstoCoeff` from
`AbsSummable.tendstoCoeff (absSummable_mul …)`).  Pointwise (E12) the function is
`j ↦ spec (F (j : ℤ_[p]))` with `F z = univChar ω (denUnit z) * const (möb z ^ n)`; so LHS
`= Δ^m (fun j : ℕ => spec (F j)) 0 = spec (Δ^m (fun j : ℕ => F j) 0)` (M5 with
`(specializeHom …).toAddMonoidHom`) `= spec (Δ^m F 0)` (the `ℕ`-vs-`ℤ_p`-domain bridge:
both are `∑_{i ≤ m} c_i • F (i)` by `fwdDiff_iter_eq_sum_shift`, with `(0 : ℤ_[p]) + i • 1 = (i : ℤ_[p])`
— a private 5-line lemma) `= spec (∑_{k ≤ n} mahlerCoeffPow k n * entry m k)` (E8)
`= ∑_{k ≤ n} mahlerCoeffPow k n * spec (entry m k)` (`map_sum`, `map_mul`, `map_intCast`).
RHS `= ∑' k, matrixCoeff Φ k n * matrixCoeff (specEntryOp) m k = ∑' k, mahlerCoeffPow k n * spec (entry m k)`
(M12, E1), `tsum_eq_sum` over `range (n+1)` (M1).  Coefficients in `K` vs `HaloInt p`:
`(mahlerCoeffPow k n : K) = spec ((mahlerCoeffPow k n : HaloInt p))` (`map_intCast`).
#### Sources
[LWX, Prop 2.17 proof] ("P′ … the infinite matrix of Up-action on this basis"), Prop 3.4; Matrix.lean:66–90.

### [E14] `monomialToMahlerBlock_eq`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:248 | **Depends on**: M15, C5, C8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem monomialToMahlerBlock_eq :
    (monomialToMahlerBlock (K := K) (ι := ι))
      = (diagFactorialBlock (K := K) (ι := ι)).comp
          ((colmezEquivBlock (K := K) (ι := ι)).symm : c(ι × ℕ, K) →L[K] c(ι × ℕ, K))
```
#### Proof sketch
`unfold monomialToMahlerBlock diagFactorialBlock colmezEquivBlock`; `coe_diagBlockEquiv_symm` (C8);
`blockDiag_comp_blockOp`-style: `(blockDiag Δ).comp (blockDiag Ψ) = blockDiag (Δ.comp Ψ)` (C5 with
`T := if a = b then Ψ else 0`, `Finset.sum_ite_eq`, `comp_zero`); then `monomialToMahler_eq` (M15).
#### Sources
[LWX, Prop 2.17 proof]; M15.

### [E15] **The seam identity blockwise**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:269 | **Depends on**: C5, C6, E2, E13
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem monomialToMahlerBlock_comp_heckeBlockOp … (hshape …) :
    (monomialToMahlerBlock (K := K) (ι := ι)).comp
        (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
          (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
          (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u)
      = (specOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω
          (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (monomialToMahlerBlock (K := K) (ι := ι))
```
#### Proof sketch
`unfold heckeBlockOp specOp monomialToMahlerBlock`; `rw [blockDiag_comp_blockOp, blockOp_comp_blockDiag]`
(C5, C6); `congr 1; funext i j`; `heckeBlock` (Compact.lean:151) is
`∑_{t : idx i t = j} ((1 : Kˣ) : K) • kappaSlash (levelMonoidOfToS θK S ⟨u i t * vRep t, _⟩)`;
`MonoidHom.one_apply`, `Units.val_one`, `one_smul`; `ContinuousLinearMap.comp_sum`/`sum_comp`
(`Finset.sum` of compositions: `ContinuousLinearMap.comp_finset_sum`, `finset_sum_comp`);
termwise `levelMonoidOfToS θK S ⟨g, hg⟩ = M1K.ofM1 ψ (certM1 …)` (`Subtype.ext`, `thetaK_cert`,
`rfl`), then E13.  `ofCerts_tgt`/`ofCerts_mat` (`rfl`) align the filter and the entry streams.
#### Sources
[LWX, Prop 3.1(1)–(2)], Prop 2.17; Compact.lean:151–166.

### [CL-E5] /cleanup Seam.lean (after E15)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E15 — inline.

### [E16] **`U_p` is compactoid at the halo weight**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:279 | **Depends on**: W17
- **Parallel**: yes | **Type**: theorem
#### Statement
```lean
theorem isCompactoid_heckeBlockOp_haloWeight … (hshape …) :
    IsCompactoid (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
      (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
      (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u)
```
#### Proof sketch
`isCompactoid_blockOp` (BlockOp.lean:683) `fun i j => IsCompactoid.finset_sum _ fun t _ => IsCompactoid.smul _ ?_`
(as `isCompactoid_heckeBlock`, Compact.lean:264); per term
`(haloWeight …).isCompactoid_kappaSlash g (hρσ := le_rfl) (hσ := haloRho_lt_one h1) (ha : ‖g.1 0 0‖ ≤ ρ)`
(Char.lean:853, `σ := ρ`); `g.1 0 0 = ψ ((certM1 …) 0 0)`, `‖·‖ = ‖(M1.toLocalMat (certM1 …)).a‖ ≤ p⁻¹`
(`hshape i t`, `IsUpShape`, `M1.coe_toLocalMat_a`, `PadicInt.norm_def`, `hψ`) `≤ ρ` (W17).
#### Sources
[LWX, §2.12] ("the action of Up is compact (see e.g. [Bu07, Lemma 12.2])"); Compact.lean:264–296;
SlashAction.lean:394.

### [E17] `diagFactorialBlock_comp_colmezConj`
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:297 | **Depends on**: E14, E15, C8
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem diagFactorialBlock_comp_colmezConj … (hshape …) :
    (diagFactorialBlock (K := K) (ι := ι)).comp
        ((((colmezEquivBlock (K := K) (ι := ι)).symm : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)).comp
          (heckeBlockOp …)).comp
          (colmezEquivBlock (K := K) (ι := ι) : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)))
      = (specOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω
          (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (diagFactorialBlock (K := K) (ι := ι))
```
#### Proof sketch
From E15 rewrite `monomialToMahlerBlock` by E14 on both sides: `(Δ ∘ Ψ⁻¹) ∘ H = specOp ∘ (Δ ∘ Ψ⁻¹)`;
compose both sides on the right with `Ψ` (`congrArg (·.comp Ψ)`), `ContinuousLinearMap.comp_assoc`,
`ContinuousLinearEquiv.symm_comp_self` (`Ψ⁻¹ ∘ Ψ = id`: `(colmezEquivBlock).symm.comp colmezEquivBlock`
as CLMs — `ContinuousLinearEquiv.coe_symm_comp_self`/`symm_comp_self`), `comp_id`.
#### Sources
[LWX, Prop 2.17 proof].

### [CLEANUP-ALL-1] /cleanup-all on the nine board files (before E18)
- **Status**: done (2026-09-05 18:02: runLinter clean on all nine modules, 0 sorries, ≤100 cols, std axioms) | **Depends on**: E17 and every earlier ticket of tranches C, S, B, M, W, H, E
- **Type**: cleanup — inline, file by file; runLinter each module.

### [E18] **MILESTONE — [LWX, Proposition 2.17] at `m = 1`**
- **Status**: done (finished 2026-09-05 17:38) | **File**: PhD/LWX/Seam.lean:315 | **Depends on**: C3, E5, E16, E17, CLEANUP-ALL-1
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem specCharSeries_ofCerts_eq_heckeCharPowerSeries (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (intHom ψ) T₀
      = heckeCharPowerSeries (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
          (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
          (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u
```
#### Proof sketch
Set `H := heckeBlockOp …`, `X := (Ψ⁻¹.comp H).comp Ψ` with `Ψ := colmezEquivBlock`.
1. `heckeCharPowerSeries … = charPowerSeries H` (`rfl`, Fredholm.lean:49).
2. `charPowerSeries H = charPowerSeries X`: `(charPowerSeries_conj (φ := Ψ.symm) H (isCompactoid_heckeBlockOp_haloWeight …)).symm`
   (Fredholm.lean:953: `charPowerSeries ((φ.comp u).comp φ.symm) = charPowerSeries u`; `φ.symm = Ψ`
   via `ContinuousLinearEquiv.symm_symm`).
3. `charPowerSeries X = charPowerSeries (specOp …)`: `charPowerSeries_eq_of_diag_intertwine (d := fun a => ((a.2 ! : ℕ) : K))
   (hd := fun a => isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))) h` (C3) where `h a b`
   comes from E17 read at `(a, b)`: `matrixCoeff (Δ.comp X) a b = d a * matrixCoeff X a b` and
   `matrixCoeff (specOp.comp Δ) a b = matrixCoeff specOp a b * d b` (`matrixCoeff_comp`,
   `matrixCoeff_blockDiag` C7, `matrixCoeff_diagFactorial` M13, `tsum_eq_single`).
4. `charPowerSeries (specOp …) = specCharSeries …` (E5 with `norm_lt_one_of_sq_lt h1`).
Chain with `Eq.trans`/`symm`.
#### Sources
[LWX, Prop 2.17 + proof, lwx.txt:963–1016]; [Buzzard, Cor 2.6]; Fredholm.lean:49, :953.

### [CL-E6] /cleanup Seam.lean — final (after E18)
- **Status**: done (inline cleanup 2026-09-05 17:38: omits, docstrings, helpers matrixCoeff_diagFactorialBlock(_comp), fwdDiff_iter_comp_natCast, header) | **File**: PhD/LWX/Seam.lean | **Depends on**: E18 — inline.

---

## Tranche F — `PhD/ForMathlib/NumberTheory/Padics/AdicCompletionEquiv.lean`

### [F1] `absNorm_asIdeal_primesEquiv_symm`
- **Status**: done (finished 2026-09-05 17:51) | **File**: PhD/ForMathlib/NumberTheory/Padics/AdicCompletionEquiv.lean:40 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma
#### Statement
```lean
theorem absNorm_asIdeal_primesEquiv_symm :
    Ideal.absNorm ((Rat.HeightOneSpectrum.primesEquiv (R := RingOfIntegers ℚ)).symm p).asIdeal
      = (p : ℕ)
```
#### Proof sketch
Generalise `JacobsSlash`'s private `asIdeal_v₃`/`absNorm_asIdeal_v₃` (`U3/2_PadicEmbedding.lean:60–85`):
`v.asIdeal = Ideal.span {(p : 𝓞 ℚ)}` from `Rat.HeightOneSpectrum.span_natGenerator` +
`primesEquiv.apply_symm_apply` (`natGenerator (primesEquiv.symm p) = p`) + `Ideal.comap_map_of_bijective`
along `Rat.IsIntegralClosure.intEquiv`; then `Ideal.absNorm_span_singleton`, `Algebra.norm_algebraMap`,
`NumberField.RingOfIntegers.rank`, `Module.finrank_self`, `Int.natAbs`.
#### Sources
mathlib `NumberTheory/Padics/HeightOneSpectrum.lean:85–105`; JacobsSlash U3/2_PadicEmbedding.lean.

### [F2] `norm_natCast_adicCompletion`
- **Status**: done (finished 2026-09-05 17:51) | **File**: …/AdicCompletionEquiv.lean:46 | **Depends on**: F1
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem norm_natCast_adicCompletion :
    ‖(((p : ℕ) : ℕ) : ((Rat.HeightOneSpectrum.primesEquiv (R := RingOfIntegers ℚ)).symm p).adicCompletion ℚ)‖
      = ((p : ℕ) : ℝ)⁻¹
```
#### Proof sketch
Mirror `JacobsSlash.norm_three_eq` (U3/2_PadicEmbedding.lean:90): `FinitePlace.norm_def`
(`‖x‖ = toNNReal (absNorm v) (Valued.v x)`), `Valued.v (p : K_v) = exp (−1)` (the valuation of the
generator: `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` + `intValuation` of the
generator `= exp (-1)`; mirror `valued_three_eq`, U3/1_Setting.lean:504), `WithZeroMulInt.toNNReal_neg_apply`,
F1.
#### Sources
JacobsSlash U3/2_PadicEmbedding.lean:90–101; ForMathlib FinitePlace.lean.

### [F3] **The comparison equivalence is an isometry**
- **Status**: done (finished 2026-09-05 17:51) | **File**: …/AdicCompletionEquiv.lean:53 | **Depends on**: F2
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem norm_adicCompletionEquiv (y : ℚ_[p]) :
    ‖(adicCompletionEquiv (RingOfIntegers ℚ) p y : …adicCompletion ℚ)‖ = ‖y‖
```
#### Proof sketch
Mirror `JacobsSlash.norm_adicCompletionEquiv` (U3/2_PadicEmbedding.lean:103–160): the closed unit
ball maps into the integers (`PadicInt.coe_adicCompletionIntegersEquiv_apply`, `mem_adicCompletionIntegers`,
`Valued.toNormedField.norm_le_one_iff`), so `‖E y‖ ≤ 1` for `‖y‖ ≤ 1` and (via `y⁻¹`) `‖E y‖ = 1`
for `‖y‖ = 1`; write `y = p^k · u` with `‖u‖ = 1` (`Padic.norm_eq_zpow`/`Padic.valuation` and
`Padic.unitCoeff`), `map_mul`, `map_zpow₀`, `E p = p` (`map_natCast`), F2, `padicNormE.norm_p_zpow`.
#### Sources
JacobsSlash U3/2_PadicEmbedding.lean:103–160; [LWX, §2.4] ("we fix an isomorphism D⊗Qp ≃ M2(Qp)").

### [CL-F1] /cleanup AdicCompletionEquiv.lean — final (after F3)
- **Status**: done (inline cleanup 2026-09-05 17:51: helpers asIdeal/natGenerator/intValuation/valued lemmas, norm_adicCompletionEquiv_symm corollary, header, ≤100 cols) | **File**: PhD/ForMathlib/NumberTheory/Padics/AdicCompletionEquiv.lean | **Depends on**: F3 — inline; consider a `Padic.norm_adicCompletionEquiv_symm` corollary.

---

## Tranche Q — `PhD/LWX/Quaternionic.lean` (`D/ℚ`)

### [Q1] `CharZero (Kp p)`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:56 | **Depends on**: none
- **Parallel**: yes | **Type**: instance
#### Statement
```lean
instance : CharZero (Kp p) := by sorry
```
#### Proof sketch
`charZero_of_injective_algebraMap (algebraMap ℚ (Kp p)).injective` (as U3/1_Setting.lean:109; may
need `attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion`
to pin the `Algebra ℚ` path, as that file does).
#### Sources
JacobsSlash U3/1_Setting.lean:104–109.

### [Q2] `padicComparisonSymm_comp`, `padicComparison_comp`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:68, :72 | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas (2)
#### Statement
```lean
theorem padicComparisonSymm_comp : (padicComparisonSymm p).comp (padicComparison p) = RingHom.id ℚ_[p]
theorem padicComparison_comp : (padicComparisonSymm p).comp … -- see file: (padicComparison p).comp (padicComparisonSymm p) = RingHom.id (Kp p)
```
#### Proof sketch
`RingHom.ext`; `RingHomClass.toRingHom` applied is the underlying function (`RingHomClass.coe_coe`/`rfl`);
`ContinuousAlgEquiv.symm_apply_apply` / `apply_symm_apply`.
#### Sources
mathlib `Padic.adicCompletionEquiv`.

### [Q3] `norm_padicComparison`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:76 | **Depends on**: F3
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem norm_padicComparison (y : ℚ_[p]) : ‖padicComparison p y‖ = ‖y‖
```
#### Proof sketch
`Padic.norm_adicCompletionEquiv ⟨p, hp.out⟩ y` (F3); `padicComparison` unfolds to the same term
(`padicPlace` is `primesEquiv.symm ⟨p, _⟩` by definition, `rfl`).
#### Sources
F3.

### [CL-Q1] /cleanup Quaternionic.lean (after Q3)
- **Status**: done (inline cleanup 2026-09-05 18:02: norm_natCast_p_Kp helper, docstrings, declaration order, header) | **File**: PhD/LWX/Quaternionic.lean | **Depends on**: Q3 — inline.

### [Q4] `valued_natCast_p_le_one`, `natCast_p_ne_zero`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:80, :83 | **Depends on**: Q1, Q3
- **Parallel**: no | **Type**: lemmas (2)
#### Statement
```lean
theorem valued_natCast_p_le_one : Valued.v ((p : ℕ) : Kp p) ≤ 1
theorem natCast_p_ne_zero : ((p : ℕ) : Kp p) ≠ 0
```
#### Proof sketch
`Valued.toNormedField.norm_le_one_iff` (AdicLevel.lean pattern) with `‖(p : Kp p)‖ = p⁻¹ ≤ 1`
(`(p : Kp) = padicComparison p (p : ℚ_[p])`, `map_natCast`, Q3, `padicNormE.norm_p`); or
`mem_adicCompletionIntegers` + `algebraMap` integrality.  `natCast_p_ne_zero`: `Nat.cast_ne_zero.2 hp.out.ne_zero`
(`CharZero`, Q1).
#### Sources
AdicLevel.lean (`Valued.toNormedField.norm_le_iff`).

### [Q5] `thetaK_thetaInt`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:96 | **Depends on**: Q2
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem thetaK_thetaInt : thetaK (padicComparison p) (thetaInt p D) = toMatrix ℚ D (padicPlace p)
```
#### Proof sketch
`MonoidHom.ext fun g`; `thetaK_apply`, `thetaInt` unfold: `mapMatrix E (mapMatrix E.symm M) = M`
(`RingHom.mapMatrix_apply`, `Matrix.map_map`, Q2 (`padicComparison_comp`) pointwise, `Matrix.map_id`).
#### Sources
—

### [Q6] `subset_levelMonoidOf_toMatrix`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:108 | **Depends on**: E6, Q5
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem subset_levelMonoidOf_toMatrix (U : Subgroup (Dfx ℚ D))
    (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D)) :
    (U : Set (Dfx ℚ D)) ⊆ levelMonoidOf (toMatrix ℚ D (padicPlace p)) (M1K (padicComparison p))
```
#### Proof sketch
`rw [← thetaK_thetaInt]; exact subset_levelMonoidOf_thetaK _ _ U hU` (E6).
#### Sources
—

### [CL-Q2] /cleanup Quaternionic.lean (after Q6)
- **Status**: done (inline cleanup 2026-09-05 18:02: norm_natCast_p_Kp helper, docstrings, declaration order, header) | **File**: PhD/LWX/Quaternionic.lean | **Depends on**: Q6 — inline.

### [Q7] `thetaInt_etaAdelic'`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:120 | **Depends on**: Q2, Q4
- **Parallel**: no | **Type**: lemma
#### Statement
```lean
theorem thetaInt_etaAdelic' :
    thetaInt p D (etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p))
      = !![(p : ℚ_[p]), 0; 0, 1]
```
#### Proof sketch
`thetaInt` unfold; `toMatrix_etaAdelic' ℚ D v γ hγ ϖ (valued_natCast_p_le_one p) (natCast_p_ne_zero p)`
(Slash/Quaternionic.lean:125) with any `γ < 1` (e.g. `(Multiplicative.ofAdd (-1 : ℤ) : …)`, `by decide`
as in Weight/Quaternionic.lean:80); `Sigma0'.eta … = Matrix.of ![![ϖ, 0], ![0, 1]]` (Slash/Sigma0.lean:127);
`RingHom.mapMatrix_apply`, `Matrix.map` entrywise: `E.symm (p : Kp) = p` (`map_natCast`), `map_zero`, `map_one`;
`Matrix.ext`, `fin_cases`.
#### Sources
[LWX, §2.5] (`U_p = Iw_q (p 0; 0 1) Iw_q`); Slash/Quaternionic.lean:117–140.

### [Q8] `etaAdelic'_mem_levelM1`, `norm_thetaInt_etaAdelic'_zero_zero`
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:114, :126 | **Depends on**: Q7
- **Parallel**: no | **Type**: lemmas (2)
#### Statement
```lean
theorem etaAdelic'_mem_levelM1 :
    etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p) ∈ levelM1 (p := p) (thetaInt p D)
theorem norm_thetaInt_etaAdelic'_zero_zero :
    ‖thetaInt p D (etaAdelic' …) 0 0‖ ≤ (p : ℝ)⁻¹
```
#### Proof sketch
`levelM1 θ = (M1 p).comap θ`, `Submonoid.mem_comap`, Q7; `!![p,0;0,1] ∈ M1 p` (IntegralModel.lean:226):
entries `‖p‖ = p⁻¹ ≤ 1`, `‖0‖`, `‖1‖ = 1`; `‖c‖ = 0 ≤ p⁻¹`; `‖d‖ = 1`; `det = p ≠ 0`
(`Matrix.det_fin_two_of`, `padicNormE.norm_p`).  `(0,0)`-entry: `‖(p : ℚ_[p])‖ = p⁻¹`.
#### Sources
[LWX, §2.5]; IntegralModel.lean:226.

### [Q9] **MILESTONE — [LWX, Prop 2.17] for `D/ℚ`**
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:156 | **Depends on**: E18, Q5, Q6
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ (hp2 : p ≠ 2)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : Kp p} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (U : Subgroup (Dfx ℚ D)) (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))
    (vRep : Fin p → Dfx ℚ D) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) (thetaInt p D))
    (idx : ι → Fin p → ι) (u : ι → Fin p → U)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 (thetaInt p D) U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u hshape) ω
        (intHom (padicComparison p)) T₀
      = heckeCharPowerSeries (toMatrix ℚ D (padicPlace p))
          (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U
          (subset_levelMonoidOf_toMatrix p D U hU) 1 vRep
          (fun t => by
            have := mem_levelMonoidOf_thetaK (padicComparison p) (thetaInt p D) (hvΔ t)
            rwa [thetaK_thetaInt] at this) idx u
```
#### Proof sketch
`specCharSeries_ofCerts_eq_heckeCharPowerSeries hp2 (padicComparison p) (norm_padicComparison p) h0 h1 …`
(E18) at `θ := thetaInt p D`, then rewrite `thetaK (padicComparison p) (thetaInt p D)` to `toMatrix`
by Q5.  The dependent hypotheses (`hU'`, `hvΔ'`) transported along `thetaK_thetaInt` are propositions:
use `subst`-free transport — `heckeCharPowerSeries` depends on `hU`/`hvΔ` only through proofs, so
after `rw [thetaK_thetaInt]`/`simp only [thetaK_thetaInt]` the goal closes by `rfl` up to proof
irrelevance (`congr`/`convert … using 2` with `Subsingleton.elim`).
#### Sources
[LWX, Prop 2.17]; E18.

### [CLEANUP-ALL-2] /cleanup-all on the nine board files (before Q10)
- **Status**: done (2026-09-05 18:02: runLinter clean on all nine modules, 0 sorries, ≤100 cols, std axioms) | **Depends on**: Q9 and every earlier ticket — inline, file by file; runLinter each module.

### [Q10] **MILESTONE — the spectral reading at a halo point** ([LWX, Def 2.13] fibre)
- **Status**: done (finished 2026-09-05 18:02) | **File**: PhD/LWX/Quaternionic.lean:201 | **Depends on**: H4, H6, E16, Q8, Q9, CLEANUP-ALL-2
- **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem evalT_specCharSeries_eq_zero_iff … {a : Kp p} (ha0 : a ≠ 0) :
    PowerSeries.evalT a
        (specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u
            (isUpShape_certM1 (thetaInt p D) U hU vRep hvΔ u (etaAdelic'_mem_levelM1 p D)
              (norm_thetaInt_etaAdelic'_zero_zero p D) hv)) ω
          (intHom (padicComparison p)) T₀) = 0 ↔
      ∃ φ : FormsQ ℚ D (padicPlace p) (haloWeight …) U (subset_levelMonoidOf_toMatrix p D U hU),
        φ ≠ 0 ∧ heckeUpiQ ℚ D (padicPlace p) (haloWeight …) U … ((p : ℕ) : Kp p) (natCast_p_ne_zero p) (…) h φ = a⁻¹ • φ
```
#### Proof sketch
`rw [specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ …]` (Q9, with the `hshape` term of the
statement).  Then `QMF.Weight.evalT_heckeCharPowerSeries_eq_zero_iff (toMatrix ℚ D v) κ U hU' 1 c hc
hstab' hη h vRep hvΔ' hv hvinj idx d hd u hfact (σ := haloRho T₀) (hρσ := le_rfl) (hσ := haloRho_lt_one h1)
(hdet : ‖(toMatrix η).det‖ ≤ ρ) ha0` (Fredholm.lean:57), where `hdet`: `toMatrix η = (p 0; 0 1)`
(`toMatrix_etaAdelic'`, Q7's ingredient), `det = p`, `‖(p : Kp)‖ = p⁻¹ ≤ ρ` (Q3/Q4, W17 `inv_le_haloRho`);
`hstab'` (stabilisers act trivially) from `hstab` (`= ⊥`) as in `bijective_evalAtReps_of_stabilizer_eq_bot`
(Compact.lean:368): `w = 1`, `map_one`, `kappaSlash_one`, `one_smul`.  `heckeUpiQ … = heckeOperator …`
is `rfl` (Weight/Quaternionic.lean:64); `FormsQ = Forms` (`abbrev`).  The `χ = 1` twist: `heckeCharPowerSeries … 1`
matches (the QMF theorem is stated for a general `χ`; instantiate `χ := 1`).
#### Sources
[LWX, Def 2.13, lwx.txt:876–885] (zero locus of `Char(Up)`, slope map `x ↦ x⁻¹`); Fredholm.lean:57.

### [CL-Q3] /cleanup Quaternionic.lean — final (after Q10)
- **Status**: done (inline cleanup 2026-09-05 18:02: norm_natCast_p_Kp helper, docstrings, declaration order, header) | **File**: PhD/LWX/Quaternionic.lean | **Depends on**: Q10 — inline.

### [CLEANUP-FINAL] /cleanup-all on all nine board files; README notes
- **Status**: done (2026-09-05 18:04: all nine modules build, 0 sorries, runLinter clean, std axioms; README notes in PhD/QMF/README.md §5 and PhD/TateFredholm/README.md §11; lwx-halo plan.md deferred items 1 and 3 updated) | **Depends on**: every ticket above
- **Type**: cleanup — inline.  Also: append a "lwx-seam" paragraph to `PhD/QMF/README.md` §5
  ("Weight space / families" item 3: the halo weight is the first `AnalyticWeight` coming from a
  family; `heckeCharPowerSeries_eq_of_reps` + Prop 2.17 give the specialization half at `m = 1`)
  and a line in `PhD/TateFredholm/README.md` for `Conjugation.lean`; update
  `.mathlib-quality/lwx-halo/plan.md` §"Still deferred" items 1 and 3 with a pointer to this board.
