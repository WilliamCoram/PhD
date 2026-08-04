import PhD.TateFredholm.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Mock PR: generalise `ContinuousLinearMap.opNorm` away from field scalars

Mathlib defines the operator norm in `Mathlib/Analysis/Normed/Operator/Basic.lean` as

```
def opNorm (f : E →SL[σ₁₂] F) := sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
```

under `[NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E]
[NormedSpace 𝕜₂ F]`.  The formula mentions none of those: it needs a scalar semiring for
`E →SL[σ] F` to typecheck and seminorms on `E` and `F` to state the bound.  The field
hypotheses are load-bearing only from `bounds_nonempty` onwards, where continuity has to
be turned into boundedness.

This file is the proposed generalisation, written as it would appear in Mathlib.  In the
real PR everything below replaces the corresponding declarations in
`Mathlib/Analysis/Normed/Operator/Basic.lean` inside `namespace ContinuousLinearMap`;
here it lives in `MathlibPR` so that it can be compared with — rather than clash with —
the current definitions.  Semilinearity (`σ`) is kept throughout.

The pay-off is at the bottom of the file: the generalised `Norm` instance is
*definitionally* both Mathlib's `ContinuousLinearMap.hasOpNorm` (over a normed field) and
this project's `TateFredholm.instNorm` (over a Banach–Tate ring), so the PR lets the
project delete its own instance instead of maintaining a second `Norm` on the same type.

Reference for the Tate side: [JN] Definition 2.1.4, [Bel] II.1.1; see
`PhD/TateFredholm/OperatorNorm.lean`.
-/

open Set

noncomputable section

namespace MathlibPR

/-! ### Semiring scalars

The definition and everything that follows from it by order theory alone. -/

section SemiringScalars

variable {R S E F : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def opNorm (f : E →SL[σ] F) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}

scoped instance hasOpNorm : Norm (E →SL[σ] F) :=
  ⟨opNorm⟩

theorem norm_def (f : E →SL[σ] F) : ‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  rfl

/-- The set of bounds is bounded below by `0`.  (Mathlib's proof verbatim; it never used
the field structure.) -/
theorem bounds_bddBelow {f : E →SL[σ] F} :
    BddBelow {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem opNorm_le_bound (f : E →SL[σ] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

theorem opNorm_nonneg (f : E →SL[σ] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ => And.left

/-- The norm of the `0` operator is `0`. -/
@[simp] theorem opNorm_zero : ‖(0 : E →SL[σ] F)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun _ => by simp) (opNorm_nonneg _)

theorem opNorm_eq_of_bounds {φ : E →SL[σ] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (opNorm_le_bound φ M_nonneg h_above)
    ((le_csInf_iff bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`.  Mathlib's proof is pure topology
(`mem_closure_zero_iff_norm` + `map_zero`), so it never needed the field either — this is
what lets the degenerate case of a *seminorm* be handled without any scaling. -/
theorem norm_image_of_norm_eq_zero (f : E →SL[σ] F) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map f.continuous

theorem opNorm_le_bound' (f : E →SL[σ] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f h, le_refl]

theorem norm_id_le : ‖ContinuousLinearMap.id R E‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

end SemiringScalars

/-! ### Ring scalars

Negation and subtraction of continuous linear maps are `Ring`-scalar notions in Mathlib
(`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`, `section Ring`), so
the lemmas that mention them ask for that much and no more. -/

section RingScalars

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]

@[simp] theorem opNorm_neg (f : E →SL[σ] F) : ‖-f‖ = ‖f‖ := by
  simp only [norm_def, neg_apply, norm_neg]

/-- New: Mathlib currently gets this from the `SeminormedAddCommGroup` structure on the
hom space, which is unavailable at this generality. -/
theorem opNorm_sub_rev (f g : E →SL[σ] F) : ‖f - g‖ = ‖g - f‖ := by
  rw [← opNorm_neg, neg_sub]

end RingScalars

/-! ### The next tier: continuity ⇒ boundedness

`bounds_nonempty` is where the scalars start to matter: it says the bound set is
inhabited, i.e. that a continuous linear map is bounded.  Over a normed field that is
`ContinuousLinearMap.bound`; over a Banach–Tate ring it is `TateFredholm.le_opNorm`,
proved by `ϖ`-scaling.

These are *not* two parallel arguments.  Both scale a vector into a shell by a unit of
controlled norm and unscale afterwards, and the field case is an instance of the Tate
one: every `NontriviallyNormedField` is `IsTate` (the instance `TateFredholm.instIsTate`), so
`le_opNorm` applies verbatim to a normed space over a normed field — see the `example`
in the `Field` section below, which is a proof of Mathlib's statement.  So this tier
generalises too, on hypotheses `[NormedRing R] [NormOneClass R] [IsTate R]` together
with `[Module R M] [IsBoundedSMul R M]`: no commutativity (verified by rebuilding
`OperatorNorm.lean` with `NormedRing` in place of `NormedCommRing`), and `IsBoundedSMul`
in place of `NormedSpace`, exactly as in the tiers above.

Two gaps remain before this tier could replace Mathlib's:

* **Seminormed modules.**  `le_opNorm` currently needs `NormedAddCommGroup`, because it
  argues by cases on `‖y‖ = 0` via `norm_pos_iff`.  This is a small edit rather than new
  mathematics: the degenerate case needs no scaling at all, since
  `norm_image_of_norm_eq_zero` above gives `‖u y‖ = 0` from continuity alone (pure
  topology, tier 1), leaving the shell argument to handle only `0 < ‖y‖`.
* **Semilinearity.**  For `f : M →SL[σ] N` the unscaling happens in `N` against
  `σ(ϖ)`, and one needs `‖σ(ϖ)⁻¹ • w‖ = ‖σ(ϖ)‖⁻¹ ‖w‖`.  Submultiplicativity gives only
  `‖a⁻¹‖ ≥ ‖a‖⁻¹`, the wrong direction, so `RingHomIsometric σ` alone is not enough:
  one needs `σ` to carry pseudo-uniformizers to pseudo-uniformizers.  Over a field that
  is automatic (the norm is multiplicative); over a Tate ring it is an extra hypothesis.

So the honest scope of the PR is: tiers 1 and 2 generalise, tier 2 modulo the two gaps
above; `isLeast_opNorm` and the `SeminormedAddCommGroup` structure on the hom space
follow tier 2. -/

section Field

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜₂ F] [RingHomIsometric σ]

/-- Over a normed field the generalised norm *is* Mathlib's, definitionally: the PR is a
hypothesis weakening, not a new definition. -/
example : (hasOpNorm : Norm (E →SL[σ] F)) = ContinuousLinearMap.hasOpNorm := rfl

example (f : E →SL[σ] F) : opNorm f = ContinuousLinearMap.opNorm f := rfl

/-- Hence Mathlib's proof of `bounds_nonempty` transfers unchanged. -/
example (f : E →SL[σ] F) : ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, hMp.le, hMb⟩

/-- Tier 2 is not field-specific: the Tate `ϖ`-scaling proof *is* a proof of Mathlib's
`le_opNorm` over a normed field, via the `IsTate` instance.  (`σ = RingHom.id` and
normed — not seminormed — modules; those are the two gaps listed above.) -/
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  TateFredholm.le_opNorm f x

end Field

section BanachTate

open TateFredholm

variable {R M N : Type*} [NormedCommRing R] [NormOneClass R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Over a Banach–Tate ring the generalised norm is this project's `instNorm`, again
definitionally — so the PR would let `PhD/TateFredholm/OperatorNorm.lean` drop its own
`Norm` instance and the duplicated `norm_def` / `opNorm_nonneg` / `opNorm_le_of_forall` /
`opNorm_zero` / `opNorm_neg` / `opNorm_sub_comm`. -/
example : (hasOpNorm : Norm (M →L[R] N)) = TateFredholm.instNorm := rfl

example (u : M →L[R] N) : opNorm u = ‖u‖ := rfl

/-- And the analytic input that replaces `ContinuousLinearMap.bound` is `le_opNorm`,
i.e. `ϖ`-scaling — the Tate half of `bounds_nonempty`. -/
example [IsTate R] (u : M →L[R] N) : ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} :=
  ⟨‖u‖, opNorm_nonneg u, fun x => le_opNorm u x⟩

end BanachTate

end MathlibPR

end
