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

/-! ### What stays behind

`bounds_nonempty` is where the scalars start to matter: it says the bound set is
inhabited, i.e. that a continuous linear map is bounded.  Over a normed field that is
`ContinuousLinearMap.bound`; over a Banach–Tate ring it is `TateFredholm.le_opNorm`,
proved by `ϖ`-scaling.  There is no common generalisation, so this lemma and everything
downstream of it (`isLeast_opNorm`, the `SeminormedAddCommGroup` structure on the hom
space, …) keep their present hypotheses in the PR.

The two instantiations below are the point of the exercise. -/

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
