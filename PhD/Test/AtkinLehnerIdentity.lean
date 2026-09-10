/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.AtkinLehner
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# SCRATCH — experimenting with the Atkin–Lehner operator identity (hypothesis H1)

**This is a `PhD/Test/` scratch file.**  It is not imported by `PhD.lean` and is not part of any
board.  Sorries here are deliberate: this is where we try to discharge the one hypothesis the
`lwx-atkinlehner` board deliberately left open.

## The hypothesis

`PhD/LWX/AtkinLehner.lean` proves [LWX, Prop 3.22] *granted* the operator identity

  `U_p ∘ U'_p = p^{k+1}`  on `S^D_{k+2}(K^p Iw_{p^m}; ψ)`,   `ψ` of conductor exactly `p^m`,

where `U_p = [Iw η Iw]` with `η = diag(1,p)` and `U'_p = [Iw η' Iw]` with `η' = diag(p,1)`.
[LWX] proves Prop 3.22 by Jacquet–Langlands instead; see
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`.  No source stating the operator identity in the
quaternionic setting has been found, so it is not on the board.  This file is the sandbox for
finding a proof.

## What the local computation gives (all verified by hand, and the identities below are proved)

Coset representatives:

* `U_p`:  `η · (1,b;0,1) = (1, b; 0, p)` for `b` mod `p`      — `upRep b`
* `U'_p`: `η' · (1,0;c p^m,1) = (p, 0; c p^m, 1)` for `c` mod `p` — `upAdjRep m c`

Their product factors (`upRep_mul_upAdjRep`):

  `(1,b;0,p) · (p,0;c p^m,1) = (p,b;0,p) · (1,0;c p^m,1)`

The right factor `(1,0;c p^m,1)` lies in `Iw_{p^m}` (`lowerUni_mem_Iw`), so the whole product is
`obstruction b` times an Iwahori element, where `obstruction b = (p,b;0,p) = p · (1, b/p; 0, 1)`.

**The `b = 0` term is central** (`obstruction_zero`): `(p,0;0,p) = p · 1`.  Summing it over the `p`
values of `c` gives `p` copies of the central element `p`, which on `Sym^k` acts by `p^k`.  That is
where `p · p^k = p^{k+1}` comes from.  So the identity holds **iff the `b ≠ 0` terms cancel.**

## The mechanism for the `b ≠ 0` terms — this is the thing to make precise

Because `obstruction b = p · u(b/p)` with `u(x) = (1,x;0,1)` and `p` is central, one can move the
Iwahori element across (`obstruction_mul_lowerUni`, proved below):

  `obstruction b · (1, 0; c p^{h+2}, 1) = conjTwist b c h · obstruction b`

with

  `conjTwist b c h = ( 1 + b c p^{h+1} ,  −b² c p^h ;  c p^{h+2} ,  1 − b c p^{h+1} )`.

This matrix is again in `Iw_{p^{h+2}}` (`det_conjTwist` gives determinant exactly `1`; the entry
bounds are `conjTwist_mem_Iw`).  **Its diagonal entries are `1 ± b c p^{h+1}`**: congruent to `1`
modulo `p^{h+1}`, but as `c` runs over `ℤ/p` and `b` is a unit they run over *all* of
`1 + p^{h+1}ℤ / p^{h+2}`.

So the `b ≠ 0` part of `U_p U'_p` is, for each fixed `b`, a sum of `ψ` over a full coset of the
subgroup `1 + p^{m−1}ℤ_p` modulo `p^m`.  A character of conductor **exactly** `p^m` is by
definition non-trivial on that subgroup, so the sum vanishes by character orthogonality.  This is
the classical "`U_p` is invertible at ramified nebentypus".

Note the arithmetic: `conjTwist`'s `(0,1)` entry is `−b² c p^h`, which is integral only for
`m = h + 2 ≥ 2`.  That is not a defect — [LWX, §3.23] works at conductor `q² = p²`, i.e. `m = 2`,
so `m ≥ 2` is exactly the case needed.  The `m = 1` case would need a separate argument and is not
required.

## What is still missing

Everything above is about *matrices*.  Turning it into the operator identity needs the classical
space `S^D_{k+2}(K^p Iw_{p^m}; ψ)` and its `U_p`-action, which do not exist in Lean yet — they are
built by the theta layer on the companion board.  The "What remains" section at the end of this
file records exactly what that seam needs.

**Everything currently in this file is proved** — there are no sorries.  The two open steps are
written as prose at the end rather than as placeholder declarations, so that nothing here can be
mistaken for a discharged obligation.

## Next experiments to try

1. Prove that `c ↦ conjTwist b c h` composed with "read off the `(1,1)` entry" is injective modulo
   `p^{h+2}` when `b` is a unit — that is the input to character orthogonality.
2. State and prove the character-sum vanishing: for `χ : (ZMod (p^(h+2)))ˣ →* ℂˣ` non-trivial on
   `1 + p^{h+1}`, the sum over `c : ZMod p` of `χ (1 − b c p^{h+1})` is `0`.  This is pure finite
   group theory and needs none of the automorphic setup — a good self-contained target.
3. Only then attach it to the forms.
-/

namespace LWX.Test

open Matrix

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Coset representatives -/

variable (p) in
/-- Representative of the `b`-th `Iw`-coset in `Iw η Iw`, `η = diag(1,p)`. -/
noncomputable def upRep (b : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1, b; 0, (p : ℚ_[p])]

variable (p) in
/-- Representative of the `c`-th `Iw`-coset in `Iw η' Iw`, `η' = diag(p,1)`, at level `p ^ m`. -/
noncomputable def upAdjRep (m : ℕ) (c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(p : ℚ_[p]), 0; c * (p : ℚ_[p]) ^ m, 1]

variable (p) in
/-- `(p, b; 0, p) = p · (1, b/p; 0, 1)` — the non-central obstruction for `b ≠ 0`. -/
noncomputable def obstruction (b : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(p : ℚ_[p]), b; 0, (p : ℚ_[p])]

variable (p) in
/-- The lower unipotent `(1, 0; c p^m, 1)`, an element of `Iw_{p^m}`. -/
noncomputable def lowerUni (m : ℕ) (c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1, 0; c * (p : ℚ_[p]) ^ m, 1]

variable (p) in
/-- The conjugate `u(b/p) · (1,0;c p^{h+2},1) · u(b/p)⁻¹`, written without denominators.
Its diagonal is `1 ± b c p^{h+1}` — the source of the character sum. -/
noncomputable def conjTwist (b c : ℚ_[p]) (h : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1 + b * c * (p : ℚ_[p]) ^ (h + 1), -(b ^ 2 * c * (p : ℚ_[p]) ^ h);
     c * (p : ℚ_[p]) ^ (h + 2), 1 - b * c * (p : ℚ_[p]) ^ (h + 1)]

/-! ### The identities (all proved) -/

/-- **The key factorisation.**  A product of a `U_p`-coset representative and a `U'_p`-coset
representative is `obstruction b` times an element of `Iw_{p^m}`. -/
theorem upRep_mul_upAdjRep (m : ℕ) (b c : ℚ_[p]) :
    upRep p b * upAdjRep p m c = obstruction p b * lowerUni p m c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upRep, upAdjRep, obstruction, lowerUni, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The `b = 0` term is central**: this is where `p^{k+1}` comes from. -/
theorem obstruction_zero : obstruction p 0 = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [obstruction]

/-- **The conjugation identity.**  Moving the Iwahori element across the obstruction replaces it by
`conjTwist`, whose diagonal entries vary with `c`. -/
theorem obstruction_mul_lowerUni (b c : ℚ_[p]) (h : ℕ) :
    obstruction p b * lowerUni p (h + 2) c = conjTwist p b c h * obstruction p b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [obstruction, lowerUni, conjTwist, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

/-- `conjTwist` has determinant exactly `1`. -/
theorem det_conjTwist (b c : ℚ_[p]) (h : ℕ) : (conjTwist p b c h).det = 1 := by
  rw [conjTwist, Matrix.det_fin_two_of]
  ring

/-- The lower unipotent lies in the Iwahori subgroup. -/
theorem lowerUni_mem_Iw (m : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) : lowerUni p m c ∈ Iw p m := by
  have hP : ‖((p : ℚ_[p]) ^ m)‖ = (p : ℝ)⁻¹ ^ m := by rw [norm_pow, Padic.norm_p]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : ((p : ℝ))⁻¹ ^ m ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
  have e10 : ‖lowerUni p m c 1 0‖ ≤ (p : ℝ)⁻¹ ^ m := by
    have hentry : lowerUni p m c 1 0 = c * (p : ℚ_[p]) ^ m := by simp [lowerUni]
    rw [hentry, norm_mul, hP]
    calc ‖c‖ * (p : ℝ)⁻¹ ^ m ≤ 1 * (p : ℝ)⁻¹ ^ m := by gcongr
      _ = (p : ℝ)⁻¹ ^ m := one_mul _
  refine ⟨fun i j => ?_, e10, ?_⟩
  · fin_cases i <;> fin_cases j
    · simp [lowerUni]
    · simp [lowerUni]
    · exact e10.trans hp1
    · simp [lowerUni]
  · rw [lowerUni, Matrix.det_fin_two_of]
    simp

/-- The `(1,1)` entry of `conjTwist` — the diagonal entry the nebentypus sees. -/
theorem diag_conjTwist (b c : ℚ_[p]) (h : ℕ) :
    conjTwist p b c h 1 1 = 1 - b * c * (p : ℚ_[p]) ^ (h + 1) := by
  simp [conjTwist]

/-- **The injectivity content, in closed form.**  Two values of `c` give diagonal entries differing
by exactly `-b (c₁ - c₂) p^{h+1}`.  For `b` a unit and `c₁ - c₂` a unit this has norm
`p^{-(h+1)}`, so the two entries are *not* congruent modulo `p^{h+2}`: as `c` runs over
representatives mod `p`, the diagonal runs over a full coset of `1 + p^{h+1}` modulo `p^{h+2}`.
That is exactly the hypothesis character orthogonality needs. -/
theorem diag_conjTwist_sub (b c₁ c₂ : ℚ_[p]) (h : ℕ) :
    conjTwist p b c₁ h 1 1 - conjTwist p b c₂ h 1 1
      = -(b * (c₁ - c₂) * (p : ℚ_[p]) ^ (h + 1)) := by
  simp [conjTwist]
  ring

/-- The norm form of the previous lemma: for `b` and `c₁ - c₂` units the diagonal entries differ by
exactly `p^{-(h+1)}`, hence are distinct modulo `p^{h+2}`. -/
theorem norm_diag_conjTwist_sub (b c₁ c₂ : ℚ_[p]) (h : ℕ) (hb : ‖b‖ = 1) (hc : ‖c₁ - c₂‖ = 1) :
    ‖conjTwist p b c₁ h 1 1 - conjTwist p b c₂ h 1 1‖ = (p : ℝ)⁻¹ ^ (h + 1) := by
  rw [diag_conjTwist_sub, norm_neg, norm_mul, norm_mul, hb, hc, norm_pow, Padic.norm_p]
  ring

/-- `conjTwist` lies in the Iwahori subgroup at level `p^{h+2}`. -/
theorem conjTwist_mem_Iw (b c : ℚ_[p]) (h : ℕ) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    conjTwist p b c h ∈ Iw p (h + 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hpinv : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hpow : ∀ k : ℕ, ‖((p : ℚ_[p]) ^ k)‖ = (p : ℝ)⁻¹ ^ k := fun k => by
    rw [norm_pow, Padic.norm_p]
  have hpow1 : ∀ k : ℕ, ((p : ℝ))⁻¹ ^ k ≤ 1 := fun k => pow_le_one₀ (by positivity) hpinv
  have key : ∀ (x : ℚ_[p]) (k : ℕ), ‖x‖ ≤ 1 → ‖x * (p : ℚ_[p]) ^ k‖ ≤ (p : ℝ)⁻¹ ^ k := by
    intro x k hx
    rw [norm_mul, hpow]
    calc ‖x‖ * (p : ℝ)⁻¹ ^ k ≤ 1 * (p : ℝ)⁻¹ ^ k := by gcongr
      _ = (p : ℝ)⁻¹ ^ k := one_mul _
  have e10 : ‖conjTwist p b c h 1 0‖ ≤ (p : ℝ)⁻¹ ^ (h + 2) := by
    have hentry : conjTwist p b c h 1 0 = c * (p : ℚ_[p]) ^ (h + 2) := by simp [conjTwist]
    rw [hentry]; exact key c _ hc
  refine ⟨fun i j => ?_, e10, ?_⟩
  · fin_cases i <;> fin_cases j
    · show ‖1 + b * c * (p : ℚ_[p]) ^ (h + 1)‖ ≤ 1
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
      exact (key (b * c) _ (by rw [norm_mul]; exact mul_le_one₀ hb (norm_nonneg _) hc)).trans
        (hpow1 _)
    · show ‖-(b ^ 2 * c * (p : ℚ_[p]) ^ h)‖ ≤ 1
      rw [norm_neg]
      refine (key (b ^ 2 * c) _ ?_).trans (hpow1 _)
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _) hc
    · exact e10.trans (hpow1 _)
    · show ‖1 - b * c * (p : ℚ_[p]) ^ (h + 1)‖ ≤ 1
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
      rw [norm_neg]
      exact (key (b * c) _ (by rw [norm_mul]; exact mul_le_one₀ hb (norm_nonneg _) hc)).trans
        (hpow1 _)
  · rw [det_conjTwist]; simp

/-! ### What remains

Both remaining steps are recorded here rather than stated as Lean theorems, because neither can be
written down until the classical space exists in Lean.  Stating them as `True` placeholders would
be misleading.

**Step 1 — the character sum. DONE** (`sum_diagUnit_eq_zero`).
Let `χ` be a character of `(ZMod (p ^ (h + 2)))ˣ` whose restriction to the subgroup
`1 + p^(h+1) ZMod (p^(h+2))` is non-trivial — equivalently, `χ` has conductor exactly `p^(h+2)`.
Then for every unit `b`,

    ∑ c : ZMod p, χ (1 - b * c * p^(h+1)) = 0.

Proved as `sum_diagUnit_eq_zero`.  The route: `p · π = 0` makes `1 - b c π` depend only on `c`
modulo `p`, and `π² = 0` makes it a unit and makes `c ↦ 1 - b c π` multiplicative.  So it is an
additive character of `ZMod p`, and `AddChar.sum_eq_zero_of_ne_one` finishes.
`norm_diag_conjTwist_sub` is the matrix-side counterpart: distinct `c` mod `p` give diagonal
entries differing by exactly `p^{-(h+1)}` in norm, hence distinct mod `p^{h+2}`.

**Step 2 — attaching it to the forms.  THE ONLY REMAINING STEP.**
With Step 1 now proved, `upRep_mul_upAdjRep` + `obstruction_mul_lowerUni` + `obstruction_zero` give

    U_p ∘ U'_p  =  (b = 0 part)  +  (b ≠ 0 part)
                =  p · (central action of p)  +  0
                =  p^{k+1}.

This needs `S^D_{k+2}(K^p Iw_{p^m}; ψ)` and its `U_p`-action, which the theta layer on the
companion board supplies.  Until then the identity stays a hypothesis in
`PhD/LWX/AtkinLehner.lean`.
-/

/-! ## Step 1 — the character sum

The self-contained finite-group-theory half, done here.  Nothing below mentions matrices,
Iwahori subgroups or automorphic forms: it is a statement about `ZMod (p ^ (h + 2))`.

Writing `π = p^(h+1)`, the point is that `π² = 0` and `p · π = 0` in `ZMod (p^(h+2))`.  The first
makes `1 - b c π` a unit with inverse `1 + b c π`, and makes `c ↦ 1 - b c π` multiplicative; the
second makes it depend only on `c` modulo `p`.  So it is an additive character of `ZMod p`, and a
non-trivial additive character sums to zero. -/

section CharacterSum

variable {R : Type*} [CommRing R] [IsDomain R]

variable (p) in
/-- `π = p^(h+1)` in `ZMod (p^(h+2))`: the level at which the nebentypus must be non-trivial. -/
def levelPi (h : ℕ) : ZMod (p ^ (h + 2)) := (p : ZMod (p ^ (h + 2))) ^ (h + 1)

variable (p) in
/-- `p · π = 0`: this is why `1 - b c π` depends only on `c` modulo `p`. -/
theorem p_mul_levelPi (h : ℕ) : (p : ZMod (p ^ (h + 2))) * levelPi p h = 0 := by
  have hz : ((p ^ (h + 2) : ℕ) : ZMod (p ^ (h + 2))) = 0 := ZMod.natCast_self _
  rw [Nat.cast_pow] at hz
  rw [levelPi, ← pow_succ']
  exact hz

variable (p) in
/-- `π² = 0`: this is why `1 - b c π` is a unit and why the map is multiplicative. -/
theorem levelPi_sq (h : ℕ) : levelPi p h * levelPi p h = 0 := by
  have hz : ((p ^ (h + 2) : ℕ) : ZMod (p ^ (h + 2))) = 0 := ZMod.natCast_self _
  rw [Nat.cast_pow] at hz
  have hsplit : levelPi p h * levelPi p h
      = (p : ZMod (p ^ (h + 2))) ^ (h + 2) * (p : ZMod (p ^ (h + 2))) ^ h := by
    rw [levelPi, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hsplit, hz, zero_mul]

variable (p) in
/-- The unit `1 - b c p^{h+1}` of `ZMod (p^{h+2})`.  It is a unit because the perturbation squares
to zero, so `(1 - x)(1 + x) = 1`. -/
def diagUnit (h : ℕ) (b : ZMod (p ^ (h + 2))) (c : ZMod p) : (ZMod (p ^ (h + 2)))ˣ where
  val := 1 - b * (c.val : ZMod (p ^ (h + 2))) * levelPi p h
  inv := 1 + b * (c.val : ZMod (p ^ (h + 2))) * levelPi p h
  val_inv := by
    have hx : (b * (c.val : ZMod (p ^ (h + 2))) * levelPi p h) ^ 2 = 0 := by
      rw [mul_pow, sq (levelPi p h), levelPi_sq, mul_zero]
    linear_combination -hx
  inv_val := by
    have hx : (b * (c.val : ZMod (p ^ (h + 2))) * levelPi p h) ^ 2 = 0 := by
      rw [mul_pow, sq (levelPi p h), levelPi_sq, mul_zero]
    linear_combination -hx

@[simp]
theorem diagUnit_val (h : ℕ) (b : ZMod (p ^ (h + 2))) (c : ZMod p) :
    (diagUnit p h b c : ZMod (p ^ (h + 2)))
      = 1 - b * (c.val : ZMod (p ^ (h + 2))) * levelPi p h := rfl

variable (p) in
/-- The cast of `c.val` into `ZMod (p^{h+2})` only matters modulo `p` after multiplying by `π`. -/
theorem val_add_cast_mul_levelPi (h : ℕ) (c₁ c₂ : ZMod p) :
    (((c₁ + c₂).val : ℕ) : ZMod (p ^ (h + 2))) * levelPi p h
      = ((c₁.val : ℕ) + (c₂.val : ℕ) : ℕ) * levelPi p h := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hmod : (c₁ + c₂).val = (c₁.val + c₂.val) % p := ZMod.val_add _ _
  have hdiv : (c₁.val + c₂.val) % p + p * ((c₁.val + c₂.val) / p) = c₁.val + c₂.val :=
    Nat.mod_add_div _ _
  rw [hmod]
  have hcast : (((c₁.val + c₂.val : ℕ) : ZMod (p ^ (h + 2))))
      = (((c₁.val + c₂.val) % p : ℕ) : ZMod (p ^ (h + 2)))
        + (p : ZMod (p ^ (h + 2))) * (((c₁.val + c₂.val) / p : ℕ) : ZMod (p ^ (h + 2))) := by
    conv_lhs => rw [← hdiv]
    push_cast
    ring
  rw [hcast]
  linear_combination (-((((c₁.val + c₂.val) / p : ℕ) : ZMod (p ^ (h + 2))))) * p_mul_levelPi p h

variable (p) in
/-- `c ↦ 1 - b c π` is multiplicative in `c`. -/
theorem diagUnit_add (h : ℕ) (b : ZMod (p ^ (h + 2))) (c₁ c₂ : ZMod p) :
    diagUnit p h b (c₁ + c₂) = diagUnit p h b c₁ * diagUnit p h b c₂ := by
  refine Units.ext ?_
  have hsq : levelPi p h * levelPi p h = 0 := levelPi_sq p h
  have hval := val_add_cast_mul_levelPi p h c₁ c₂
  push_cast at hval
  simp only [diagUnit_val, Units.val_mul]
  linear_combination -b * hval
    - (b * (c₁.val : ZMod (p ^ (h + 2))) * (b * (c₂.val : ZMod (p ^ (h + 2))))) * hsq

variable (p) in
/-- **The additive character.**  `c ↦ χ (1 - b c p^{h+1})` is an additive character of `ZMod p`. -/
noncomputable def diagChar (h : ℕ) (b : ZMod (p ^ (h + 2)))
    (χ : (ZMod (p ^ (h + 2)))ˣ →* Rˣ) : AddChar (ZMod p) R where
  toFun c := (χ (diagUnit p h b c) : R)
  map_zero_eq_one' := by
    have h0 : diagUnit p h b 0 = 1 := by
      refine Units.ext ?_
      rw [diagUnit_val, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_mul, sub_zero,
        Units.val_one]
    rw [h0, map_one, Units.val_one]
  map_add_eq_mul' c₁ c₂ := by
    rw [diagUnit_add, map_mul, Units.val_mul]

@[simp]
theorem diagChar_apply (h : ℕ) (b : ZMod (p ^ (h + 2))) (χ : (ZMod (p ^ (h + 2)))ˣ →* Rˣ)
    (c : ZMod p) : diagChar p h b χ c = (χ (diagUnit p h b c) : R) := rfl

variable (p) in
/-- **STEP 1, PROVED.**  If the nebentypus `χ` is non-trivial on the subgroup
`1 + p^{h+1} ZMod (p^{h+2})` — equivalently, if `χ` has conductor exactly `p^{h+2}` — then for
every `b` the character sum over `c` vanishes.  This is what kills the `b ≠ 0` terms of
`U_p ∘ U'_p` and leaves only the central `b = 0` term `p^{k+1}`. -/
theorem sum_diagUnit_eq_zero (h : ℕ) (b : ZMod (p ^ (h + 2)))
    (χ : (ZMod (p ^ (h + 2)))ˣ →* Rˣ)
    (hnt : ∃ c : ZMod p, (χ (diagUnit p h b c) : R) ≠ 1) :
    ∑ c : ZMod p, (χ (diagUnit p h b c) : R) = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hne : diagChar p h b χ ≠ 1 := by
    obtain ⟨c, hc⟩ := hnt
    exact AddChar.ne_one_iff.2 ⟨c, by simpa using hc⟩
  simpa using AddChar.sum_eq_zero_of_ne_one hne

end CharacterSum

end LWX.Test
