/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Level
import PhD.QMF.UpiElement

/-!
# Lemma 2.3: the double-coset decomposition of `U η₃ U`

[Jacobs, Lemma 2.3 p. 25]:

> "Write G = {(a b; c d) ∈ GL₂(Z₃) : (a b; c d) ≡ (∗ ∗; 0 1) mod 9}.  Then
> G (3 0; 0 1) G = G (3 0; 0 1) ⊔ G (3 0; 9 1) ⊔ G (3 0; 18 1)."

The thesis marks the proof "elementary" and omits it; the expansion (recorded in
`decomposition.md` R2) is: `(3 0; 9t 1) = (3 0; 0 1)·(1 0; 3t 1) … = u·η·u'` with
`u' = (1 0; 9t 1) ∈ G`, disjointness because `v_s v_t⁻¹ = (1 0; 3(s−t) 1) ∈ G` iff
`s ≡ t mod 3`, and covering by the mod-`27` analysis of the lower-left entry.

The `QMF` library forms the Hecke sum over the image of `U·{η}` in the *left* quotient
`G ⧸ U` (cosets `w·U`), so the decomposition is stated in that form; it is the thesis's
statement transported by the adjugate anti-isomorphism (which swaps the two coset sides
and carries the right-handed `η = (3 0; 0 1)` to the library's `eta = (1 0; 0 3)`).

This is the clearest place the handedness bites: the *sides* of the coset decomposition
are exchanged, so `⊔ₜ G·vₜ` (thesis) becomes `⊔ₜ wₜ·U` (here), and the `wₜ` must be
recomputed rather than copied.  The reason the library is left-handed, and the reason the
adjugate — rather than `g ↦ g⁻¹`, which does not exist on the monoid `Σ₀` precisely
because `η` is not invertible in it — is the bridge, is documented in
`PhD/QMF/Sigma0.lean`'s header.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped Pointwise

namespace Jacobs.U3

/-- The uniformiser `3` of `K₃`, as the `Sigma0.eta` datum. -/
noncomputable def pi3 : K₃ := (3 : K₃)

theorem valued_pi3_le_one : Valued.v pi3 ≤ 1 := sorry

theorem pi3_ne_zero : pi3 ≠ 0 := sorry

/-- The adelic Hecke element `η₃` [Jacobs, p. 24: "`η₃,q = 1` if `q ≠ 3`,
`(3 0; 0 1)` if `q = 3`"], in the library's left-handed normalisation
(`v`-component `eta = (1 0; 0 3)`). -/
noncomputable def eta3 : Dfx ℚ D := etaAdelic ℚ D v₃ pi3 pi3_ne_zero

theorem eta3_mem_levelMonoid : eta3 ∈ levelMonoid ℚ D v₃ γ₉ γ₉_lt_one :=
  sorry

/-- The left-coset representatives `w_t` of `U·η₃·U`: `3`-component
`(1 0; 0 3)·(1 3t 0 1)`-form (the adjugate transport of the thesis's
`v_t = (3 0; 9t 1)`), trivial elsewhere. -/
noncomputable def etaRep : Fin 3 → Dfx ℚ D := sorry

theorem etaRep_mem_levelMonoid (t : Fin 3) :
    etaRep t ∈ levelMonoid ℚ D v₃ γ₉ γ₉_lt_one := sorry

/-- The `3`-components of the representatives lie in `Σ₁(9)`. -/
theorem toMatrix_etaRep_mem_sigma1 (t : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t) ∈ Sigma1 := sorry

/-- **[Jacobs, Lemma 2.3]**, adelic left-coset form: the image of `U₁(9)·{η₃}` in
`D_f^× ⧸ U₁(9)` is exactly the three classes of the `etaRep t`, and these are pairwise
distinct.  (Bijectivity form consumed by `heckeOperator_eq_finsetSum` /
`heckeOperator_apply_rep`.) -/
theorem bijOn_etaRep :
    Set.BijOn QuotientGroup.mk (Set.range etaRep)
      (QuotientGroup.mk '' ((U1_9 : Set (Dfx ℚ D)) * {eta3}) :
        Set (Dfx ℚ D ⧸ U1_9)) := sorry

theorem etaRep_injective : Function.Injective etaRep := sorry

/-- The finiteness input for `QMF.heckeOperator` at `η₃`, discharged by the explicit
decomposition (no adelic topology needed). -/
theorem finite_image_eta3 :
    (QuotientGroup.mk '' ((U1_9 : Set (Dfx ℚ D)) * {eta3}) :
      Set (Dfx ℚ D ⧸ U1_9)).Finite := sorry

end Jacobs.U3
