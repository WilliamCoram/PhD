/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.Fredholm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# The Hecke algebra acting on `S_κ(U)`

[Buzzard, *Eigenvarieties*, §5 p. 33] takes the commuting structure as **data**:

> "Let us now go back to our more general situation, where `M` is a Banach `R`-module satisfying
> property (Pr) and `T` is a commutative `R`-algebra equipped with an `R`-algebra map
> `T → End_R(M)`, such that the endomorphism of `M` induced by `φ ∈ T` is compact."

so this file does the same: a commutative `R`-algebra `𝕋` acting on `Forms`, with a distinguished
compact `φ = [UηU]`.  What is *proved* here is what the eigenvariety machine consumes from that
datum: everything in `𝕋` preserves the Riesz finite-slope subspace `N` (it commutes with `φ`), so
`N` carries a system of eigenvalues.

Commutativity of individual Hecke operators is **not** proved (Buzzard does not prove it either;
for `T_v`, `T_w` at distinct places it is the Satake/Gelfand argument).  What is available is the
abstract criterion `heckeOperatorSlash_comm_of_reps`: two double-coset operators commute when
their representative families can be matched pairwise up to the level.

## Main declarations

* `AutomorphicFunction.heckeOperatorSlash_comm_of_reps` — the abstract commutation criterion.
* `QMF.Weight.mapsTo_ker_of_commute` — an operator commuting with `[UηU]` preserves the kernel of
  `(1 − a·[UηU])^n`, i.e. the Riesz finite-slope subspace.
* `QMF.Weight.exists_common_eigenvector` — a commuting family on a nonzero finite-dimensional
  space over an algebraically closed field has a common generalised eigenvector.
* `QMF.Weight.exists_eigensystem_of_riesz` — **the milestone**: a system of eigenvalues on the
  finite-slope subspace produced by `exists_riesz_decomposition_forms`.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace AutomorphicFunction

open AbstractHeckeOperatorSlash RightSlashAction

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {Δ' : Submonoid G} {U : Subgroup G}
variable {A : Type*} [AddCommGroup A] [RightSlashAction Δ' A] [Module R A]
  [RightSlashAction.SMulSlashClass R Δ' A]
variable (hU : (U : Set G) ⊆ Δ')

/-- **Abstract commutation criterion for double-coset operators**: if the representative
families `s` (for `UgU`) and `s'` (for `Ug'U`) can be matched by a bijection `e` of `s ×ˢ s'`
with itself such that `x * y` and `e (x, y).2 * e (x, y).1` act identically on the level, the
two Hecke operators commute.  (Buzzard takes commutativity as data — [*Eigenvarieties*, §5
p. 33]; this criterion is what a Satake-style argument would discharge.) -/
theorem heckeOperatorSlash_comm_of_reps {g g' : G} (hg : g ∈ Δ') (hg' : g' ∈ Δ')
    (h : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (h' : (((Quotient.mk'' : G → RightCosets U) '' ({g'} * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (s s' : Finset G) (hsΔ : (s : Set G) ⊆ Δ') (hs'Δ : (s' : Set G) ⊆ Δ')
    (hs : Set.BijOn (Quotient.mk'' : G → RightCosets U) (s : Set G)
      (((Quotient.mk'' : G → RightCosets U) '' ({g} * (U : Set G))) : Set (RightCosets U)))
    (hs' : Set.BijOn (Quotient.mk'' : G → RightCosets U) (s' : Set G)
      (((Quotient.mk'' : G → RightCosets U) '' ({g'} * (U : Set G))) : Set (RightCosets U)))
    (e : s ×ˢ s' ≃ s ×ˢ s')
    (he : ∀ p : (s ×ˢ s' : Finset (G × G)), ∀ a : A,
      a ∣ₛ (⟨(p : G × G).1 * (p : G × G).2, Δ'.mul_mem (hsΔ (Finset.mem_product.mp p.2).1)
          (hs'Δ (Finset.mem_product.mp p.2).2)⟩ : Δ')
        = a ∣ₛ (⟨((e p : G × G)).2 * ((e p : G × G)).1,
          Δ'.mul_mem (hs'Δ (Finset.mem_product.mp (e p).2).2)
            (hsΔ (Finset.mem_product.mp (e p).2).1)⟩ : Δ'))
    (a : slashFixedPointsOfLE R A hU) :
    heckeOperatorSlash R hU hU hg h (heckeOperatorSlash R hU hU hg' h' a)
      = heckeOperatorSlash R hU hU hg' h' (heckeOperatorSlash R hU hU hg h a) := by
  classical
  -- The slash by an element of `G`, extended by `0` off `Δ'`, so that both double sums can be
  -- taken over the honest finsets `s`, `s'` instead of their `attach`ed subtypes.
  set F : G → A := fun z => if hz : z ∈ Δ' then (a : A) ∣ₛ (⟨z, hz⟩ : Δ') else 0 with hF
  have hFapply : ∀ {z : G} (hz : z ∈ Δ'), F z = (a : A) ∣ₛ (⟨z, hz⟩ : Δ') := fun hz => dif_pos hz
  -- Expanding twice: `[UgU]([Ug'U]a) = ∑_{y ∈ s} ∑_{x ∈ s'} a ∣ₛ (x * y)`.
  have hexp : ∀ (t t' : Finset G) (htΔ : (t : Set G) ⊆ Δ') (ht'Δ : (t' : Set G) ⊆ Δ')
      {k k' : G} (hk : k ∈ Δ') (hk' : k' ∈ Δ')
      (hfin : (((Quotient.mk'' : G → RightCosets U) '' ({k} * (U : Set G))) :
        Set (RightCosets U)).Finite)
      (hfin' : (((Quotient.mk'' : G → RightCosets U) '' ({k'} * (U : Set G))) :
        Set (RightCosets U)).Finite),
      Set.BijOn (Quotient.mk'' : G → RightCosets U) (t : Set G)
        (((Quotient.mk'' : G → RightCosets U) '' ({k} * (U : Set G))) : Set (RightCosets U)) →
      Set.BijOn (Quotient.mk'' : G → RightCosets U) (t' : Set G)
        (((Quotient.mk'' : G → RightCosets U) '' ({k'} * (U : Set G))) : Set (RightCosets U)) →
      ((heckeOperatorSlash R hU hU hk hfin (heckeOperatorSlash R hU hU hk' hfin' a) : _) : A)
        = ∑ y ∈ t, ∑ x ∈ t', F (x * y) := by
    intro t t' htΔ ht'Δ k k' hk hk' hfin hfin' ht ht'
    rw [heckeOperatorSlash_eq_finsetSum R hU hU hk hfin _ t htΔ ht,
      ← Finset.sum_attach t fun y => ∑ x ∈ t', F (x * y)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [heckeOperatorSlash_eq_finsetSum R hU hU hk' hfin' a t' ht'Δ ht',
      ← slashAddHom_apply (Δ := Δ'), map_sum,
      ← Finset.sum_attach t' fun x => F (x * y.1)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [slashAddHom_apply, hFapply (Δ'.mul_mem (ht'Δ x.2) (htΔ y.2)),
      subtype_slash_mul (a : A) (ht'Δ x.2) (htΔ y.2)]
  refine Subtype.ext ?_
  rw [hexp s s' hsΔ hs'Δ hg hg' h h' hs hs', hexp s' s hs'Δ hsΔ hg' hg h' h hs' hs,
    Finset.sum_comm (s := s') (t := s) (f := fun x y => F (y * x))]
  -- Both sides are now sums over `s ×ˢ s'`; the pairing `e` matches them term by term.
  rw [← Finset.sum_product' (f := fun y x => F (x * y)),
    ← Finset.sum_product' (f := fun y x => F (y * x)),
    ← Finset.sum_attach (s ×ˢ s') fun p => F (p.2 * p.1),
    ← Finset.sum_attach (s ×ˢ s') fun p => F (p.1 * p.2),
    ← Finset.univ_eq_attach,
    ← Equiv.sum_comp e fun p : (s ×ˢ s' : Finset (G × G)) => F ((p : G × G).2 * (p : G × G).1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hFapply (Δ'.mul_mem (hsΔ (Finset.mem_product.mp p.2).1)
      (hs'Δ (Finset.mem_product.mp p.2).2)),
    hFapply (Δ'.mul_mem (hs'Δ (Finset.mem_product.mp (e p).2).2)
      (hsΔ (Finset.mem_product.mp (e p).2).1))]
  exact (he p (a : A)).symm

end AutomorphicFunction

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ} {UK : Subgroup Kˣ}
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A commuting operator preserves the generalised eigenspace** ([Buzzard, §5 p. 33]: the
`T`-action preserves the Riesz decomposition because every `t ∈ T` commutes with `φ`): if
`t` commutes with `φ`, it maps `ker ((1 − a·φ)^n)` into itself. -/
theorem mapsTo_ker_of_commute {M : Type*} [AddCommGroup M] [Module K M]
    (φ t : Module.End K M) (hcomm : Commute φ t) (a : K) (n : ℕ) {x : M}
    (hx : ((1 - a • φ) ^ n) x = 0) : ((1 - a • φ) ^ n) (t x) = 0 := by
  have h : Commute ((1 - a • φ) ^ n) t :=
    ((Commute.one_left t).sub_left (hcomm.smul_left a)).pow_left n
  calc ((1 - a • φ) ^ n) (t x) = ((1 - a • φ) ^ n * t) x := rfl
    _ = (t * (1 - a • φ) ^ n) x := by rw [h.eq]
    _ = t (((1 - a • φ) ^ n) x) := rfl
    _ = 0 := by rw [hx, map_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A system of eigenvalues on the finite-slope subspace**: a commuting family of
endomorphisms of a nonzero finite-dimensional space over an algebraically closed field has a
common generalised eigenvector; applied to the Riesz subspace `N` of
`exists_riesz_decomposition_forms` this is Buzzard's "`φ`-finite system of eigenvalues"
([*Eigenvarieties*, §5 p. 33]). -/
theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [IsAlgClosed K] (hM : Nontrivial M)
    {ι : Type*} (t : ι → Module.End K M) (hcomm : ∀ i j, Commute (t i) (t j)) :
    ∃ (χ : ι → K) (x : M), x ≠ 0 ∧ ∀ i, x ∈ (t i).maxGenEigenspace (χ i) := by
  -- Simultaneous triangularizability of a commuting family over an algebraically closed field.
  have htop : ⨆ ψ : ι → K, ⨅ i, (t i).maxGenEigenspace (ψ i) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute t
      (fun i j _ => hcomm i j) fun i => Module.End.iSup_maxGenEigenspace_eq_top (t i)
  -- Some joint generalised eigenspace is nonzero, since `M` is.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ι → K, (⨅ i, (t i).maxGenEigenspace (ψ i)) ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    simp only [hc, iSup_bot] at htop
    exact absurd htop.symm (bot_ne_top (α := Submodule K M)).symm
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hψ
  exact ⟨ψ, x, hx0, fun i => (Submodule.mem_iInf _).1 hxmem i⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A system of eigenvalues on the Riesz finite-slope subspace** ([Buzzard,
*Eigenvarieties*, §5 p. 33]).  Let `φ` be the compact operator (`[UηU]`), `N` the finite-slope
subspace attached to a zero `a` of its Fredholm determinant — i.e. `N = ker((1 − a·φ)^n)`, which
is exactly what `exists_riesz_decomposition_forms` produces — and let `t` be a commuting family
of operators each commuting with `φ` (Buzzard's commutative Hecke algebra `𝕋`, taken as data).
Then `N` contains a nonzero simultaneous generalised eigenvector for the whole family: a
`φ`-finite system of eigenvalues.

The hypotheses are stated as the Riesz output gives them (`hNker`/`hNmem` say `N` *is* the
kernel), so this applies verbatim to both the neat-level determinant `heckeCharPowerSeries` and
the general-level `heckeCharPowerSeriesPr`. -/
theorem exists_eigensystem_of_riesz {M : Type*} [AddCommGroup M] [Module K M] [IsAlgClosed K]
    {ι' : Type*} (t : ι' → Module.End K M) (φ : Module.End K M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (hφ : ∀ i, Commute φ (t i)) (a : K) (n : ℕ)
    (N : Submodule K M) [FiniteDimensional K N] (hN : N ≠ ⊥)
    (hNker : ∀ x ∈ N, ((1 - a • φ) ^ n) x = 0)
    (hNmem : ∀ x : M, ((1 - a • φ) ^ n) x = 0 → x ∈ N) :
    ∃ (lam : ι' → K) (ψ : M), ψ ≠ 0 ∧ ψ ∈ N ∧ ∀ i, ψ ∈ (t i).maxGenEigenspace (lam i) := by
  -- Every `t i` preserves `N`, because it commutes with `φ` (this is the whole point of `N`).
  have hmaps : ∀ (i : ι') (x : M), x ∈ N → t i x ∈ N := fun i x hx =>
    hNmem _ (mapsTo_ker_of_commute φ (t i) (hφ i) a n (hNker x hx))
  set T : ι' → Module.End K N := fun i => (t i).restrict (hmaps i) with hT
  have hTcomm : ∀ i j, Commute (T i) (T j) := fun i j =>
    LinearMap.ext fun x => Subtype.ext (by
      simpa [hT, Module.End.mul_apply] using LinearMap.congr_fun (hcomm i j).eq (x : M))
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  obtain ⟨lam, y, hy0, hy⟩ := exists_common_eigenvector (inferInstance) T hTcomm
  refine ⟨lam, (y : M), fun h0 => hy0 (Subtype.ext h0), y.2, fun i => ?_⟩
  have h := hy i
  rw [Module.End.maxGenEigenspace,
    Module.End.genEigenspace_restrict (t i) N ⊤ (lam i) (hmaps i)] at h
  exact h

end QMF.Weight
