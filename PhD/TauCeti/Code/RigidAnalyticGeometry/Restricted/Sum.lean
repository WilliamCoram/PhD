/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Eval

/-!
# Restricted power series in a sum of variables, and renaming of variables

A restricted power series in the variables `σ ⊕ τ` is the same as a restricted power series in
`σ` whose coefficients are restricted power series in `τ`: `A⟨X, Y⟩ ≅ A⟨Y⟩⟨X⟩`, isometrically for
the Gauss norms. Renaming the variables along a bijection is an isometric isomorphism as well. Both
isomorphisms are built from the evaluation homomorphisms of `TateAlgebra/Eval.lean`, which makes
them ring homomorphisms for free; they are mutually inverse because continuous ring homomorphisms
out of the restricted power series are determined by their values on constants and variables.

For the Tate algebras this gives `Tₙ⟨Y₁, …, Y_m⟩ ≅ T_{m+n}`, BGR 6.1.1/8 without the complete tensor
product.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.3 (`A⟨X⟩⟨Y⟩ ≅ A⟨X, Y⟩`).
Tau Ceti home: `TauCeti/RingTheory/MvPowerSeries/Restricted/Sum.lean`.

## Main definitions

* `MvPowerSeries.Restricted.sumEquiv` — `Restricted R c ≃+* Restricted (Restricted R (c ∘ inr))
  (c ∘ inl)` for `c : σ ⊕ τ → ℝ`.
* `MvPowerSeries.Restricted.renameHom` — renaming along any map `e : σ → τ` at the unit
  polyradius; `renameEquiv` — along a bijection.
* `Affinoid.TateAlgebra.sumEquiv` — `Restricted (TateAlgebra K n) 1 ≃ₐ[K] TateAlgebra K (m + n)`,
  the new variables first (`Fin.castAdd`), the old ones last (`Fin.natAdd`).

## Main results

* `MvPowerSeries.Restricted.norm_sumEquiv`, `norm_renameEquiv`, `Affinoid.TateAlgebra.norm_sumEquiv`
  — the three isomorphisms are isometric.
* `MvPowerSeries.Restricted.renameHom_comp_renameHom` — renaming along a left inverse undoes a
  renaming.
-/

open Filter Topology

namespace MvPowerSeries.Restricted

section Sum

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  {σ τ : Type*} (c : σ ⊕ τ → ℝ) [Fact (∀ i, 0 < c i)]

instance : Fact (∀ i, 0 < (c ∘ Sum.inl) i) := ⟨fun i ↦ Fact.out (p := ∀ i, 0 < c i) (Sum.inl i)⟩

instance : Fact (∀ i, 0 < (c ∘ Sum.inr) i) := ⟨fun i ↦ Fact.out (p := ∀ i, 0 < c i) (Sum.inr i)⟩

variable (R) in
/-- The variables of `R⟨X ⊕ Y⟩` as elements of `R⟨Y⟩⟨X⟩`: `X i ↦ X i`, `Y j ↦ C (Y j)`. -/
noncomputable def sumTuple :
    σ ⊕ τ → Restricted (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) :=
  Sum.elim (fun i ↦ X (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) i)
    (fun j ↦ C (c ∘ Sum.inl) (X R (c ∘ Sum.inr) j))

omit [CompleteSpace R] in
theorem norm_sumTuple_le (i : σ ⊕ τ) : ‖sumTuple R c i‖ ≤ c i := by
  rcases i with i | j
  · simp [sumTuple, norm_X]
  · simp [sumTuple, norm_C, norm_X]

/-- The homomorphism `R⟨X ⊕ Y⟩ → R⟨Y⟩⟨X⟩`, by evaluation at the variables. -/
noncomputable def sumToIter :
    Restricted R c →+* Restricted (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) :=
  eval₂ (Cφ := 1) c ((C (c ∘ Sum.inl)).comp (C (c ∘ Sum.inr))) (sumTuple R c)
    (fun r ↦ by simp [norm_C]) (norm_prod_pow_le_of_norm_le c _ (norm_sumTuple_le c))

/-- The homomorphism `R⟨Y⟩⟨X⟩ → R⟨X ⊕ Y⟩`: the coefficients `R⟨Y⟩` are evaluated at the variables
`Y j ↦ X (inr j)` and then the outer variables at `X i ↦ X (inl i)`. -/
noncomputable def iterToSum :
    Restricted (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) →+* Restricted R c :=
  eval₂ (Cφ := 1) (c ∘ Sum.inl) (eval₂ (Cφ := 1) (c ∘ Sum.inr) (C c) (fun j ↦ X R c (Sum.inr j))
      (fun r ↦ by simp [norm_C]) (norm_prod_pow_le_of_norm_le _ _ fun j ↦ by simp [norm_X]))
    (fun i ↦ X R c (Sum.inl i)) (fun f ↦ by rw [one_mul]; exact norm_eval₂_le _ _ f)
    (norm_prod_pow_le_of_norm_le _ _ fun i ↦ by simp [norm_X])

theorem continuous_sumToIter : Continuous (sumToIter (R := R) c) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

theorem continuous_iterToSum : Continuous (iterToSum (R := R) c) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

theorem iterToSum_comp_sumToIter :
    (iterToSum (R := R) c).comp (sumToIter c) = RingHom.id (Restricted R c) := by
  refine ringHom_ext_of_continuous ((continuous_iterToSum c).comp (continuous_sumToIter c))
    continuous_id (fun r ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.comp_apply, iterToSum, sumToIter, eval₂_C, RingHom.id_apply]
  · rcases i with i | j
    · simp only [RingHom.comp_apply, iterToSum, sumToIter, eval₂_X, sumTuple, Sum.elim_inl,
        RingHom.id_apply]
    · simp only [RingHom.comp_apply, iterToSum, sumToIter, eval₂_X, eval₂_C, sumTuple,
        Sum.elim_inr, RingHom.id_apply]

theorem sumToIter_comp_iterToSum :
    (sumToIter (R := R) c).comp (iterToSum c) =
      RingHom.id (Restricted (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl)) := by
  have hC : Continuous (C (R := Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl)) :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun a ↦ by rw [norm_C, one_mul]
  have hinner : (sumToIter (R := R) c).comp
      (eval₂ (Cφ := 1) (c ∘ Sum.inr) (C c) (fun j ↦ X R c (Sum.inr j))
        (fun r ↦ by simp [norm_C]) (norm_prod_pow_le_of_norm_le _ _ fun j ↦ by simp [norm_X])) =
      C (c ∘ Sum.inl) := by
    refine ringHom_ext_of_continuous
      ((continuous_sumToIter c).comp (continuous_eval₂ (Cφ := 1) (Cx := 1) _ _)) hC
      (fun r ↦ ?_) fun j ↦ ?_
    · simp only [RingHom.comp_apply, sumToIter, eval₂_C]
    · simp only [RingHom.comp_apply, sumToIter, eval₂_X, sumTuple, Sum.elim_inr]
  refine ringHom_ext_of_continuous ((continuous_sumToIter c).comp (continuous_iterToSum c))
    continuous_id (fun g ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.comp_apply, iterToSum, eval₂_C, RingHom.id_apply]
    exact RingHom.congr_fun hinner g
  · simp only [RingHom.comp_apply, iterToSum, eval₂_X, sumToIter, sumTuple, Sum.elim_inl,
      RingHom.id_apply]

/-- `R⟨X ⊕ Y⟩ ≅ R⟨Y⟩⟨X⟩`: a restricted power series in a sum of variables is a restricted power
series in the first variables with coefficients restricted power series in the second ones.
Source: BGR 6.1.1/7–8 (`A⟨X⟩ ≅ A ⊗̂ k⟨X⟩`, `T_m ⊗̂ Tₙ ≅ T_{m+n}`), without tensor products. -/
noncomputable def sumEquiv :
    Restricted R c ≃+* Restricted (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) :=
  RingEquiv.ofRingHom (sumToIter c) (iterToSum c) (sumToIter_comp_iterToSum c)
    (iterToSum_comp_sumToIter c)

@[simp]
theorem sumEquiv_C (r : R) : sumEquiv c (C c r) = C (c ∘ Sum.inl) (C (c ∘ Sum.inr) r) := by
  change sumToIter c (C c r) = _
  simp only [sumToIter, eval₂_C, RingHom.comp_apply]

@[simp]
theorem sumEquiv_X_inl (i : σ) :
    sumEquiv c (X R c (Sum.inl i)) = X (Restricted R (c ∘ Sum.inr)) (c ∘ Sum.inl) i := by
  change sumToIter c (X R c (Sum.inl i)) = _
  simp only [sumToIter, eval₂_X, sumTuple, Sum.elim_inl]

@[simp]
theorem sumEquiv_X_inr (j : τ) :
    sumEquiv c (X R c (Sum.inr j)) = C (c ∘ Sum.inl) (X R (c ∘ Sum.inr) j) := by
  change sumToIter c (X R c (Sum.inr j)) = _
  simp only [sumToIter, eval₂_X, sumTuple, Sum.elim_inr]

/-- The isomorphism `R⟨X ⊕ Y⟩ ≅ R⟨Y⟩⟨X⟩` is isometric for the Gauss norms. -/
theorem norm_sumEquiv (f : Restricted R c) : ‖sumEquiv (R := R) c f‖ = ‖f‖ := by
  change ‖sumToIter (R := R) c f‖ = ‖f‖
  have h1 : ‖sumToIter (R := R) c f‖ ≤ ‖f‖ := norm_eval₂_le _ _ f
  have h2 : ‖iterToSum (R := R) c (sumToIter c f)‖ ≤ ‖sumToIter (R := R) c f‖ :=
    norm_eval₂_le _ _ _
  rw [← RingHom.comp_apply, iterToSum_comp_sumToIter, RingHom.id_apply] at h2
  exact le_antisymm h1 h2

theorem continuous_sumEquiv : Continuous (sumEquiv (R := R) c) :=
  continuous_sumToIter c

theorem continuous_sumEquiv_symm : Continuous (sumEquiv (R := R) c).symm :=
  continuous_iterToSum c

end Sum

section Rename

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  {σ τ : Type*}

variable (R) in
/-- Renaming the variables of a strictly convergent power series along a map `e : σ → τ`,
`X i ↦ X (e i)`, at the unit polyradius: the evaluation homomorphism at the variables `X (e i)`,
which have norm one. -/
noncomputable def renameHom (e : σ → τ) :
    Restricted R (1 : σ → ℝ) →+* Restricted R (1 : τ → ℝ) :=
  eval₂ (Cφ := 1) (Cx := 1) (1 : σ → ℝ) (C (1 : τ → ℝ)) (fun i ↦ X R (1 : τ → ℝ) (e i))
    (fun r ↦ by simp [norm_C]) (norm_prod_pow_le_of_norm_le _ _ fun i ↦ by simp [norm_X])

@[simp]
theorem renameHom_C (e : σ → τ) (r : R) :
    renameHom R e (C (1 : σ → ℝ) r) = C (1 : τ → ℝ) r :=
  eval₂_C _ _ r

@[simp]
theorem renameHom_X (e : σ → τ) (i : σ) :
    renameHom R e (X R (1 : σ → ℝ) i) = X R (1 : τ → ℝ) (e i) :=
  eval₂_X _ _ i

theorem continuous_renameHom (e : σ → τ) : Continuous (renameHom R e) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

theorem norm_renameHom_le (e : σ → τ) (f : Restricted R (1 : σ → ℝ)) :
    ‖renameHom R e f‖ ≤ ‖f‖ :=
  norm_eval₂_le _ _ f

/-- Renaming along `e` and then along a left inverse of `e` is the identity. -/
theorem renameHom_comp_renameHom {e : σ → τ} {e' : τ → σ} (h : ∀ i, e' (e i) = i) :
    (renameHom R e').comp (renameHom R e) = RingHom.id (Restricted R (1 : σ → ℝ)) := by
  refine ringHom_ext_of_continuous ((continuous_renameHom e').comp (continuous_renameHom e))
    continuous_id (fun r ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.comp_apply, renameHom_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, renameHom_X, h, RingHom.id_apply]

variable (R) in
/-- Renaming the variables of a strictly convergent power series along a bijection `e : σ ≃ τ`,
at the unit polyradius. Source: BGR 5.1.3 (a chart is a renaming of the variables). -/
noncomputable def renameEquiv (e : σ ≃ τ) :
    Restricted R (1 : σ → ℝ) ≃+* Restricted R (1 : τ → ℝ) :=
  RingEquiv.ofRingHom (renameHom R e) (renameHom R e.symm)
    (renameHom_comp_renameHom e.apply_symm_apply) (renameHom_comp_renameHom e.symm_apply_apply)

variable (e : σ ≃ τ)

@[simp]
theorem renameEquiv_C (r : R) : renameEquiv R e (C (1 : σ → ℝ) r) = C (1 : τ → ℝ) r :=
  renameHom_C e r

@[simp]
theorem renameEquiv_X (i : σ) : renameEquiv R e (X R (1 : σ → ℝ) i) = X R (1 : τ → ℝ) (e i) :=
  renameHom_X e i

/-- Renaming the variables is an isometry for the Gauss norms. -/
theorem norm_renameEquiv (f : Restricted R (1 : σ → ℝ)) : ‖renameEquiv R e f‖ = ‖f‖ := by
  change ‖renameHom R e f‖ = ‖f‖
  refine le_antisymm (norm_renameHom_le e f) ?_
  calc ‖f‖ = ‖renameHom R e.symm (renameHom R e f)‖ := by
        rw [← RingHom.comp_apply, renameHom_comp_renameHom e.symm_apply_apply, RingHom.id_apply]
    _ ≤ ‖renameHom R e f‖ := norm_renameHom_le _ _

end Rename

end MvPowerSeries.Restricted

namespace Affinoid.TateAlgebra

open MvPowerSeries MvPowerSeries.Restricted

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (n m : ℕ)

/-- `Tₙ → T_{m+n}`, `X i ↦ X (natAdd m i)`: the old variables are the last `n`. -/
private noncomputable def sumInner : TateAlgebra K n →+* TateAlgebra K (m + n) :=
  eval₂ (Cφ := 1) (Cx := 1) (1 : Fin n → ℝ) (Restricted.C (1 : Fin (m + n) → ℝ))
    (fun i ↦ X K (1 : Fin (m + n) → ℝ) (Fin.natAdd m i)) (fun r ↦ by simp [norm_C])
    (norm_prod_pow_le_of_norm_le _ _ fun i ↦ by simp [norm_X])

/-- `Tₙ⟨Y_m⟩ → T_{m+n}`: the coefficients by `sumInner`, `Y j ↦ X (castAdd n j)`. -/
private noncomputable def sumFwd :
    Restricted (TateAlgebra K n) (1 : Fin m → ℝ) →+* TateAlgebra K (m + n) :=
  eval₂ (Cφ := 1) (Cx := 1) (1 : Fin m → ℝ) (sumInner K n m)
    (fun j ↦ X K (1 : Fin (m + n) → ℝ) (Fin.castAdd n j))
    (fun f ↦ by rw [one_mul]; exact norm_eval₂_le _ _ f)
    (norm_prod_pow_le_of_norm_le _ _ fun j ↦ by simp [norm_X])

/-- The variables of `T_{m+n}` in `Tₙ⟨Y_m⟩`: the first `m` are the `Y j`, the last `n` the
constants `X i`. -/
private noncomputable def sumTupleTate :
    Fin (m + n) → Restricted (TateAlgebra K n) (1 : Fin m → ℝ) :=
  Fin.append (fun j ↦ X (TateAlgebra K n) (1 : Fin m → ℝ) j)
    (fun i ↦ Restricted.C (1 : Fin m → ℝ) (X K (1 : Fin n → ℝ) i))

omit [CompleteSpace K] in
private theorem norm_sumTupleTate_le (k : Fin (m + n)) : ‖sumTupleTate K n m k‖ ≤ 1 := by
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) k
  · simp [sumTupleTate, Fin.append_left, norm_X]
  · simp [sumTupleTate, Fin.append_right, norm_C, norm_X]

/-- `T_{m+n} → Tₙ⟨Y_m⟩`. -/
private noncomputable def sumBwd :
    TateAlgebra K (m + n) →+* Restricted (TateAlgebra K n) (1 : Fin m → ℝ) :=
  eval₂ (Cφ := 1) (Cx := 1) (1 : Fin (m + n) → ℝ)
    ((Restricted.C (1 : Fin m → ℝ)).comp (Restricted.C (1 : Fin n → ℝ))) (sumTupleTate K n m)
    (fun r ↦ by simp [norm_C]) (norm_prod_pow_le_of_norm_le _ _ (norm_sumTupleTate_le K n m))

private theorem continuous_sumInner : Continuous (sumInner K n m) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

private theorem continuous_sumFwd : Continuous (sumFwd K n m) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

private theorem continuous_sumBwd : Continuous (sumBwd K n m) :=
  continuous_eval₂ (Cφ := 1) (Cx := 1) _ _

private theorem sumBwd_comp_sumInner :
    (sumBwd K n m).comp (sumInner K n m) = Restricted.C (1 : Fin m → ℝ) := by
  have hC : Continuous (Restricted.C (R := TateAlgebra K n) (1 : Fin m → ℝ)) :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun a ↦ by rw [norm_C, one_mul]
  refine ringHom_ext_of_continuous ((continuous_sumBwd K n m).comp (continuous_sumInner K n m)) hC
    (fun r ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.comp_apply, sumBwd, sumInner, eval₂_C]
  · simp only [RingHom.comp_apply, sumBwd, sumInner, eval₂_X, sumTupleTate, Fin.append_right]

private theorem sumBwd_comp_sumFwd :
    (sumBwd K n m).comp (sumFwd K n m) = RingHom.id _ := by
  refine ringHom_ext_of_continuous ((continuous_sumBwd K n m).comp (continuous_sumFwd K n m))
    continuous_id (fun f ↦ ?_) fun j ↦ ?_
  · simp only [RingHom.comp_apply, sumFwd, eval₂_C, RingHom.id_apply]
    exact RingHom.congr_fun (sumBwd_comp_sumInner K n m) f
  · simp only [RingHom.comp_apply, sumFwd, sumBwd, eval₂_X, sumTupleTate, Fin.append_left,
      RingHom.id_apply]

private theorem sumFwd_comp_sumBwd :
    (sumFwd K n m).comp (sumBwd K n m) = RingHom.id _ := by
  refine ringHom_ext_of_continuous ((continuous_sumFwd K n m).comp (continuous_sumBwd K n m))
    continuous_id (fun r ↦ ?_) fun k ↦ ?_
  · simp only [RingHom.comp_apply, sumBwd, sumFwd, sumInner, eval₂_C, RingHom.id_apply]
  · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) k
    · simp only [RingHom.comp_apply, sumBwd, sumFwd, eval₂_X, sumTupleTate, Fin.append_left,
        RingHom.id_apply]
    · simp only [RingHom.comp_apply, sumBwd, sumFwd, sumInner, eval₂_X, eval₂_C, sumTupleTate,
        Fin.append_right, RingHom.id_apply]

private theorem sumFwd_algebraMap (r : K) :
    sumFwd K n m (algebraMap K (Restricted (TateAlgebra K n) (1 : Fin m → ℝ)) r) =
      algebraMap K (TateAlgebra K (m + n)) r := by
  rw [algebraMap_eq_C_comp, RingHom.comp_apply, algebraMap_apply, algebraMap_apply]
  simp only [sumFwd, sumInner, eval₂_C]

/-- `Tₙ⟨Y₁, …, Y_m⟩ ≅ T_{m+n}` as `K`-algebras, isometrically: the sum isomorphism followed by the
renaming `Fin m ⊕ Fin n ≃ Fin (m + n)`. Source: BGR 6.1.1/8 (`T_m ⊗̂_k Tₙ ≅ T_{m+n}`). -/
noncomputable def sumEquiv :
    Restricted (TateAlgebra K n) (1 : Fin m → ℝ) ≃ₐ[K] TateAlgebra K (m + n) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (sumFwd K n m) (sumBwd K n m)
    (sumFwd_comp_sumBwd K n m) (sumBwd_comp_sumFwd K n m)) (sumFwd_algebraMap K n m)

theorem norm_sumEquiv (f : Restricted (TateAlgebra K n) (1 : Fin m → ℝ)) :
    ‖sumEquiv K n m f‖ = ‖f‖ := by
  change ‖sumFwd K n m f‖ = ‖f‖
  refine le_antisymm (norm_eval₂_le _ _ f) ?_
  calc ‖f‖ = ‖sumBwd K n m (sumFwd K n m f)‖ := by
        rw [← RingHom.comp_apply, sumBwd_comp_sumFwd, RingHom.id_apply]
    _ ≤ ‖sumFwd K n m f‖ := norm_eval₂_le _ _ _

@[simp]
theorem sumEquiv_C (f : TateAlgebra K n) :
    sumEquiv K n m (C (1 : Fin m → ℝ) f) =
      eval₂ (Cφ := 1) (1 : Fin n → ℝ) (C (1 : Fin (m + n) → ℝ))
        (fun i ↦ X K (1 : Fin (m + n) → ℝ) (Fin.natAdd m i))
        (fun r ↦ by simp [norm_C])
        (norm_prod_pow_le_of_norm_le _ _ fun i ↦ by simp [norm_X]) f := by
  change sumFwd K n m (Restricted.C (1 : Fin m → ℝ) f) = _
  simp only [sumFwd, eval₂_C]
  rfl

@[simp]
theorem sumEquiv_X (i : Fin m) :
    sumEquiv K n m (X (TateAlgebra K n) (1 : Fin m → ℝ) i) =
      X K (1 : Fin (m + n) → ℝ) (Fin.castAdd n i) := by
  change sumFwd K n m (X (TateAlgebra K n) (1 : Fin m → ℝ) i) = _
  simp only [sumFwd, eval₂_X]

end Affinoid.TateAlgebra
