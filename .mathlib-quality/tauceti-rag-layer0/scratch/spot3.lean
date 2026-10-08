import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.StdBasis

/-! Spot checks of the planned proof shapes (second round). Nothing here is part of the board's
code; each `example` checks that a ticket's plan typechecks against the skeleton. -/

universe u

open MvPowerSeries MvPowerSeries.Restricted Affinoid Affinoid.TateAlgebra Subring NormedRing
  IsLocalRing

section Rueckert

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- (1) the Rückert axioms assemble from the Tate-algebra statements
example (n : ℕ)
    (h3 : ∀ f : TateAlgebra K (n + 1), f ≠ 0 →
      ∃ (σ : TateAlgebra K (n + 1) ≃+* TateAlgebra K (n + 1)) (e : (TateAlgebra K (n + 1))ˣ)
        (ω : Polynomial (TateAlgebra K n)),
        ω ∈ {ω | IsWeierstrassPolynomial K n ω} ∧ e * σ f = ofPolynomial K n ω) :
    IsRueckert (ofPolynomial K n) {ω | IsWeierstrassPolynomial K n ω} :=
  ⟨ofPolynomial_injective, fun _ hω ↦ hω.monic,
    fun _ _ hp hq h ↦ IsWeierstrassPolynomial.of_mul hp hq h,
    fun _ hω ↦ IsWeierstrassPolynomial.bijective_quotientMap hω, h3⟩

-- (2) the induction step of the noetherian instance
example (n : ℕ) (_ : IsNoetherianRing (TateAlgebra K n)) : IsNoetherianRing (TateAlgebra K (n + 1)) :=
  (isRueckert_ofPolynomial K n).isNoetherianRing

-- (3) the base case along `T₀ ≃ K`
example : IsNoetherianRing (TateAlgebra K 0) :=
  isNoetherianRing_of_ringEquiv K (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).symm

-- (3') the dimension step
example (n : ℕ) : ringKrullDim (TateAlgebra K (n + 1)) = ringKrullDim (TateAlgebra K n) + 1 :=
  (isRueckert_ofPolynomial K n).ringKrullDim_eq (by simpa using isWeierstrassPolynomial_X_pow 1)

-- (3'') the Jacobson step
example (n : ℕ) (_ : IsJacobsonRing (TateAlgebra K n)) : IsJacobsonRing (TateAlgebra K (n + 1)) :=
  (isRueckert_ofPolynomial K n).isJacobsonRing jacobson_bot

end Rueckert

section MaxModulus

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- (4) the spectral normed-field structure on a finite extension feeds the point-level statement
example (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Restricted K (1 : Fin 2 → ℝ)) (S : Finset L)
    (hS₁ : ∀ s ∈ S, spectralNorm K L s = 1)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → spectralNorm K L (s - t) = 1)
    (hf : ∀ t : Fin 2 →₀ ℕ, ‖coeff t f.1‖ = ‖f‖ → ∀ i, t i < S.card) :
    ∃ x : MaximalSpectrum (Restricted K (1 : Fin 2 → ℝ)), evalNorm K x f = ‖f‖ := by
  letI := spectralNorm.normedField K L
  letI := spectralNorm.normedAlgebra K L
  haveI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  haveI : CompleteSpace L := spectralNorm.completeSpace K L
  obtain ⟨x, hx, -, hxf⟩ := exists_norm_aeval_eq_norm (K := K) S (fun s hs ↦ (hS₁ s hs).le) hS f hf
  haveI := Affinoid.isMaximal_ker_of_isAlgebraic (aeval (K := K) (1 : Fin 2 → ℝ) x hx)
  refine ⟨⟨RingHom.ker (aeval (K := K) (1 : Fin 2 → ℝ) x hx), inferInstance⟩, ?_⟩
  rw [Affinoid.evalNorm_eq_norm_algHom (aeval (K := K) (1 : Fin 2 → ℝ) x hx) _ rfl]
  exact hxf

end MaxModulus

section Basis

-- (6) the coordinates of `k[X]^ι` in the index type of the monomial orthonormal basis
noncomputable example (k : Type*) [Field k] (σ ι : Type*) [Fintype ι] :
    (ι → MvPolynomial σ k) ≃ₗ[k] ((Σ _ : ι, σ →₀ ℕ) →₀ k) :=
  (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ k).repr

end Basis
