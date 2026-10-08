import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.StrictlyClosed

/-! Spot check: the adapted orthonormal basis assembles from its four ingredients, and the
corollaries follow from the nearest-point statement. -/

open Filter Topology Subring NormedRing IsLocalRing MvPowerSeries MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ ι : Type*} [Fintype ι]
  [DecidableEq ι] [Finite σ] [CompleteSpace K]

example (N : Submodule (Restricted K (1 : σ → ℝ)) (ι → Restricted K (1 : σ → ℝ))) :
    ∃ (r : ℕ) (g : Fin r → ι → Restricted K (1 : σ → ℝ)) (A : Set ((σ →₀ ℕ) × Fin r))
      (B : Set (Σ _ : ι, σ →₀ ℕ)),
      (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧ IsOrthonormalBasis K (adaptedFamily g A B) ∧
        ∀ x ∈ N, ∀ c : A ⊕ B → K, HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) x →
          ∀ b : B, c (Sum.inr b) = 0 := by
  obtain ⟨r, g, hg, hgN, hspan⟩ := exists_generators_reductionSubmodule N
  obtain ⟨A, B, hli, hsp, hA⟩ :=
    MvPolynomial.exists_basis_adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le)
  have hON := isOrthonormalBasis_adaptedFamily hg hli hsp
  refine ⟨r, g, A, B, hgN, hg, hON, fun x hx c hc b ↦ ?_⟩
  exact coeff_inr_eq_zero_of_mem hg hgN hON hli (hA.trans (by rw [hspan])) hx hc b

-- generators with bounds from the nearest-point statement
example (N : Submodule (Restricted K (1 : σ → ℝ)) (ι → Restricted K (1 : σ → ℝ))) :
    ∃ (r : ℕ) (g : Fin r → ι → Restricted K (1 : σ → ℝ)), (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ x ∈ N, ∃ q : Fin r → Restricted K (1 : σ → ℝ), x = ∑ j, q j • g j ∧ ∀ j, ‖q j‖ ≤ ‖x‖ := by
  obtain ⟨r, g, hgN, hg, h⟩ := exists_generators_forall_exists_isNearest N
  refine ⟨r, g, hgN, hg, fun x hx ↦ ?_⟩
  obtain ⟨q, hq, hmin⟩ := h x
  refine ⟨q, ?_, hq⟩
  have hmem : x - ∑ j, q j • g j ∈ N :=
    N.sub_mem hx (N.sum_mem fun j _ ↦ N.smul_mem _ (hgN j))
  have h0 := hmin _ hmem
  rw [sub_self, norm_zero] at h0
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
