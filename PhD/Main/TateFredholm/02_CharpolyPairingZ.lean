/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.TateFredholm.«01_CharpolyPairing»
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The pairing of characteristic roots up to a finite-order operator

`01_CharpolyPairing.lean` pairs the characteristic roots of `A` and `B` when `A B = c·1`.  Here the
scalar is replaced by `c·Z` with `Z` commuting with `A` and of finite order (`Z^N = 1`): this is the
shape of the Atkin–Lehner identity `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z` at a general tame level,
where `Z` is the tame central operator (right translation by the central idèle `p^{(p)}`), whose
eigenvalues are the values of the tame central characters at `p` — roots of unity ([Miyake,
Thm 4.6.17], cited at `bu04.txt:1122–1124`: `a_p(f)·a_p(f|W) = χ_M(p)·p^{k+1}`).  The conclusion is
the multiset identity of the **norms** of the roots, which is all the slope arguments use.

The route: `Z^N = 1` makes `Z` semisimple (`X^N − 1` is squarefree in characteristic zero,
`isSemisimple_toLin'_of_pow_eq_one`), so the space is the direct sum of the eigenspaces of `Z`
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top`), each preserved by `A⁻¹`, which commutes with
`Z`; on the `μ`-eigenspace `A⁻¹Z` is `μ·A⁻¹` with `‖μ‖ = 1`, and the characteristic polynomial of
a map preserving a direct sum is the product of those of the restrictions
(`LinearMap.charpoly_prodMap`, `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top`).
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Field

variable {K : Type*} [Field K] {A B Z : Matrix n n K} {c : K}

/-- `A B = c Z` ⇒ `det A · det B = c^n · det Z`. -/
theorem det_mul_det_of_mul_eq_smul_mul (h : A * B = c • Z) :
    A.det * B.det = c ^ Fintype.card n * Z.det := by
  rw [← det_mul, h, det_smul]

/-- A matrix of finite order has nonzero determinant. -/
theorem det_ne_zero_of_pow_eq_one {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) : Z.det ≠ 0 := by
  intro h0
  have h := congrArg det hZ
  rw [det_pow, det_one, h0, zero_pow hN.ne'] at h
  exact zero_ne_one h

/-- Under `A B = c Z`, `c ≠ 0`, `Z^N = 1`, the determinant of `A` is nonzero. -/
theorem det_ne_zero_of_mul_eq_smul_mul (hc : c ≠ 0) (h : A * B = c • Z) {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : A.det ≠ 0 := by
  intro h0
  have hprod := det_mul_det_of_mul_eq_smul_mul h
  rw [h0, zero_mul] at hprod
  exact mul_ne_zero (pow_ne_zero _ hc) (det_ne_zero_of_pow_eq_one hN hZ) hprod.symm

/-- Under `A B = c Z`, `c ≠ 0`, `Z^N = 1`, the determinant of `B` is nonzero. -/
theorem det_ne_zero_of_mul_eq_smul_mul' (hc : c ≠ 0) (h : A * B = c • Z) {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : B.det ≠ 0 := by
  intro h0
  have hprod := det_mul_det_of_mul_eq_smul_mul h
  rw [h0, mul_zero] at hprod
  exact mul_ne_zero (pow_ne_zero _ hc) (det_ne_zero_of_pow_eq_one hN hZ) hprod.symm

/-- `Z` commutes with `A⁻¹` when it commutes with `A`. -/
private theorem mul_nonsing_inv_comm (hA : IsUnit A.det) (hZA : Z * A = A * Z) :
    Z * A⁻¹ = A⁻¹ * Z := by
  calc Z * A⁻¹ = A⁻¹ * A * Z * A⁻¹ := by rw [nonsing_inv_mul A hA, Matrix.one_mul]
    _ = A⁻¹ * (Z * A) * A⁻¹ := by rw [hZA, Matrix.mul_assoc A⁻¹ A Z]
    _ = A⁻¹ * Z := by simp only [Matrix.mul_assoc, mul_nonsing_inv A hA, Matrix.mul_one]

/-- `Z` commutes with `B` as well: `B = A⁻¹·(c Z)` and `Z` commutes with `A⁻¹`. -/
theorem mul_comm_of_mul_eq_smul_mul (hc : c ≠ 0) (h : A * B = c • Z) (hZA : Z * A = A * Z)
    {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) : Z * B = B * Z := by
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_mul_eq_smul_mul hc h hN hZ)
  have hB : B = A⁻¹ * (c • Z) := by
    rw [← h, ← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul]
  rw [hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
    mul_nonsing_inv_comm hA hZA]

/-- `B A = c Z` as well. -/
theorem mul_eq_smul_mul_symm (hc : c ≠ 0) (h : A * B = c • Z) (hZA : Z * A = A * Z) {N : ℕ}
    (hN : 0 < N) (hZ : Z ^ N = 1) : B * A = c • Z := by
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_mul_eq_smul_mul hc h hN hZ)
  have hB : B = A⁻¹ * (c • Z) := by
    rw [← h, ← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul]
  rw [hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hZA, ← Matrix.mul_assoc,
    nonsing_inv_mul A hA, Matrix.one_mul]

end Field

section Normed

variable {K : Type*} [NormedField K]

/-- A matrix of finite order has a determinant of norm one. -/
theorem norm_det_eq_one_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    ‖Z.det‖ = 1 := by
  have h := congrArg (fun M : Matrix n n K => ‖M.det‖) hZ
  simp only [det_pow, det_one, norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h

end Normed

section Split

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial of an endomorphism preserving two complementary subspaces is the
product of those of its restrictions (the one-split pattern of
`Mathlib/LinearAlgebra/Eigenspace/Zero.lean`, `finrank_maxGenEigenspace_zero_eq`). -/
private theorem charpoly_eq_mul_charpoly_restrict (φ : Module.End K V) {U W : Submodule K V}
    (hUW : IsCompl U W) (hφU : ∀ x ∈ U, φ x ∈ U) (hφW : ∀ x ∈ W, φ x ∈ W) :
    φ.charpoly = (φ.restrict hφU).charpoly * (φ.restrict hφW).charpoly := by
  let e := Submodule.prodEquivOfIsCompl U W hUW
  let b := (Module.Free.chooseBasis K U).prod (Module.Free.chooseBasis K W)
  have hψ : (φ.restrict hφU).prodMap (φ.restrict hφW) = e.symm.conj φ := by
    apply b.ext
    simp only [Module.Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr,
      LinearMap.prodMap_apply, LinearEquiv.conj_apply, LinearEquiv.symm_symm,
      Submodule.coe_prodEquivOfIsCompl, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.coprod_apply, Submodule.coe_subtype, _root_.map_add,
      Sum.forall, Sum.elim_inl, _root_.map_zero, ZeroMemClass.coe_zero, add_zero,
      LinearEquiv.eq_symm_apply, and_self, Submodule.coe_prodEquivOfIsCompl',
      LinearMap.coe_restrict_apply, implies_true, Sum.elim_inr, zero_add, e, b]
  rw [← e.symm.charpoly_conj φ, ← hψ, LinearMap.charpoly_prodMap]

end Split

section AlgClosed

variable {K : Type*} [NormedField K] [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] [CharZero K] in
/-- The roots of `charpolyRev (μ • A)` are those of `charpolyRev A` divided by `μ`
(`charpolyRev (μ • A) = (charpolyRev A).comp (C μ * X)`, `Polynomial.roots_comp_C_mul_X_add_C`). -/
theorem roots_charpolyRev_smul {A : Matrix n n K} {μ : K} (hμ : μ ≠ 0) :
    (μ • A).charpolyRev.roots = A.charpolyRev.roots.map (fun x => μ⁻¹ * x) := by
  have hcomp : (μ • A).charpolyRev = A.charpolyRev.comp (C μ * X) := by
    rw [charpolyRev, charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [RingHom.mapMatrix_apply, map_apply, sub_apply, smul_apply, one_apply_eq,
        smul_eq_mul, Polynomial.coe_compRingHom_apply, Polynomial.sub_comp, Polynomial.one_comp,
        Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp, _root_.map_mul]
      ring_nf
    · simp only [RingHom.mapMatrix_apply, map_apply, sub_apply, smul_apply, one_apply_ne hij,
        smul_eq_mul, Polynomial.coe_compRingHom_apply, Polynomial.sub_comp, Polynomial.zero_comp,
        Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp, _root_.map_mul]
      ring_nf
  rw [hcomp, show (C μ * X : K[X]) = C μ * X + C 0 by simp,
    roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.2 hμ)]
  exact Multiset.map_congr rfl fun x _ => by rw [Ring.inverse_eq_inv, sub_zero]

omit [IsAlgClosed K] [CharZero K] in
/-- The roots of `charpoly (μ • A)` are those of `charpoly A` times `μ`. -/
theorem roots_charpoly_smul {A : Matrix n n K} {μ : K} (hμ : μ ≠ 0) :
    (μ • A).charpoly.roots = A.charpoly.roots.map (fun x => μ * x) := by
  have hCC : C μ * C μ⁻¹ = (1 : K[X]) := by rw [← C_mul, mul_inv_cancel₀ hμ, C_1]
  have hmat : charmatrix (μ • A)
      = C μ • (Polynomial.compRingHom (C μ⁻¹ * X)).mapMatrix (charmatrix A) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [charmatrix_apply_eq, smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, map_apply,
        Polynomial.coe_compRingHom_apply, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp, _root_.map_mul, mul_sub, ← mul_assoc, hCC, one_mul]
    · simp only [charmatrix_apply_ne _ _ _ hij, smul_apply, smul_eq_mul, RingHom.mapMatrix_apply,
        map_apply, Polynomial.coe_compRingHom_apply, Polynomial.neg_comp, Polynomial.C_comp,
        _root_.map_mul]
      ring_nf
  have hcomp : (μ • A).charpoly = C (μ ^ Fintype.card n) * A.charpoly.comp (C μ⁻¹ * X) := by
    rw [charpoly, charpoly, hmat, det_smul, ← Polynomial.coe_compRingHom_apply, RingHom.map_det,
      C_pow]
  rw [hcomp, roots_C_mul _ (pow_ne_zero _ hμ), show (C μ⁻¹ * X : K[X]) = C μ⁻¹ * X + C 0 by simp,
    roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.2 (inv_ne_zero hμ))]
  exact Multiset.map_congr rfl fun x _ => by rw [Ring.inverse_eq_inv, inv_inv, sub_zero]

omit [IsAlgClosed K] [CharZero K] in
/-- The characteristic roots of `μ • f` are those of `f` times `μ` (`roots_charpoly_smul` in a
basis). -/
private theorem roots_charpoly_smul_end {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) {μ : K} (hμ : μ ≠ 0) :
    (μ • f).charpoly.roots = f.charpoly.roots.map (fun x => μ * x) := by
  rw [← LinearMap.charpoly_toMatrix (μ • f) (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f (Module.finBasis K V), _root_.map_smul]
  exact roots_charpoly_smul hμ

omit [IsAlgClosed K] [CharZero K] in
/-- The induction behind `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top`, on the
dimension: split off one eigenspace of `g`. -/
private theorem norm_roots_charpoly_mul_aux (d : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = d → ∀ (f g : Module.End K V), Commute f g →
      (⨆ μ : K, g.eigenspace μ = ⊤) → (∀ μ : K, g.eigenspace μ ≠ ⊥ → ‖μ‖ = 1) →
      (f * g).charpoly.roots.map (fun x => ‖x‖) = f.charpoly.roots.map (fun x => ‖x‖) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd f g hfg hg hnorm
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp hd
    rw [Subsingleton.elim (f * g) f]
  have : Nontrivial V := Module.finrank_pos_iff.mp (by rw [hd]; exact hdpos)
  obtain ⟨μ, hμ⟩ : ∃ μ, g.eigenspace μ ≠ ⊥ := by
    by_contra! h
    exact top_ne_bot (hg.symm.trans (iSup_eq_bot.2 h))
  have hμ1 := hnorm μ hμ
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ1
  have hfE : ∀ ν, ∀ x ∈ g.eigenspace ν, f x ∈ g.eigenspace ν := fun ν x hx =>
    Module.End.mem_eigenspace_iff.2 (by
      rw [← Module.End.mul_apply, ← hfg.eq, Module.End.mul_apply,
        Module.End.mem_eigenspace_iff.1 hx, _root_.map_smul])
  have hgE : ∀ ν, ∀ x ∈ g.eigenspace ν, g x ∈ g.eigenspace ν := fun ν x hx => by
    rw [Module.End.mem_eigenspace_iff.1 hx]; exact Submodule.smul_mem _ ν hx
  have hnormR : ∀ (P : Submodule K V) (hP : ∀ x ∈ P, g x ∈ P) (ν : K),
      Module.End.eigenspace (g.restrict hP) ν ≠ ⊥ → ‖ν‖ = 1 := by
    intro P hP ν hν
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hν
    refine hnorm ν ((Submodule.ne_bot_iff _).2
      ⟨x, Module.End.mem_eigenspace_iff.2 ?_, fun h => hx0 (Subtype.ext h)⟩)
    exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hx)
  have hcommR : ∀ (P : Submodule K V) (hfP : ∀ x ∈ P, f x ∈ P) (hgP : ∀ x ∈ P, g x ∈ P),
      Commute (f.restrict hfP) (g.restrict hgP) := fun P hfP hgP =>
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun hfg.eq (x : V))
  have hresR : ∀ (P : Submodule K V) (hfP : ∀ x ∈ P, f x ∈ P) (hgP : ∀ x ∈ P, g x ∈ P)
      (hfgP : ∀ x ∈ P, (f * g) x ∈ P), (f * g).restrict hfgP = f.restrict hfP * g.restrict hgP :=
    fun P hfP hgP hfgP => LinearMap.ext fun x => rfl
  have hmon : ∀ (P Q : Submodule K V) (φ : Module.End K P) (ψ : Module.End K Q),
      φ.charpoly * ψ.charpoly ≠ 0 := fun P Q φ ψ =>
    ((LinearMap.charpoly_monic φ).mul (LinearMap.charpoly_monic ψ)).ne_zero
  by_cases htop : g.eigenspace μ = ⊤
  · have hgμ : g = μ • 1 := by
      ext x
      have hx : x ∈ g.eigenspace μ := by rw [htop]; exact Submodule.mem_top
      simpa using Module.End.mem_eigenspace_iff.1 hx
    rw [hgμ, mul_smul_comm, mul_one, roots_charpoly_smul_end f hμ0, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => by simp [hμ1]
  obtain ⟨W, hW⟩ : ∃ W : Submodule K V, W = ⨆ (ν : K) (_ : ν ≠ μ), g.eigenspace ν := ⟨_, rfl⟩
  have hEW : ∀ ν, ν ≠ μ → g.eigenspace ν ≤ W := fun ν hν => by
    rw [hW]; exact le_iSup₂ (f := fun ν' (_ : ν' ≠ μ) => g.eigenspace ν') ν hν
  have hUW : IsCompl (g.eigenspace μ) W := by
    refine ⟨by rw [hW]; exact g.eigenspaces_iSupIndep μ, ?_⟩
    rw [codisjoint_iff, eq_top_iff, ← hg]
    refine iSup_le fun ν => ?_
    by_cases hν : ν = μ
    · rw [hν]; exact le_sup_left
    · exact le_sup_of_le_right (hEW ν hν)
  have hWinv : ∀ φ : Module.End K V, (∀ ν, ∀ x ∈ g.eigenspace ν, φ x ∈ g.eigenspace ν) →
      ∀ x ∈ W, φ x ∈ W := by
    intro φ hφ
    have hle : W ≤ W.comap φ := by
      conv_lhs => rw [hW]
      exact iSup₂_le fun ν hν y hy => hEW ν hν (hφ ν y hy)
    exact fun x hx => hle hx
  have hfW := hWinv f hfE
  have hgW := hWinv g hgE
  have hfgW : ∀ x ∈ W, (f * g) x ∈ W := fun x hx => hfW _ (hgW x hx)
  have hfgU : ∀ x ∈ g.eigenspace μ, (f * g) x ∈ g.eigenspace μ := fun x hx =>
    hfE μ _ (hgE μ x hx)
  have hWne : W ≠ ⊥ := fun h0 => htop (by
    have h := codisjoint_iff.1 hUW.codisjoint
    rwa [h0, sup_bot_eq] at h)
  have hsum := Submodule.finrank_add_eq_of_isCompl hUW
  have hUpos : Module.finrank K (g.eigenspace μ) ≠ 0 := fun h =>
    hμ (Submodule.finrank_eq_zero.1 h)
  have hWpos : Module.finrank K W ≠ 0 := fun h => hWne (Submodule.finrank_eq_zero.1 h)
  have hltU : Module.finrank K (g.eigenspace μ) < d := by omega
  have hltW : Module.finrank K W < d := by omega
  have hsupU : ⨆ ν, Module.End.eigenspace (g.restrict (hgE μ)) ν = ⊤ := by
    refine eq_top_iff.2 (le_trans ?_ (le_iSup _ μ))
    intro x _
    exact Module.End.mem_eigenspace_iff.2 (Subtype.ext (Module.End.mem_eigenspace_iff.1 x.2))
  have hsupW : ⨆ ν, Module.End.eigenspace (g.restrict hgW) ν = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_iSup, Submodule.map_subtype_top]
    have hmap : ∀ ν, Submodule.map W.subtype (Module.End.eigenspace (g.restrict hgW) ν)
        = W ⊓ g.eigenspace ν := fun ν => (Submodule.inf_genEigenspace g W hgW).symm
    rw [iSup_congr hmap]
    refine le_antisymm (iSup_le fun ν => inf_le_left) ?_
    conv_lhs => rw [hW]
    exact iSup₂_le fun ν hν => le_iSup_of_le ν (le_inf (hEW ν hν) le_rfl)
  rw [charpoly_eq_mul_charpoly_restrict f hUW (hfE μ) hfW,
    charpoly_eq_mul_charpoly_restrict (f * g) hUW hfgU hfgW,
    hresR _ (hfE μ) (hgE μ) hfgU, hresR _ hfW hgW hfgW, roots_mul (hmon _ _ _ _),
    roots_mul (hmon _ _ _ _), Multiset.map_add, Multiset.map_add]
  congr 1
  · exact ih _ hltU rfl _ _ (hcommR _ _ _) hsupU (hnormR _ _)
  · exact ih _ hltW rfl _ _ (hcommR _ _ _) hsupW (hnormR _ _)

omit [IsAlgClosed K] [CharZero K] in
/-- **Norms of the eigenvalues are unchanged by a commuting semisimple factor with eigenvalues of
norm one**: for `f g : End K V` commuting, with `V` spanned by the eigenspaces of `g` and every
eigenvalue of `g` of norm one, the characteristic roots of `f * g` have the same norms, with
multiplicity, as those of `f`.  Induction on `finrank V`, splitting off one eigenspace of `g`
(`Submodule.prodEquivOfIsCompl`, `LinearMap.charpoly_prodMap`, `LinearEquiv.charpoly_conj`). -/
theorem _root_.Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f g : Module.End K V)
    (hfg : Commute f g) (hg : ⨆ μ : K, g.eigenspace μ = ⊤)
    (hnorm : ∀ μ : K, g.eigenspace μ ≠ ⊥ → ‖μ‖ = 1) :
    (f * g).charpoly.roots.map (fun x => ‖x‖) = f.charpoly.roots.map (fun x => ‖x‖) :=
  norm_roots_charpoly_mul_aux _ rfl f g hfg hg hnorm

omit [IsAlgClosed K] in
/-- `Z^N = 1` ⇒ `toLin' Z` is semisimple (`X^N − 1` is squarefree in characteristic zero). -/
theorem isSemisimple_toLin'_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : Module.End.IsSemisimple (Matrix.toLin' Z) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (n := N) (1 : K) (by exact_mod_cast hN.ne')
      one_ne_zero).squarefree ?_
  rw [_root_.map_sub, _root_.map_pow, Polynomial.aeval_X, Polynomial.aeval_C, _root_.map_one,
    ← Matrix.toLin'_pow, hZ, Matrix.toLin'_one, ← Module.End.one_eq_id, sub_self]

omit [IsAlgClosed K] [CharZero K] in
/-- An eigenvalue of a matrix of finite order has norm one. -/
theorem norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) {μ : K} (hμ : Module.End.eigenspace (Matrix.toLin' Z) μ ≠ ⊥) : ‖μ‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hμ
  rw [Module.End.mem_eigenspace_iff] at hv
  have hpow : ∀ m : ℕ, (Matrix.toLin' Z ^ m) v = μ ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, _root_.map_smul, hv, smul_smul, pow_succ]
  have h := hpow N
  rw [← Matrix.toLin'_pow, hZ, Matrix.toLin'_one, LinearMap.id_apply] at h
  have hμN : μ ^ N = 1 :=
    (smul_left_injective K hv0 (show (1 : K) • v = μ ^ N • v by rw [one_smul]; exact h)).symm
  have hn := congrArg norm hμN
  rw [norm_pow, norm_one] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 hn

/-- **The norms of the characteristic roots of `M Z` are those of `M`** for `Z` of finite order
commuting with `M`. -/
theorem norm_roots_charpoly_mul_of_commute_of_pow_eq_one {M Z : Matrix n n K}
    (hMZ : M * Z = Z * M) {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    (M * Z).charpoly.roots.map (fun x => ‖x‖) = M.charpoly.roots.map (fun x => ‖x‖) := by
  have hcomm : Commute (Matrix.toLin' M) (Matrix.toLin' Z) := by
    change Matrix.toLin' M * Matrix.toLin' Z = Matrix.toLin' Z * Matrix.toLin' M
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      hMZ]
  rw [← Matrix.charpoly_toLin' (M * Z), ← Matrix.charpoly_toLin' M, Matrix.toLin'_mul,
    ← Module.End.mul_eq_comp]
  exact Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top _ _ hcomm
    (isSemisimple_toLin'_of_pow_eq_one hN hZ).iSup_eigenspace_eq_top
    (fun μ hμ => norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one hN hZ hμ)

/-- **The pairing of characteristic roots up to a finite-order operator**: if `A B = c Z` with `Z`
commuting with `A` and `Z^N = 1`, the norms of the characteristic roots of `B` are `‖c‖` divided by
those of `A`, with multiplicity (`roots_charpoly_of_mul_eq_smul` at `M := c • A⁻¹`, then
`norm_roots_charpoly_mul_of_commute_of_pow_eq_one`). -/
theorem norm_roots_charpoly_of_mul_eq_smul_mul {A B Z : Matrix n n K} {c : K} (hc : c ≠ 0)
    (h : A * B = c • Z) (hZA : Z * A = A * Z) {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    B.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖) := by
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_mul_eq_smul_mul hc h hN hZ)
  have hAM : A * (c • A⁻¹) = c • (1 : Matrix n n K) := by
    rw [Matrix.mul_smul, mul_nonsing_inv A hA]
  have hB : B = (c • A⁻¹) * Z := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, nonsing_inv_mul A hA,
      Matrix.one_mul]
  have hMZ : (c • A⁻¹) * Z = Z * (c • A⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_nonsing_inv_comm hA hZA]
  rw [hB, norm_roots_charpoly_mul_of_commute_of_pow_eq_one hMZ hN hZ,
    roots_charpoly_of_mul_eq_smul hc hAM, Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => by simp [norm_div]

end AlgClosed

end Matrix
