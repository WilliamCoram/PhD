/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Extend
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.PowerSeries.Basic

/-!
# Convergent power series on polydiscs of arbitrary polyradius

The algebra `T_{n,ρ} = Restricted K ρ` of series converging on the closed polydisc of polyradius
`ρ` is affinoid when every `ρᵢ` is a root of an element of `|K^×|`: for `ρᵢ^{sᵢ} = |cᵢ|⁻¹` the
homomorphism `Tₙ → T_{n,ρ}`, `Xᵢ ↦ cᵢ Xᵢ^{sᵢ}`, is a finite monomorphism with the monomials
`X^λ`, `0 ≤ λᵢ < sᵢ`, as module generators (BGR 6.1.5/4, the first half), so `T_{n,ρ}` is affinoid
by BGR 6.1.1/5. The Banach algebra structure, the density of the polynomials and the
multiplicativity of the Gauss norm at every polyradius (BGR 6.1.5/1–2, roadmap §1.5.1) are Layer 0
(`Restricted/GaussNorm.lean`, `TateAlgebra/Basic.lean`). A series convergent on the open disc of
radius `ρ` but not in `T_{1,ρ}` is recorded (BGR 6.1.5, the remark after 6.1.5/2).

⚠ Deviations from roadmap §1.5.2: the proof follows BGR 6.1.5/4 directly (a finite monomorphism
`Tₙ → T_{n,ρ}`) rather than the roadmap's rescaling to a Weierstrass domain of the unit polydisc;
the "only if" half of BGR 6.1.5/4 and the identification of `|·|_ρ` with the supremum norm
(BGR 6.1.5/5) need the supremum seminorm of Layer 2 and are deferred to it.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.5. Tau Ceti home:
`TauCeti/RingTheory/TateAlgebra/Polydisc.lean`.

## Main results

* `MvPowerSeries.Restricted.rescaleAlgHom` — `Tₙ → T_{n,ρ}`, `Xᵢ ↦ cᵢ Xᵢ^{sᵢ}`, with
  `injective_rescaleAlgHom` and `finite_rescaleAlgHom`.
* `MvPowerSeries.Restricted.coeff_rescaleAlgHom_scaleExp`,
  `MvPowerSeries.Restricted.coeff_rescaleAlgHom_of_forall_ne` — `φ(Σ a_μ X^μ) = Σ a_μ c^μ X^{μ s}`.
* `MvPowerSeries.Restricted.eq_sum_rescaleAlgHom_mul_monomial` — `f = Σ_λ φ(g_λ) X^λ`.
* `MvPowerSeries.Restricted.isAffinoidAlgebra_of_forall_exists_pow_eq_norm` — BGR 6.1.5/4, "if".
* `PowerSeries.exists_summable_not_isRestricted` — the open-disc example (BGR 6.1.5), over a
  complete field.
-/

open Filter Topology MvPowerSeries MvPowerSeries.Restricted

namespace MvPowerSeries.Restricted

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
  (ρ : Fin n → ℝ) [Fact (∀ i, 0 < ρ i)] (s : Fin n → ℕ) (c : Fin n → K)

omit [CompleteSpace K] in
/-- `‖cᵢ Xᵢ^{sᵢ}‖_ρ = 1` when `ρᵢ^{sᵢ} ‖cᵢ‖ = 1`. Source: BGR 6.1.5/4
("Then `|cᵢ Xᵢ^{sᵢ}|_ϱ = 1`"). -/
theorem norm_smul_X_pow (hc : ∀ i, ρ i ^ s i * ‖c i‖ = 1) (i : Fin n) :
    ‖c i • X K ρ i ^ s i‖ = 1 := by
  rw [norm_smul, norm_pow, norm_X, norm_one, one_mul, mul_comm]
  exact hc i

/-- The rescaling homomorphism `Tₙ → T_{n,ρ}`, `Xᵢ ↦ cᵢ Xᵢ^{sᵢ}`, for `ρᵢ^{sᵢ} ‖cᵢ‖ = 1`.
Source: BGR 6.1.5/4 ("we can define a monomorphism `φ : Tₙ → T_{n,ϱ}` by setting
`φ(Xᵢ) := cᵢ Xᵢ^{sᵢ}` (see Proposition 6.1.1/4)"). -/
noncomputable def rescaleAlgHom (hc : ∀ i, ρ i ^ s i * ‖c i‖ = 1) :
    Affinoid.TateAlgebra K n →ₐ[K] Restricted K ρ :=
  aeval (1 : Fin n → ℝ) (fun i ↦ c i • X K ρ i ^ s i) fun i ↦ by
    rw [norm_smul_X_pow ρ s c hc i]
    exact le_rfl

variable {ρ s c} (hc : ∀ i, ρ i ^ s i * ‖c i‖ = 1)

@[simp]
theorem rescaleAlgHom_X (i : Fin n) :
    rescaleAlgHom ρ s c hc (X K (1 : Fin n → ℝ) i) = c i • X K ρ i ^ s i :=
  aeval_X _ i

theorem continuous_rescaleAlgHom : Continuous (rescaleAlgHom ρ s c hc) :=
  continuous_aeval _

omit [CompleteSpace K] in
/-- The coefficient functionals of `T_{n,ρ}` are continuous: `‖a_ν‖ ρ^ν ≤ ‖f‖`. -/
theorem continuous_coeff_restricted (ν : Fin n →₀ ℕ) :
    Continuous fun f : Restricted K ρ ↦ coeff ν f.1 := by
  let L : Restricted K ρ →+ K :=
    { toFun := fun f ↦ coeff ν f.1
      map_zero' := by simp
      map_add' := fun f g ↦ by simp }
  have hpos : 0 < ν.prod (ρ · ^ ·) :=
    Finset.prod_pos fun i _ ↦ pow_pos (Fact.out (p := ∀ i, 0 < ρ i) i) _
  refine AddMonoidHomClass.continuous_of_bound L (ν.prod (ρ · ^ ·))⁻¹ fun f ↦ ?_
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  exact norm_coeff_mul_prod_le ρ f ν

variable (s) in
/-- The exponent `μ ↦ (μᵢ sᵢ)ᵢ`: the rescaling sends `X^μ` to `c^μ X^{μ s}`. -/
noncomputable def scaleExp (μ : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ μ i * s i) (Set.toFinite _)

omit [Fact (∀ i, 0 < ρ i)] in
@[simp]
theorem scaleExp_apply (μ : Fin n →₀ ℕ) (i : Fin n) : scaleExp s μ i = μ i * s i :=
  rfl

omit [Fact (∀ i, 0 < ρ i)] in
theorem scaleExp_injective (hs : ∀ i, s i ≠ 0) : Function.Injective (scaleExp s) :=
  fun _ _ h ↦ Finsupp.ext fun i ↦
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (hs i)) (DFunLike.congr_fun h i)

omit [IsUltrametricDist K] [CompleteSpace K] [Fact (∀ i, 0 < ρ i)] in
/-- `C a ∏ (cᵢ Xᵢ^{sᵢ})^{tᵢ} = a c^t X^{t s}` among polynomials. -/
theorem C_mul_prod_rescale (a : K) (t : Fin n →₀ ℕ) :
    MvPolynomial.C a * t.prod (fun i k ↦ (MvPolynomial.C (c i) * MvPolynomial.X i ^ s i) ^ k) =
      MvPolynomial.monomial (scaleExp s t) (a * ∏ i, c i ^ t i) := by
  rw [Finsupp.prod_fintype _ _ fun i ↦ pow_zero _, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ fun i ↦ pow_zero _, map_mul, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← pow_mul', scaleExp_apply, mul_assoc]

omit [CompleteSpace K] [Fact (∀ i, 0 < ρ i)] in
/-- The terms of the rescaling: `a φ(X)^t = a c^t X^{t s}`. -/
theorem algebraMap_mul_prod_rescale (a : K) (t : Fin n →₀ ℕ) :
    algebraMap K (Restricted K ρ) a * t.prod (fun i k ↦ (c i • X K ρ i ^ s i) ^ k) =
      MvPolynomial.toRestricted ρ (MvPolynomial.monomial (scaleExp s t) (a * ∏ i, c i ^ t i)) := by
  have hx : ∀ i, c i • X K ρ i ^ s i =
      MvPolynomial.toRestricted ρ (MvPolynomial.C (c i) * MvPolynomial.X i ^ s i) := fun i ↦ by
    rw [map_mul, map_pow, MvPolynomial.toRestricted_C, MvPolynomial.toRestricted_X,
      Algebra.smul_def, algebraMap_apply]
  simp_rw [hx, ← map_pow]
  rw [← map_finsuppProd, algebraMap_apply, ← MvPolynomial.toRestricted_C, ← map_mul,
    C_mul_prod_rescale]

/-- The coefficients of the rescaling, as a sum over the exponents of `Tₙ`. -/
theorem hasSum_coeff_rescaleAlgHom (g : Affinoid.TateAlgebra K n) (ν : Fin n →₀ ℕ) :
    HasSum (fun t ↦ if scaleExp s t = ν then coeff t g.1 * ∏ i, c i ^ t i else 0)
      (coeff ν (rescaleAlgHom ρ s c hc g).1) := by
  have h : HasSum (fun t : Fin n →₀ ℕ ↦ algebraMap K (Restricted K ρ) (coeff t g.1) *
      t.prod fun i k ↦ (c i • X K ρ i ^ s i) ^ k) (rescaleAlgHom ρ s c hc g) :=
    hasSum_eval₂ (norm_algebraMap_le_one_mul (B := Restricted K ρ))
      (norm_prod_pow_le_of_norm_le 1 (fun i ↦ c i • X K ρ i ^ s i)
        fun i ↦ (norm_smul_X_pow ρ s c hc i).le) g
  let L : Restricted K ρ →+ K :=
    { toFun := fun f ↦ coeff ν f.1
      map_zero' := by simp
      map_add' := fun f g ↦ by simp }
  convert h.map L (continuous_coeff_restricted (ρ := ρ) ν) using 1
  · funext t
    change _ = coeff ν (algebraMap K (Restricted K ρ) (coeff t g.1) *
        t.prod fun i k ↦ (c i • X K ρ i ^ s i) ^ k).1
    rw [algebraMap_mul_prod_rescale, MvPolynomial.val_toRestricted, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_monomial]
  · rfl

/-- The coefficient of `φ(g)` at `μ s` is `a_μ c^μ`. -/
theorem coeff_rescaleAlgHom_scaleExp (hs : ∀ i, s i ≠ 0) (g : Affinoid.TateAlgebra K n)
    (μ : Fin n →₀ ℕ) :
    coeff (scaleExp s μ) (rescaleAlgHom ρ s c hc g).1 = coeff μ g.1 * ∏ i, c i ^ μ i := by
  have h1 := hasSum_single (f := fun t ↦
    if scaleExp s t = scaleExp s μ then coeff t g.1 * ∏ i, c i ^ t i else 0) μ
    fun t ht ↦ if_neg fun h ↦ ht (scaleExp_injective hs h)
  rw [if_pos rfl] at h1
  exact (hasSum_coeff_rescaleAlgHom hc g (scaleExp s μ)).unique h1

/-- The coefficients of `φ(g)` away from the exponents `μ s` vanish. -/
theorem coeff_rescaleAlgHom_of_forall_ne (g : Affinoid.TateAlgebra K n) {ν : Fin n →₀ ℕ}
    (hν : ∀ μ, scaleExp s μ ≠ ν) : coeff ν (rescaleAlgHom ρ s c hc g).1 = 0 := by
  refine (hasSum_coeff_rescaleAlgHom hc g ν).unique ?_
  simp_rw [if_neg (hν _)]
  exact hasSum_zero

/-- The rescaling acts on coefficients by `a_μ ↦ a_μ c^μ` placed at `μ s`; in particular it is
injective. Source: BGR 6.1.5/4 ("a monomorphism"). -/
theorem injective_rescaleAlgHom (hs : ∀ i, s i ≠ 0) :
    Function.Injective (rescaleAlgHom ρ s c hc) := by
  refine (injective_iff_map_eq_zero _).2 fun g hg ↦ Restricted.ext (MvPowerSeries.ext fun μ ↦ ?_)
  have h := coeff_rescaleAlgHom_scaleExp hc hs g μ
  rw [hg, val_zero, map_zero] at h
  have hprod : ∏ i, c i ^ μ i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ fun h0 ↦ by
    simpa [h0] using hc i
  rw [val_zero, map_zero]
  exact (mul_eq_zero.1 h.symm).resolve_right hprod

omit [CompleteSpace K] in
include hc in
/-- The series `g_λ = Σ_μ a_{μs+λ} c^{−μ} X^μ` of BGR 6.1.5/4 lies in `Tₙ`, since
`|a_{μs+λ} c^{−μ}| = |a_{μs+λ}| ϱ^{μs+λ} ϱ^{−λ} → 0`. -/
theorem isRestricted_shiftCoeff (hs : ∀ i, s i ≠ 0) (f : Restricted K ρ)
    (l : Fin n →₀ ℕ) :
    IsRestricted (1 : Fin n → ℝ) (fun μ : Fin n →₀ ℕ ↦
      coeff (Finsupp.ofSupportFinite (fun i ↦ μ i * s i) (Set.toFinite _) + l) f.1 *
        ∏ i, (c i)⁻¹ ^ μ i : MvPowerSeries (Fin n) K) := by
  have hρ : ∀ i, 0 < ρ i := Fact.out
  have hnorm : ∀ i, ‖(c i)⁻¹‖ = ρ i ^ s i := fun i ↦ by
    rw [norm_inv]
    exact (eq_inv_of_mul_eq_one_left (hc i)).symm
  have hl : 0 < l.prod (ρ · ^ ·) := Finset.prod_pos fun i _ ↦ pow_pos (hρ i) _
  have hinj : Function.Injective fun μ ↦ scaleExp s μ + l :=
    fun _ _ h ↦ scaleExp_injective hs (add_right_cancel h)
  have hf : Tendsto (fun t ↦ ‖coeff t f.1‖ * t.prod (ρ · ^ ·)) cofinite (𝓝 0) := f.2
  have h := (hf.comp hinj.tendsto_cofinite).mul_const (l.prod (ρ · ^ ·))⁻¹
  rw [zero_mul] at h
  refine h.congr fun μ ↦ ?_
  show ‖coeff (scaleExp s μ + l) f.1‖ * (scaleExp s μ + l).prod (ρ · ^ ·) *
      (l.prod (ρ · ^ ·))⁻¹ =
    ‖coeff (scaleExp s μ + l) f.1 * ∏ i, (c i)⁻¹ ^ μ i‖ * μ.prod ((1 : Fin n → ℝ) · ^ ·)
  rw [Finsupp.prod_add_index' (fun i ↦ pow_zero _) (fun i _ _ ↦ pow_add _ _ _), mul_assoc,
    mul_assoc, mul_inv_cancel₀ hl.ne', mul_one, norm_mul, norm_prod,
    Finsupp.prod_fintype _ _ fun i ↦ pow_zero _, Finsupp.prod_fintype _ _ fun i ↦ pow_zero _]
  simp only [norm_pow, hnorm, scaleExp_apply, Pi.one_apply, one_pow, Finset.prod_const_one,
    mul_one, ← pow_mul, mul_comm (s _)]

/-- The series `g_λ = Σ_μ a_{μs+λ} c^{−μ} X^μ ∈ Tₙ` of BGR 6.1.5/4. -/
noncomputable def shiftCoeffSeries (hs : ∀ i, s i ≠ 0) (f : Restricted K ρ) (l : Fin n →₀ ℕ) :
    Affinoid.TateAlgebra K n :=
  ⟨fun μ ↦ coeff (scaleExp s μ + l) f.1 * ∏ i, (c i)⁻¹ ^ μ i, isRestricted_shiftCoeff hc hs f l⟩

omit [CompleteSpace K] in
theorem coeff_shiftCoeffSeries (hs : ∀ i, s i ≠ 0) (f : Restricted K ρ) (l μ : Fin n →₀ ℕ) :
    coeff μ (shiftCoeffSeries hc hs f l).1 = coeff (scaleExp s μ + l) f.1 * ∏ i, (c i)⁻¹ ^ μ i :=
  rfl

/-- `φ(g_λ)` has the coefficient `a_{μs+λ}` at `μ s`. -/
theorem coeff_rescaleAlgHom_shiftCoeffSeries (hs : ∀ i, s i ≠ 0) (f : Restricted K ρ)
    (l μ : Fin n →₀ ℕ) :
    coeff (scaleExp s μ) (rescaleAlgHom ρ s c hc (shiftCoeffSeries hc hs f l)).1 =
      coeff (scaleExp s μ + l) f.1 := by
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 ↦ by simpa [h0] using hc i
  rw [coeff_rescaleAlgHom_scaleExp hc hs, coeff_shiftCoeffSeries, mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, inv_mul_cancel₀ (hc0 _), one_pow, Finset.prod_const_one, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] [Fact (∀ i, 0 < ρ i)] in
/-- The box `{λ | ∀ i, λᵢ < sᵢ}` of exponents of the module generators. -/
theorem mem_box_iff (l : Fin n →₀ ℕ) :
    l ∈ (Fintype.piFinset fun i ↦ Finset.range (s i)).map
      Finsupp.equivFunOnFinite.symm.toEmbedding ↔ ∀ i, l i < s i := by
  simp [Finset.mem_map_equiv, Fintype.mem_piFinset]

omit [CompleteSpace K] [Fact (∀ i, 0 < ρ i)] in
/-- The coefficients of `F X^λ`. -/
theorem coeff_mul_monomial_one (F : Restricted K ρ) (l ν : Fin n →₀ ℕ) :
    coeff ν (F * monomial ρ l 1).1 = if l ≤ ν then coeff (ν - l) F.1 else 0 := by
  rw [val_mul, val_monomial, MvPowerSeries.coeff_mul_monomial, mul_one]

/-- **BGR 6.1.5/4**: `f = Σ_λ φ(g_λ) X^λ`, the sum over the box `0 ≤ λᵢ < sᵢ`. -/
theorem eq_sum_rescaleAlgHom_mul_monomial (hs : ∀ i, s i ≠ 0) (f : Restricted K ρ) :
    f = ∑ l ∈ (Fintype.piFinset fun i ↦ Finset.range (s i)).map
        Finsupp.equivFunOnFinite.symm.toEmbedding,
      rescaleAlgHom ρ s c hc (shiftCoeffSeries hc hs f l) * monomial ρ l 1 := by
  refine Restricted.ext (MvPowerSeries.ext fun ν ↦ ?_)
  rw [val_sum, map_sum]
  simp only [coeff_mul_monomial_one]
  let r : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i ↦ ν i % s i
  let q : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i ↦ ν i / s i
  have hr : ∀ i, r i = ν i % s i := fun _ ↦ rfl
  have hq : ∀ i, q i = ν i / s i := fun _ ↦ rfl
  have hrν : r ≤ ν := fun i ↦ (hr i).trans_le (Nat.mod_le _ _)
  have hsub : ν - r = scaleExp s q := Finsupp.ext fun i ↦ by
    rw [Finsupp.tsub_apply, scaleExp_apply, hr, hq]
    have := Nat.div_add_mod (ν i) (s i)
    rw [Nat.mul_comm] at this
    omega
  rw [Finset.sum_eq_single r]
  · rw [if_pos hrν, hsub, coeff_rescaleAlgHom_shiftCoeffSeries hc hs f r q, ← hsub,
      tsub_add_cancel_of_le hrν]
  · intro b hb hbr
    split_ifs with hbν
    · refine coeff_rescaleAlgHom_of_forall_ne hc _ fun μ hμ ↦ hbr (Finsupp.ext fun i ↦ ?_)
      have hbi := (mem_box_iff b).1 hb i
      have hμi := DFunLike.congr_fun hμ i
      rw [scaleExp_apply, Finsupp.tsub_apply] at hμi
      have hνi : ν i = μ i * s i + b i := by have := hbν i; omega
      rw [hr, hνi, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbi]
    · rfl
  · intro hr'
    exact absurd ((mem_box_iff r).2 fun i ↦ (hr i).trans_lt
      (Nat.mod_lt _ (Nat.pos_of_ne_zero (hs i)))) hr'

/-- **`T_{n,ρ}` is a finite `Tₙ`-module** via the rescaling, generated by the monomials `X^λ`,
`0 ≤ λᵢ < sᵢ`: `f = Σ_λ φ(g_λ) X^λ`. Source: BGR 6.1.5/4 ("We have `f = Σ_λ φ(g_λ) X^λ` so that
`T_{n,ϱ}` is a finite `Tₙ`-module via `φ`; the monomials `X^λ`, `0 ≤ λᵢ < sᵢ`, are generators"). -/
theorem finite_rescaleAlgHom (hs : ∀ i, s i ≠ 0) :
    (rescaleAlgHom ρ s c hc).toRingHom.Finite := by
  classical
  letI := (rescaleAlgHom ρ s c hc).toRingHom.toAlgebra
  refine ⟨⟨((Fintype.piFinset fun i ↦ Finset.range (s i)).map
    Finsupp.equivFunOnFinite.symm.toEmbedding).image fun l ↦ monomial ρ l (1 : K),
    eq_top_iff.2 fun f _ ↦ ?_⟩⟩
  rw [eq_sum_rescaleAlgHom_mul_monomial hc hs f]
  refine Submodule.sum_mem _ fun l hl ↦ ?_
  have h : rescaleAlgHom ρ s c hc (shiftCoeffSeries hc hs f l) * monomial ρ l 1 =
      shiftCoeffSeries hc hs f l • monomial ρ l (1 : K) :=
    (Algebra.smul_def _ _).symm
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2
    (Finset.mem_image_of_mem _ hl)))

/-- **BGR 6.1.5/4, the "if" half**: `T_{n,ρ}` is affinoid when every `ρᵢ` is a root of an element
of `|K^×|`. Source: BGR 6.1.5/4 ("Thus, `T_{n,ϱ}` is `k`-affinoid by Proposition 6.1.1/5, and half
of the theorem is proved"). -/
theorem isAffinoidAlgebra_of_forall_exists_pow_eq_norm
    (h : ∀ i, ∃ (s : ℕ) (c : K), s ≠ 0 ∧ c ≠ 0 ∧ ρ i ^ s = ‖c‖) :
    IsAffinoidAlgebra K (Restricted K ρ) := by
  choose s c hs hc0 h using h
  have hc : ∀ i, ρ i ^ s i * ‖(c i)⁻¹‖ = 1 := fun i ↦ by
    rw [norm_inv, ← h i, mul_inv_cancel₀ (pow_ne_zero _ (Fact.out (p := ∀ i, 0 < ρ i) i).ne')]
  exact IsAffinoidAlgebra.of_finite_tateAlgebra (rescaleAlgHom ρ s (fun i ↦ (c i)⁻¹) hc)
    (continuous_rescaleAlgHom hc) (finite_rescaleAlgHom hc hs)

end MvPowerSeries.Restricted

namespace PowerSeries

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- **The open-disc example** (BGR 6.1.5): for every `ρ > 0` there is a power series converging at
every `x` with `‖x‖ < ρ` which is not in `T_{1,ρ}`, namely `Σ aₙ Xⁿ` with `‖aₙ‖ ρⁿ ∈ [‖π‖⁻¹, 1]`.
Source: BGR 6.1.5 ("there are power series `f = Σ a_ν X^ν` converging on `B⁻(0, ϱ)`, which do not
satisfy the condition `lim |a_ν| ϱ^ν = 0`, so that `f ∉ T_{1,ϱ}` in this case"). -/
theorem exists_summable_not_isRestricted {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ f : PowerSeries K, (∀ x : K, ‖x‖ < ρ → Summable fun ν ↦ coeff ν f * x ^ ν) ∧
      ¬ IsRestricted ρ f := by
  obtain ⟨π, hπ⟩ := NormedField.exists_one_lt_norm K
  have hπ0 : 0 < ‖π‖ := by linarith
  have hk : ∀ ν : ℕ, ∃ k : ℤ, ‖π‖ ^ k ≤ (ρ ^ ν)⁻¹ ∧ (ρ ^ ν)⁻¹ < ‖π‖ ^ (k + 1) := fun ν ↦
    exists_mem_Ico_zpow (inv_pos.2 (pow_pos hρ ν)) hπ
  choose k hk₁ hk₂ using hk
  refine ⟨PowerSeries.mk fun ν ↦ π ^ k ν, fun x hx ↦ ?_, fun hres ↦ ?_⟩
  · refine Summable.of_norm_bounded
      (summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hx)) fun ν ↦ ?_
    rw [PowerSeries.coeff_mk, norm_mul, norm_zpow, norm_pow, div_pow, ← inv_mul_eq_div]
    exact mul_le_mul_of_nonneg_right (hk₁ ν) (by positivity)
  · rw [PowerSeries.isRestricted_iff] at hres
    obtain ⟨ν, hν⟩ := (hres.eventually (gt_mem_nhds (inv_pos.2 hπ0))).exists
    rw [PowerSeries.coeff_mk, norm_zpow] at hν
    have h2 := hk₂ ν
    rw [zpow_add₀ hπ0.ne', zpow_one] at h2
    have hρν : 0 < ρ ^ ν := pow_pos hρ ν
    -- multiply `(ρ^ν)⁻¹ < ‖π‖^k ‖π‖` by `ρ^ν ‖π‖⁻¹`
    have h3 := mul_lt_mul_of_pos_right h2 (mul_pos hρν (inv_pos.2 hπ0))
    have hl : (ρ ^ ν)⁻¹ * (ρ ^ ν * ‖π‖⁻¹) = ‖π‖⁻¹ := by
      rw [← mul_assoc, inv_mul_cancel₀ hρν.ne', one_mul]
    have hr : ‖π‖ ^ k ν * ‖π‖ * (ρ ^ ν * ‖π‖⁻¹) = ‖π‖ ^ k ν * ρ ^ ν := by
      rw [mul_comm (ρ ^ ν), ← mul_assoc, mul_assoc (‖π‖ ^ k ν), mul_inv_cancel₀ hπ0.ne', mul_one]
    rw [hl, hr] at h3
    exact absurd hν (not_lt.2 h3.le)

end PowerSeries
