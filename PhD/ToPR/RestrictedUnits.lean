import PhD.ToPR.PowerBounded
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted
import PhD.ToPR.RestrictedIso
import Mathlib.RingTheory.Polynomial.Nilpotent

namespace Restricted

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [NormMulClass S] {c : ℝ}
  [StrongPos (fun _ : Unit ↦ c)]

/-- Under `[NormMulClass S]` and `c ≤ 1`, a restricted power series whose constant
coefficient vanishes and whose higher coefficients are topologically nilpotent has Gauss
norm strictly less than `1`. -/
lemma gaussNorm_lt_one_of_coeff_topNilp (hc1 : c ≤ 1) (hc0 : 0 ≤ c)
    (g : PowerSeries.Restricted S c)
    (h0 : PowerSeries.coeff 0 g.1 = 0)
    (hpos : ∀ v, 0 < v → IsTopologicallyNilpotent (PowerSeries.coeff v g.1)) :
    Restricted.gaussNorm S c g < 1 := by
  -- The Gauss norm is achieved by some coefficient `‖coeff a g.1‖ * c^a`.
  obtain ⟨a, ha⟩ := Restricted.gaussNorm_achieved' c hc0 g
  rw [← ha]
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · -- For `a = 0`, the term is `‖0‖ * 1 = 0`.
    rw [h0]; simp
  · -- For `a ≥ 1`, `coeff a g.1` is topologically nilpotent, so `‖coeff a g.1‖ < 1`
    -- (using `NormMulClass`); and `c^a ≤ 1` since `c ≤ 1`.
    have h_norm : ‖PowerSeries.coeff a g.1‖ < 1 :=
      IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass.mp (hpos a ha_pos)
    have h_pow : c ^ a ≤ 1 := pow_le_one₀ hc0 hc1
    calc ‖PowerSeries.coeff a g.1‖ * c ^ a
        ≤ ‖PowerSeries.coeff a g.1‖ * 1 :=
            mul_le_mul_of_nonneg_left h_pow (norm_nonneg _)
      _ = ‖PowerSeries.coeff a g.1‖ := mul_one _
      _ < 1 := h_norm

lemma isTopologicallyNilpotent_of_coeff_topNilp (hc1 : c ≤ 1) (hc0 : 0 ≤ c)
    (g : PowerSeries.Restricted S c)
    (h0 : PowerSeries.coeff 0 g.1 = 0)
    (hpos : ∀ v, 0 < v → IsTopologicallyNilpotent (PowerSeries.coeff v g.1)) :
    IsTopologicallyNilpotent g :=
  IsTopologicallyNilpotent.of_norm_lt_one
    (gaussNorm_lt_one_of_coeff_topNilp hc1 hc0 g h0 hpos)

end Restricted

variable (R : Type*) [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R] (c : ℝ)
  [CompleteSpace R]

lemma Restricted.residue_isUnit [StrongPos (fun _ : Unit ↦ c)]
    [NormMulClass R] (hc1 : c ≤ 1) (f : PowerSeries.Restricted
      (TopologicalRing.powerBoundedSubring.toSubring R) c)
    (h0 : IsUnit (Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R)
      (PowerSeries.coeff 0 f.1))) (hpos : ∀ v, 0 < v →
      IsTopologicallyNilpotent (PowerSeries.coeff v f.1)) : IsUnit f := by
  have ha0 : IsUnit (PowerSeries.coeff 0 f.1) :=
      (TopologicalRing.bar_isUnit (A := R) (PowerSeries.coeff 0 f.1)).mpr h0
  -- Promote `ha0` to a unit witness `u₀` of `R°` with inverse `b₀`.
  obtain ⟨u₀, hu₀⟩ := ha0
  -- The constant power series `C(b₀⁻¹) = C(u₀.inv)` in `Restricted R° c` is a unit
  -- with constant coefficient `b₀⁻¹`; its product with `f` has constant coefficient `1`.
  -- Set `g := 1 - C(b₀⁻¹) * f`; this lives in `Restricted R° c` and we have:
  --   * `coeff 0 g = 1 - (u₀.inv) * (u₀.val) = 0`;
  --   * for `v > 0`, `coeff v g = -(u₀.inv) * (coeff v f)` is topologically nilpotent
  --     (product of a power-bounded element and a topologically-nilpotent one).
  let Cinv : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c :=
    ⟨PowerSeries.C (u₀.inv), PowerSeries.isRestricted_C c u₀.inv⟩
  let g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c :=
    1 - Cinv * f
  -- **Sub-claim** (BGR Lemma 4.18): `g` has constant coefficient `0` and topologically
  -- nilpotent higher coefficients, hence is itself topologically nilpotent in
  -- `Restricted R° c`.
  have hc0 : (0 : ℝ) ≤ c := le_of_lt (StrongPos_pos (fun _ : Unit ↦ c) ())
  -- Underlying-PowerSeries identity: `g.1 = 1 - C(u₀.inv) * f.1`.
  have h_g_val : g.1 = (1 : PowerSeries _) - PowerSeries.C u₀.inv * f.1 := rfl
  -- `coeff 0 g = 0`: by construction `Cinv * f` has constant coefficient `u₀.inv * u₀.val = 1`.
  have hg_coeff_0 : PowerSeries.coeff 0 g.1 = 0 := by
    rw [h_g_val, map_sub, PowerSeries.coeff_zero_one, PowerSeries.coeff_C_mul,
      ← hu₀, u₀.inv_val, sub_self]
  -- For `v > 0`, `coeff v g = -u₀.inv * coeff v f`: top nilp because product in
  -- `IsLinearTopology` ring `R°`.
  have hg_coeff_pos : ∀ v, 0 < v →
      IsTopologicallyNilpotent (PowerSeries.coeff v g.1) := by
    intro v hv
    have h_eq : PowerSeries.coeff v g.1 = (-u₀.inv) * PowerSeries.coeff v f.1 := by
      rw [h_g_val, map_sub, PowerSeries.coeff_C_mul]
      simp [PowerSeries.coeff_one, hv.ne']
    rw [h_eq]
    -- Use `IsTopologicallyNilpotent.mul_left` in `R°` (instance
    -- `TopologicalRing.powerBoundedSubring_isLinearTopology`).
    exact IsTopologicallyNilpotent.mul_left (-u₀.inv) (hpos v hv)
  -- Apply Lemma 4.18.
  have hg_topNilp : IsTopologicallyNilpotent g :=
    Restricted.isTopologicallyNilpotent_of_coeff_topNilp hc1 hc0 g hg_coeff_0 hg_coeff_pos
  -- Now `1 - g = Cinv * f` is a unit by the ultrametric geometric series
  -- (`isUnit_one_sub_of_isTopologicallyNilpotent`).
  have h_one_sub_g_unit : IsUnit (1 - g) :=
    TopologicalRing.isUnit_one_sub_of_isTopologicallyNilpotent hg_topNilp
  -- `1 - g = Cinv * f`, so it suffices to show `Cinv` is a unit; then `f` is the product
  -- of `Cinv⁻¹` and `1 - g`, both units.
  have h_eq : (1 - g) = Cinv * f := by simp [g]
  have h_prod_unit : IsUnit (Cinv * f) := h_eq ▸ h_one_sub_g_unit
  -- `Cinv` is a unit, with inverse the constant series `C(u₀.val)`.
  have hCinv_unit : IsUnit Cinv := by
    refine ⟨⟨Cinv,
      ⟨PowerSeries.C u₀.val, PowerSeries.isRestricted_C c u₀.val⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show PowerSeries.C u₀.inv * PowerSeries.C u₀.val = 1
      rw [← map_mul, u₀.inv_val]; exact map_one _
    · apply Subtype.ext
      show PowerSeries.C u₀.val * PowerSeries.C u₀.inv = 1
      rw [← map_mul, u₀.val_inv]; exact map_one _
  -- So `f = Cinv⁻¹ * (Cinv * f) = Cinv⁻¹ * (1 - g)` is a product of units.
  obtain ⟨Cinv_unit, hCinv_eq⟩ := hCinv_unit
  set Cinv_inv :
      PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c :=
    (Cinv_unit⁻¹ : Units _).val with hCinv_inv_def
  have hCinv_inv_unit : IsUnit Cinv_inv :=
    hCinv_inv_def ▸ (Units.isUnit Cinv_unit⁻¹)
  have hCinv_mul : Cinv_inv * Cinv = 1 := by
    simp [hCinv_inv_def, ← hCinv_eq]
  have hf_eq : f = Cinv_inv * (1 - g) := by
    calc f = 1 * f := (one_mul f).symm
      _ = (Cinv_inv * Cinv) * f := by rw [hCinv_mul]
      _ = Cinv_inv * (Cinv * f) := mul_assoc _ _ _
      _ = Cinv_inv * (1 - g) := by rw [← h_eq]
  rw [hf_eq]
  exact hCinv_inv_unit.mul h_one_sub_g_unit


lemma Restricted.PowerBounded_isUnit
    [StrongPos (fun _ : Unit ↦ c)] [NormMulClass R] (hc : c ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c)
    (h0 : IsUnit (PowerSeries.coeff 0 f.1))
    (hpos : ∀ v, 0 < v → IsTopologicallyNilpotent (PowerSeries.coeff v f.1)) :
    IsUnit f := by
  -- Key ring homomorphism: `coeff 0` viewed as a map `Restricted R° c →+* R°`.
  let φ : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c →+*
        (TopologicalRing.powerBoundedSubring.toSubring R) :=
    RingHom.comp
      (PowerSeries.constantCoeff (R := (TopologicalRing.powerBoundedSubring.toSubring R)))
      (PowerSeries.isSubring c).subtype
  have hφ : ∀ f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c,
      φ f = PowerSeries.coeff 0 f.1 := fun _ => by
    show PowerSeries.constantCoeff _ = PowerSeries.coeff 0 _
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine (Restricted.residue_isUnit R c hc f ?_ hpos)
  exact h0.map (Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R))

/-! ## API for the coefficient-wise residue map `Restricted R° c →+* R̃[X]`

For `1 ≤ c`, a restricted power series in `R°⟨x⟩` has coefficients with norm tending to
zero. Combined with `[NormMulClass R]` (under which `‖a‖ < 1 ↔ IsTopologicallyNilpotent a`),
this means the coefficients are *eventually* topologically nilpotent. Reducing
coefficient-wise modulo the topologically-nilpotent ideal `R°° ⊆ R°` therefore gives a
function `ℕ → R̃` with finite support — i.e., a polynomial in `R̃ = R° / R°°`.

This section builds up that map in stages: the eventually-vanishing lemma, the
finite-support claim for the residue function, the underlying `Finsupp`, the polynomial,
and finally the ring-hom packaging. Together with the standard fact that units in `R̃[X]`
are constants when `R̃` is reduced, this is the missing ingredient for the forward
direction of `PowerBounded_isUnit_iff` (BGR Lemma 4.19). -/

namespace Restricted

open Filter Topology

variable {R : Type*} [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R] {c : ℝ}
  [CompleteSpace R] [NormMulClass R]

/-- For `1 ≤ c`, the coefficients of a restricted power series in
`Restricted R° c = R°⟨x⟩` are eventually topologically nilpotent.

The restricted condition gives `‖coeff v f‖ * c^v → 0` (cofinite, which is `atTop` on `ℕ`).
Since `c^v ≥ 1` for `v ≥ 0`, this forces `‖coeff v f‖ → 0`. The `[NormMulClass]`
equivalence `‖a‖ < 1 ↔ IsTopologicallyNilpotent a` then converts the eventual estimate
into eventual topological nilpotence. -/
lemma coeff_eventually_topNilp [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    ∀ᶠ v in Filter.atTop,
      IsTopologicallyNilpotent (PowerSeries.coeff v f.1) := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  -- `‖coeff v f‖ * c^v → 0` in `cofinite = atTop`.
  have h_restr : Tendsto (fun v : ℕ => ‖PowerSeries.coeff v f.1‖ * c ^ v) cofinite (𝓝 0) :=
    (PowerSeries.isRestricted_iff c f.1).mp f.2
  rw [Nat.cofinite_eq_atTop] at h_restr
  -- Eventually `‖coeff v f‖ * c^v < 1`.
  have h_lt_one : ∀ᶠ v in atTop, ‖PowerSeries.coeff v f.1‖ * c ^ v < 1 := by
    have := h_restr.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [this] with v hv
    -- `hv : dist (‖coeff v f‖ * c^v) 0 < 1`. Convert to a plain `< 1`.
    rw [Real.dist_eq, sub_zero] at hv
    have hpos : 0 ≤ ‖PowerSeries.coeff v f.1‖ * c ^ v :=
      mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le _)
    rwa [abs_of_nonneg hpos] at hv
  -- Since `1 ≤ c^v`, conclude `‖coeff v f‖ < 1`, hence top-nilp.
  filter_upwards [h_lt_one] with v hv_lt
  have hcv : (1 : ℝ) ≤ c ^ v := one_le_pow₀ hc
  have h_norm_lt : ‖PowerSeries.coeff v f.1‖ < 1 :=
    calc ‖PowerSeries.coeff v f.1‖
        = ‖PowerSeries.coeff v f.1‖ * 1 := (mul_one _).symm
      _ ≤ ‖PowerSeries.coeff v f.1‖ * c ^ v :=
          mul_le_mul_of_nonneg_left hcv (norm_nonneg _)
      _ < 1 := hv_lt
  exact IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass.mpr h_norm_lt

/-- For `1 ≤ c`, the support of the residue function
`v ↦ (Ideal.Quotient.mk R°°) (coeff v f.1)` is finite: outside the (finite)
initial segment where `‖coeff v f‖ ≥ 1`, the coefficients are topologically nilpotent
and hence vanish modulo `R°°`. -/
lemma residueCoeff_support_finite [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    (Function.support fun v : ℕ =>
        Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R)
          (PowerSeries.coeff v f.1)).Finite := by
  obtain ⟨N, hN⟩ := (coeff_eventually_topNilp hc f).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro v hv
  simp only [Function.mem_support, ne_eq] at hv
  by_contra hvN
  apply hv
  rw [Ideal.Quotient.eq_zero_iff_mem,
      TopologicalRing.mem_IsTopologicallyNilpotent_ideal_iff]
  -- We have `IsTopologicallyNilpotent (coeff v f.1)` in `R°`; convert to top-nilp at the
  -- `R`-level via the norm characterisation (the subring norm on `R°` agrees definitionally
  -- with the restriction of the ambient norm on `R`).
  have h_in_sub : IsTopologicallyNilpotent (PowerSeries.coeff v f.1) :=
    hN v (Nat.le_of_not_lt hvN)
  rw [IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass] at h_in_sub
  exact IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass.mpr h_in_sub

/-- The residue of a restricted power series `f ∈ R°⟨x⟩` as a `Finsupp ℕ R̃`, i.e. a
finitely-supported coefficient sequence in the residue ring `R̃ = R° / R°°`. -/
noncomputable def residueFinsupp [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    ℕ →₀ ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.IsTopologicallyNilpotent_ideal R) :=
  Finsupp.ofSupportFinite
    (fun v => Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R)
      (PowerSeries.coeff v f.1))
    (residueCoeff_support_finite hc f)

/-- The residue of a restricted power series, viewed as a polynomial in `R̃[X]`. -/
noncomputable def residuePolynomial [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    Polynomial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.IsTopologicallyNilpotent_ideal R) :=
  ⟨residueFinsupp hc f⟩

@[simp]
lemma residuePolynomial_coeff [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) (v : ℕ) :
    (residuePolynomial hc f).coeff v =
      Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R)
        (PowerSeries.coeff v f.1) := by
  show (residueFinsupp hc f) v = _
  simp [residueFinsupp, Finsupp.ofSupportFinite]

@[simp]
lemma residuePolynomial_zero [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c) :
    residuePolynomial hc
        (0 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) = 0 := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_coeff, Polynomial.coeff_zero]
  show Ideal.Quotient.mk _
      (PowerSeries.coeff v
        (0 : PowerSeries (TopologicalRing.powerBoundedSubring.toSubring R))) = 0
  rw [map_zero, map_zero]

@[simp]
lemma residuePolynomial_one [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c) :
    residuePolynomial hc
        (1 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) = 1 := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_coeff]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (1 : PowerSeries _)) = _
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [PowerSeries.coeff_zero_one, Polynomial.coeff_one_zero]; rfl
  · rw [PowerSeries.coeff_one, if_neg hv.ne']
    rw [map_zero, Polynomial.coeff_one, if_neg hv.ne']

lemma residuePolynomial_add [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residuePolynomial hc (f + g) =
      residuePolynomial hc f + residuePolynomial hc g := by
  apply Polynomial.ext
  intro v
  rw [Polynomial.coeff_add, residuePolynomial_coeff, residuePolynomial_coeff,
      residuePolynomial_coeff]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (f + g).1) = _
  rw [show (f + g).1 = f.1 + g.1 from rfl, map_add, map_add]

lemma residuePolynomial_mul [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residuePolynomial hc (f * g) =
      residuePolynomial hc f * residuePolynomial hc g := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_coeff, Polynomial.coeff_mul]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (f * g).1) = _
  rw [show (f * g).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, residuePolynomial_coeff, residuePolynomial_coeff]

/-- The residue map as a ring homomorphism `Restricted R° c →+* R̃[X]`, valid for `1 ≤ c`.

This is the polynomial-descent ring homomorphism: for `c ≥ 1`, a restricted power series
in `R°⟨x⟩` has coefficients eventually in `R°°`, so its coefficient-wise reduction
modulo `R°°` lands in the *polynomial* ring `R̃[X]` rather than just `R̃[[X]]`. -/
noncomputable def residueRingHom [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c) :
    PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c →+*
      Polynomial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
          TopologicalRing.IsTopologicallyNilpotent_ideal R) where
  toFun := residuePolynomial hc
  map_zero' := residuePolynomial_zero hc
  map_one' := residuePolynomial_one hc
  map_add' := residuePolynomial_add hc
  map_mul' := residuePolynomial_mul hc

@[simp]
lemma residueRingHom_apply [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residueRingHom hc f = residuePolynomial hc f := rfl

/-- If the residue `[a]` of a power-bounded element `a ∈ R°` is nilpotent in `R̃`,
then `a` is topologically nilpotent (as an element of `R`).

Reason: nilpotent `[a]` means `a^k ∈ R°°` for some `k > 0`, i.e. `a^k` is topologically
nilpotent; then `TopologicalRing.IsTopologicallyNilpotent.of_pow` (radicality of the
topologically-nilpotent ideal) recovers topological nilpotence of `a`. -/
lemma _root_.TopologicalRing.isTopologicallyNilpotent_of_residue_isNilpotent
    {a : ↥(TopologicalRing.powerBoundedSubring.toSubring R)}
    (h : IsNilpotent
      (Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R) a)) :
    IsTopologicallyNilpotent (a : R) := by
  obtain ⟨k, hk⟩ := h
  -- Strengthen to a positive exponent: `(mk a)^k = 0` ⟹ `(mk a)^(k+1) = 0`.
  have hk1 :
      (Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R) a) ^ (k + 1) = 0 := by
    rw [pow_succ, hk, zero_mul]
  -- `(mk a)^(k+1) = 0` ⟺ `a^(k+1) ∈ R°°` ⟺ `IsTopologicallyNilpotent ((a^(k+1) : R°) : R)`.
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      TopologicalRing.mem_IsTopologicallyNilpotent_ideal_iff] at hk1
  -- Move the power outside the coercion.
  have h_coe_pow : (((a ^ (k + 1) :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)) = (a : R) ^ (k + 1) := by
    push_cast; rfl
  rw [h_coe_pow] at hk1
  exact TopologicalRing.IsTopologicallyNilpotent.of_pow (Nat.succ_pos k) hk1

/-! ### The truncated residue ring `R̃_ε := R° / R_ε` and `τ_ε` coefficient-wise reduction

Parallel to the `residueRingHom` machinery above but quotienting by the closed-ball ideal
`closedBall_ideal ε` instead of the topologically-nilpotent ideal `R°°`. The result is a
ring homomorphism `Restricted R° c →+* (R° / closedBall_ideal ε)[X]`, used in the PDF τ_ε
construction (`divSubgroup_dense`, Step 2).

We thread the `h_pb_norm` hypothesis (`IsPowerBounded → ‖·‖ ≤ 1`) through, decoupling
the construction from the proof of that fact. Use
`IsPowerBounded.norm_le_one_of_normedField` to discharge it when `R` is a normed field. -/

/-- For `1 ≤ c` and `ε > 0`, the coefficients of a restricted power series in
`Restricted R° c` are eventually in `closedBall_ideal ε`.

Proof: restrictedness gives `‖coeff v f‖ * c^v → 0` in `atTop`; since `c^v ≥ 1` (using
`1 ≤ c`), the factor strengthens to `‖coeff v f‖ → 0`, so eventually `‖coeff v f‖ ≤ ε`. -/
lemma coeff_eventually_inClosedBall [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    ∀ᶠ v in Filter.atTop,
      PowerSeries.coeff v f.1 ∈ TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm := by
  have hc0 : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  have h_restr :
      Tendsto (fun v : ℕ => ‖PowerSeries.coeff v f.1‖ * c ^ v) cofinite (𝓝 0) :=
    (PowerSeries.isRestricted_iff c f.1).mp f.2
  rw [Nat.cofinite_eq_atTop] at h_restr
  -- Eventually `‖coeff v f‖ * c^v ≤ ε`.
  have h_le_eps : ∀ᶠ v in atTop, ‖PowerSeries.coeff v f.1‖ * c ^ v ≤ ε := by
    have := h_restr.eventually (Metric.ball_mem_nhds (0 : ℝ) hε_pos)
    filter_upwards [this] with v hv
    rw [Real.dist_eq, sub_zero] at hv
    have hpos : 0 ≤ ‖PowerSeries.coeff v f.1‖ * c ^ v :=
      mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le _)
    rw [abs_of_nonneg hpos] at hv
    exact hv.le
  filter_upwards [h_le_eps] with v hv_le
  -- `1 ≤ c^v` so `‖coeff v f‖ ≤ ‖coeff v f‖ * c^v ≤ ε`.
  have hcv : (1 : ℝ) ≤ c ^ v := one_le_pow₀ hc
  -- Membership in `closedBall_ideal ε` is exactly `‖(_ : R)‖ ≤ ε`.
  show ‖((PowerSeries.coeff v f.1 :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)‖ ≤ ε
  calc ‖((PowerSeries.coeff v f.1 :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)‖
      = ‖PowerSeries.coeff v f.1‖ := rfl
    _ = ‖PowerSeries.coeff v f.1‖ * 1 := (mul_one _).symm
    _ ≤ ‖PowerSeries.coeff v f.1‖ * c ^ v :=
        mul_le_mul_of_nonneg_left hcv (norm_nonneg _)
    _ ≤ ε := hv_le

/-- For `1 ≤ c` and `ε > 0`, the support of the residue function
`v ↦ (Ideal.Quotient.mk (closedBall_ideal ε)) (coeff v f.1)` is finite. -/
lemma residueCoeff_ε_support_finite [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    (Function.support fun v : ℕ =>
        Ideal.Quotient.mk
          (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)
          (PowerSeries.coeff v f.1)).Finite := by
  obtain ⟨N, hN⟩ :=
    (coeff_eventually_inClosedBall hc hε_pos h_pb_norm f).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro v hv
  simp only [Function.mem_support, ne_eq] at hv
  by_contra hvN
  apply hv
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hN v (Nat.le_of_not_lt hvN)

/-- The residue of a restricted power series modulo `closedBall_ideal ε`, as a
`Finsupp ℕ R̃_ε`. -/
noncomputable def residueFinsupp_ε [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    ℕ →₀ ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) :=
  Finsupp.ofSupportFinite
    (fun v => Ideal.Quotient.mk
      (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)
      (PowerSeries.coeff v f.1))
    (residueCoeff_ε_support_finite hc hε_pos h_pb_norm f)

/-- The residue of a restricted power series modulo `closedBall_ideal ε`, as a
polynomial in `R̃_ε[X]`. -/
noncomputable def residuePolynomial_ε [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    Polynomial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
        TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) :=
  ⟨residueFinsupp_ε hc hε_pos h_pb_norm f⟩

@[simp]
lemma residuePolynomial_ε_coeff [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) (v : ℕ) :
    (residuePolynomial_ε hc hε_pos h_pb_norm f).coeff v =
      Ideal.Quotient.mk (TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm)
        (PowerSeries.coeff v f.1) := by
  show (residueFinsupp_ε hc hε_pos h_pb_norm f) v = _
  simp [residueFinsupp_ε, Finsupp.ofSupportFinite]

@[simp]
lemma residuePolynomial_ε_zero [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1) :
    residuePolynomial_ε hc hε_pos h_pb_norm
        (0 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) = 0 := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_ε_coeff, Polynomial.coeff_zero]
  show Ideal.Quotient.mk _
      (PowerSeries.coeff v
        (0 : PowerSeries (TopologicalRing.powerBoundedSubring.toSubring R))) = 0
  rw [map_zero, map_zero]

@[simp]
lemma residuePolynomial_ε_one [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1) :
    residuePolynomial_ε hc hε_pos h_pb_norm
        (1 : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) = 1 := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_ε_coeff]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (1 : PowerSeries _)) = _
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [PowerSeries.coeff_zero_one, Polynomial.coeff_one_zero]; rfl
  · rw [PowerSeries.coeff_one, if_neg hv.ne']
    rw [map_zero, Polynomial.coeff_one, if_neg hv.ne']

lemma residuePolynomial_ε_add [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residuePolynomial_ε hc hε_pos h_pb_norm (f + g) =
      residuePolynomial_ε hc hε_pos h_pb_norm f +
      residuePolynomial_ε hc hε_pos h_pb_norm g := by
  apply Polynomial.ext
  intro v
  rw [Polynomial.coeff_add, residuePolynomial_ε_coeff, residuePolynomial_ε_coeff,
      residuePolynomial_ε_coeff]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (f + g).1) = _
  rw [show (f + g).1 = f.1 + g.1 from rfl, map_add, map_add]

lemma residuePolynomial_ε_mul [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f g : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residuePolynomial_ε hc hε_pos h_pb_norm (f * g) =
      residuePolynomial_ε hc hε_pos h_pb_norm f *
      residuePolynomial_ε hc hε_pos h_pb_norm g := by
  apply Polynomial.ext
  intro v
  rw [residuePolynomial_ε_coeff, Polynomial.coeff_mul]
  show Ideal.Quotient.mk _ (PowerSeries.coeff v (f * g).1) = _
  rw [show (f * g).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, residuePolynomial_ε_coeff, residuePolynomial_ε_coeff]

/-- **The `τ_ε` residue ring homomorphism.** For `1 ≤ c` and `ε > 0`, the coefficient-wise
reduction modulo `closedBall_ideal ε` is a ring homomorphism
`Restricted R° c →+* R̃_ε[X]`. Cf. `residueRingHom` (the `ε = 0` boundary, modulo `R°°`). -/
noncomputable def residueRingHom_ε [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1) :
    PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c →+*
      Polynomial ((TopologicalRing.powerBoundedSubring.toSubring R) ⧸
          TopologicalRing.closedBall_ideal ε hε_pos.le h_pb_norm) where
  toFun := residuePolynomial_ε hc hε_pos h_pb_norm
  map_zero' := residuePolynomial_ε_zero hc hε_pos h_pb_norm
  map_one' := residuePolynomial_ε_one hc hε_pos h_pb_norm
  map_add' := residuePolynomial_ε_add hc hε_pos h_pb_norm
  map_mul' := residuePolynomial_ε_mul hc hε_pos h_pb_norm

@[simp]
lemma residueRingHom_ε_apply [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_pb_norm : ∀ b : R, TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    residueRingHom_ε hc hε_pos h_pb_norm f = residuePolynomial_ε hc hε_pos h_pb_norm f := rfl

/-! ### Lift `Restricted R c → Restricted R° c` for norm-≤-1 elements

For `1 ≤ c`, a restricted power series `f : Restricted R c` with `‖f‖ ≤ 1` has all
coefficients in `R°` (since `‖coeff v f‖ ≤ ‖f‖ ≤ 1` under `c ≥ 1` + `NormOneClass`), so
it lifts canonically to `Restricted R° c`. The lift commutes with the coercion back to
`Restricted R c`. -/

variable [NormOneClass R] [StrongPos (fun _ : Unit ↦ c)]

/-- For `1 ≤ c` and `‖f‖ ≤ 1`, lift `f : Restricted R c` to `Restricted R° c` by viewing
each coefficient as an element of `R°` (using that `‖coeff v f‖ ≤ ‖f‖ ≤ 1` implies the
coefficient is power-bounded). -/
noncomputable def toPowerBounded (hc : 1 ≤ c)
    (f : PowerSeries.Restricted R c) (hf : ‖f‖ ≤ 1) :
    PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c := by
  -- Each coefficient of `f` is in `R°` (norm ≤ ‖f‖ ≤ 1).
  have h_coeff_in : ∀ n : ℕ, ‖PowerSeries.coeff n f.1‖ ≤ 1 := fun n => by
    have h_bd : ‖PowerSeries.coeff n f.1‖ * c ^ n ≤ ‖f‖ := by
      have := PowerSeries.le_gaussNorm norm c f.1 (Restricted.hasGaussNorm c f) n
      rwa [← Restricted.norm_eq] at this
    have hcv : (1 : ℝ) ≤ c ^ n := one_le_pow₀ hc
    calc ‖PowerSeries.coeff n f.1‖
        = ‖PowerSeries.coeff n f.1‖ * 1 := (mul_one _).symm
      _ ≤ ‖PowerSeries.coeff n f.1‖ * c ^ n :=
          mul_le_mul_of_nonneg_left hcv (norm_nonneg _)
      _ ≤ ‖f‖ := h_bd
      _ ≤ 1 := hf
  have h_coeff_pb : ∀ n : ℕ, TopologicalRing.IsPowerBounded (PowerSeries.coeff n f.1) :=
    fun n => IsPowerBounded.of_norm_le_one (h_coeff_in n)
  -- Build the lifted power series.
  refine ⟨PowerSeries.mk
    (fun n : ℕ => (⟨PowerSeries.coeff n f.1, h_coeff_pb n⟩ :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R))), ?_⟩
  -- Prove `IsRestricted`: `‖coeff n (lifted)‖ * c^n → 0` along cofinite.
  show PowerSeries.IsRestricted c _
  rw [PowerSeries.isRestricted_iff]
  have hf_restr : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n f.1‖ * c ^ n) cofinite (𝓝 0) :=
    (PowerSeries.isRestricted_iff c f.1).mp f.2
  refine hf_restr.congr fun n => ?_
  -- `coeff n (mk g) = g n`, and `‖(⟨a, _⟩ : R°)‖ = ‖a‖` by Subring norm (rfl).
  simp [PowerSeries.coeff_mk]

/-- The coercion of `toPowerBounded f h` back to `PowerSeries R` agrees with `f.1`
coefficient-wise. -/
@[simp]
lemma toPowerBounded_coeff (hc : 1 ≤ c) (f : PowerSeries.Restricted R c) (hf : ‖f‖ ≤ 1)
    (n : ℕ) :
    ((PowerSeries.coeff n (toPowerBounded hc f hf).1 :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R) =
      PowerSeries.coeff n f.1 := by
  simp [toPowerBounded, PowerSeries.coeff_mk]

/-! ### Ring-hom axioms for `toPowerBounded`

The lift `toPowerBounded` respects addition, multiplication, zero, and one (when norm
hypotheses are provided). These are the building blocks for packaging as a ring
homomorphism on the closed unit ball; for the τ_ε construction in `divSubgroup_dense`,
these axioms alone suffice to push the equation `f = g·q + toR r` through the lift. -/

lemma toPowerBounded_zero (hc : 1 ≤ c) :
    toPowerBounded hc (0 : PowerSeries.Restricted R c) (by rw [norm_zero]; exact zero_le_one)
      = 0 := by
  apply Subtype.ext
  ext n
  rw [toPowerBounded_coeff]
  show PowerSeries.coeff n (0 : PowerSeries R) = 0
  exact map_zero _

lemma toPowerBounded_one (hc : 1 ≤ c)
    (h1 : ‖(1 : PowerSeries.Restricted R c)‖ ≤ 1) :
    toPowerBounded hc (1 : PowerSeries.Restricted R c) h1 = 1 := by
  apply Subtype.ext
  ext n
  -- Both sides equal `coeff n (1 : PowerSeries R) = if n = 0 then 1 else 0` viewed in R°.
  simp [toPowerBounded, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `coeff 0 (1 : PowerSeries R) = 1 : R`; RHS coeff = 1 : R°, coerced = 1 : R.
    show PowerSeries.coeff 0 (1 : PowerSeries R) =
      ((PowerSeries.coeff 0
        (1 : PowerSeries ↥(TopologicalRing.powerBoundedSubring.toSubring R)) :
          ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
    rw [PowerSeries.coeff_zero_one, PowerSeries.coeff_zero_one]; rfl
  · show PowerSeries.coeff n (1 : PowerSeries R) =
      ((PowerSeries.coeff n
        (1 : PowerSeries ↥(TopologicalRing.powerBoundedSubring.toSubring R)) :
          ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
    rw [PowerSeries.coeff_one, if_neg hn.ne', PowerSeries.coeff_one, if_neg hn.ne']
    rfl

lemma toPowerBounded_add (hc : 1 ≤ c) (f g : PowerSeries.Restricted R c)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) (hfg : ‖f + g‖ ≤ 1) :
    toPowerBounded hc (f + g) hfg = toPowerBounded hc f hf + toPowerBounded hc g hg := by
  apply Subtype.ext
  ext n
  -- Compare coefficients at the R level (extension all the way down).
  show ((PowerSeries.coeff n (toPowerBounded hc (f + g) hfg).1 :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R) =
    ((PowerSeries.coeff n (toPowerBounded hc f hf + toPowerBounded hc g hg).1 :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
  rw [toPowerBounded_coeff]
  show PowerSeries.coeff n (f.1 + g.1) =
    ((PowerSeries.coeff n
      ((toPowerBounded hc f hf).1 + (toPowerBounded hc g hg).1) :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
  rw [map_add, map_add]
  push_cast
  rw [toPowerBounded_coeff, toPowerBounded_coeff]

lemma toPowerBounded_mul (hc : 1 ≤ c) (f g : PowerSeries.Restricted R c)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) (hfg : ‖f * g‖ ≤ 1) :
    toPowerBounded hc (f * g) hfg = toPowerBounded hc f hf * toPowerBounded hc g hg := by
  apply Subtype.ext
  ext n
  show ((PowerSeries.coeff n (toPowerBounded hc (f * g) hfg).1 :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R) =
    ((PowerSeries.coeff n (toPowerBounded hc f hf * toPowerBounded hc g hg).1 :
      ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
  rw [toPowerBounded_coeff]
  show PowerSeries.coeff n (f.1 * g.1) =
    ((PowerSeries.coeff n
      ((toPowerBounded hc f hf).1 * (toPowerBounded hc g hg).1) :
        ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [toPowerBounded_coeff, toPowerBounded_coeff]

/-! ### The closed-unit-ball subring and `toPowerBounded` as a ring hom

Under `[NormMulClass R]` (and ultrametric), the closed unit ball
`{f : Restricted R c | ‖f‖ ≤ 1}` is a subring of `Restricted R c`. The lift
`toPowerBounded` then packages as a ring hom from this subring to `Restricted R° c`.

The membership of `1` in the subring requires `‖(1 : Restricted R c)‖ ≤ 1`, which we
take as an explicit `h_one` hypothesis (rather than deriving it from a `NormOneClass`
instance on `Restricted R c` that doesn't currently exist). -/

/-- The closed unit ball in `Restricted R c` as a subring. -/
noncomputable def closedBallSubring (hc : 1 ≤ c)
    (h_one : ‖(1 : PowerSeries.Restricted R c)‖ ≤ 1) :
    Subring (PowerSeries.Restricted R c) where
  carrier := {f | ‖f‖ ≤ 1}
  zero_mem' := by show ‖(0 : PowerSeries.Restricted R c)‖ ≤ 1; rw [norm_zero]; exact zero_le_one
  one_mem' := h_one
  add_mem' := fun {f g} hf hg => by
    show ‖f + g‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max f g).trans (max_le hf hg)
  neg_mem' := fun {f} hf => by show ‖-f‖ ≤ 1; rwa [norm_neg]
  mul_mem' := fun {f g} hf hg => by
    show ‖f * g‖ ≤ 1
    calc ‖f * g‖ ≤ ‖f‖ * ‖g‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hf hg (norm_nonneg _) zero_le_one
      _ = 1 := mul_one _

/-- The lift `toPowerBounded` packaged as a ring homomorphism from the closed unit ball
subring to `Restricted R° c`. -/
noncomputable def toPowerBoundedRingHom (hc : 1 ≤ c)
    (h_one : ‖(1 : PowerSeries.Restricted R c)‖ ≤ 1) :
    ↥(closedBallSubring (R := R) hc h_one) →+*
      PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c where
  toFun f := toPowerBounded hc f.1 f.2
  map_zero' := toPowerBounded_zero hc
  map_one' := toPowerBounded_one hc h_one
  map_add' f g := toPowerBounded_add hc f.1 g.1 f.2 g.2
    ((closedBallSubring hc h_one).add_mem f.2 g.2)
  map_mul' f g := toPowerBounded_mul hc f.1 g.1 f.2 g.2
    ((closedBallSubring hc h_one).mul_mem f.2 g.2)

end Restricted

/-! ## Forward direction of the unit characterisation (`PowerBounded_isTopNil_coeff`)

Now that we have the residue ring hom `Restricted R° c →+* R̃[X]` and the lift from
nilpotence-in-`R̃` to topological nilpotence-in-`R°`, the forward direction of BGR Lemma
4.19 follows by combining `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` with the
two infrastructure pieces. -/

variable (R : Type*) [NormedCommRing R] [IsLinearTopology R R] [IsUltrametricDist R] (c : ℝ)
  [CompleteSpace R]

lemma Restricted.PowerBounded_isTopNil_coeff [StrongPos (fun _ : Unit ↦ c)] (hc : 1 ≤ c)
    [NormMulClass R] (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c)
    (hf : IsUnit f) : (IsUnit (PowerSeries.coeff 0 f.1) ∧
    ∀ v, 0 < v → IsTopologicallyNilpotent (PowerSeries.coeff v f.1)) := by
  -- Push `f` through the residue ring hom `Restricted R° c →+* R̃[X]`.
  have hf_residue : IsUnit (Restricted.residuePolynomial hc f) :=
    (Restricted.residueRingHom_apply hc f) ▸ hf.map (Restricted.residueRingHom hc)
  -- A polynomial is a unit iff its constant term is a unit AND its higher coefficients
  -- are nilpotent (`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`).
  rw [Polynomial.isUnit_iff_coeff_isUnit_isNilpotent] at hf_residue
  obtain ⟨h_coeff0_unit_residue, h_nilp_residue⟩ := hf_residue
  refine ⟨?_, ?_⟩
  · -- `IsUnit (coeff 0 f.1)` in `R°`: use the ring hom `coeff 0 : Restricted R° c →+* R°`
    -- and that ring homs preserve units. (This avoids relying on the residue at `R̃` and
    -- so doesn't need `bar_isUnit`.)
    let φ : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c →+*
          (TopologicalRing.powerBoundedSubring.toSubring R) :=
      RingHom.comp
        (PowerSeries.constantCoeff (R := (TopologicalRing.powerBoundedSubring.toSubring R)))
        (PowerSeries.isSubring c).subtype
    have hφ : φ f = PowerSeries.coeff 0 f.1 := by
      show PowerSeries.constantCoeff _ = PowerSeries.coeff 0 _
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hφ ▸ hf.map φ
  · -- For `v > 0`: the residue `[coeff v f.1]` is nilpotent in `R̃`. Lift to topological
    -- nilpotence in `R` via `isTopologicallyNilpotent_of_residue_isNilpotent`, then back to
    -- `R°` via the norm characterisation under `[NormMulClass]`.
    intro v hv
    have h_nilp : IsNilpotent
        (Ideal.Quotient.mk (TopologicalRing.IsTopologicallyNilpotent_ideal R)
          (PowerSeries.coeff v f.1)) := by
      have h := h_nilp_residue v hv.ne'
      rwa [Restricted.residuePolynomial_coeff] at h
    have h_top_nilp_R :
        IsTopologicallyNilpotent ((PowerSeries.coeff v f.1 :
          ↥(TopologicalRing.powerBoundedSubring.toSubring R)) : R) :=
      TopologicalRing.isTopologicallyNilpotent_of_residue_isNilpotent h_nilp
    -- Convert from top-nilp in `R` to top-nilp in `R°` via the norm characterisation.
    rw [IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass] at h_top_nilp_R
    exact IsTopologicallyNilpotent.iff_norm_lt_one_of_normMulClass.mpr h_top_nilp_R

lemma Restricted.PowerBounded_isUnit_iff
    [StrongPos (fun _ : Unit ↦ c)] [NormMulClass R] (hc1 : c = 1)
    (f : PowerSeries.Restricted (TopologicalRing.powerBoundedSubring.toSubring R) c) :
    IsUnit f ↔ (IsUnit (PowerSeries.coeff 0 f.1) ∧
    ∀ v, 0 < v → IsTopologicallyNilpotent (PowerSeries.coeff v f.1)) := by
  refine ⟨fun hf => Restricted.PowerBounded_isTopNil_coeff R c (hc1.symm.le.trans le_rfl) f hf, ?_⟩
  rintro ⟨h0, hpos⟩
  exact Restricted.PowerBounded_isUnit R c hc1.le f h0 hpos
