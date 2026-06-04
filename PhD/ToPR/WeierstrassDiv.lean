import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted
import PhD.ToPR.EpsilonDense
import PhD.ToPR.PowerBounded
import PhD.ToPR.RestrictedUnits
import PhD.ToPR.EuclideanDiv

variable {R : Type*} (v : R → ℝ)

def coeff_isUnit [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop := IsUnit (PowerSeries.coeff s f)

def norm_eq [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop :=
  PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f)

def norm_max_achiever [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop :=
  ∀ t, s < t → v (PowerSeries.coeff t f) < v (PowerSeries.coeff s f)

structure distinguished [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop where
  unit : coeff_isUnit f s
  norm_eq : norm_eq v c f s
  norm_max : norm_max_achiever v f s

-- the first step is to prove Weierstrass prep for c = 1
-- then we can update to c in the value group
-- then try and argue if the value group is dense we can construct sequences

variable [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}

instance : StrongPos (1 : Fin (n + 1) → ℝ) where
  pos := by aesop

instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

/-! ### Additivity helpers for `Polynomial.toRestricted` -/

namespace Polynomial

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

@[simp] lemma toRestricted_zero (c : ℝ) :
    toRestricted c (0 : Polynomial S) = 0 := by
  apply Subtype.ext
  show ((0 : Polynomial S) : PowerSeries S) = 0
  exact Polynomial.coe_zero

@[simp] lemma toRestricted_add (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p + q) = toRestricted c p + toRestricted c q := by
  apply Subtype.ext
  show ((p + q : Polynomial S) : PowerSeries S) =
    ((p : PowerSeries S) + (q : PowerSeries S))
  exact Polynomial.coe_add p q

@[simp] lemma toRestricted_neg (c : ℝ) (p : Polynomial S) :
    toRestricted c (-p) = -toRestricted c p := by
  apply Subtype.ext
  show ((-p : Polynomial S) : PowerSeries S) = -((p : PowerSeries S))
  ext n
  rw [map_neg, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_neg]

@[simp] lemma toRestricted_sub (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p - q) = toRestricted c p - toRestricted c q := by
  rw [sub_eq_add_neg, toRestricted_add, toRestricted_neg, sub_eq_add_neg]

end Polynomial

/-! ### `IsLinearTopology` propagation through `Restricted`

For an open ideal `J ⊆ R`, the set `{f ∈ Restricted | ∀ v, coeff_v f ∈ J}` is an open
ideal of the restricted ring. These form a basis of `𝓝 0`, so `IsLinearTopology` propagates
from the base ring to the restricted ring (in the `c ≡ 1` case where the Gauss norm equals
`sup ‖coeff_v‖`).

The argument fails for `c < 1` (where individual coefficients can have norm larger than
the Gauss norm), so we specialize to `c = (1 : σ → ℝ)`. -/

/-- The constant-`1` function on `σ` is strongly positive. -/
instance strongPos_one_pi {σ : Type*} : StrongPos (1 : σ → ℝ) := ⟨fun _ => one_pos⟩

/-- `MvPowerSeries.Restricted R c` inherits `CommRing` from the ambient `MvPowerSeries σ R`
when `R` is a `NormedCommRing`. -/
noncomputable instance MvPowerSeries.Restricted.commRing {R : Type*} [NormedCommRing R]
    [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ) :
    CommRing (MvPowerSeries.Restricted R c) :=
  Subring.toCommRing (R := MvPowerSeries σ R) (MvPowerSeries.isSubring c)

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [IsLinearTopology R R]
  {σ : Type*} [DecidableEq σ]

/-- Lift an ideal `J ⊆ R` to an ideal of `MvPowerSeries.Restricted R (1 : σ → ℝ)`,
consisting of restricted power series with all coefficients in `J`. -/
def liftIdeal (J : _root_.Ideal R) :
    _root_.Ideal (MvPowerSeries.Restricted R (1 : σ → ℝ)) where
  carrier := {f | ∀ v : σ →₀ ℕ, MvPowerSeries.coeff v f.1 ∈ J}
  add_mem' := fun {a b} ha hb v => by
    show MvPowerSeries.coeff v ((a + b).1) ∈ J
    rw [show ((a + b).1 : MvPowerSeries σ R) = a.1 + b.1 from rfl, map_add]
    exact J.add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    show MvPowerSeries.coeff v ((0 : MvPowerSeries.Restricted R (1 : σ → ℝ)).1) ∈ J
    rw [show ((0 : MvPowerSeries.Restricted R (1 : σ → ℝ)).1 : MvPowerSeries σ R) = 0 from rfl,
      map_zero]
    exact J.zero_mem
  smul_mem' := fun a {b} hb v => by
    show MvPowerSeries.coeff v ((a • b).1) ∈ J
    rw [show ((a • b).1 : MvPowerSeries σ R) = a.1 * b.1 from rfl, MvPowerSeries.coeff_mul]
    refine _root_.Ideal.sum_mem _ fun p _ => ?_
    exact J.mul_mem_left _ (hb p.2)

omit [IsLinearTopology R R] in
@[simp] lemma mem_liftIdeal_iff (J : _root_.Ideal R)
    (f : MvPowerSeries.Restricted R (1 : σ → ℝ)) :
    f ∈ liftIdeal (σ := σ) J ↔ ∀ v : σ →₀ ℕ, MvPowerSeries.coeff v f.1 ∈ J := Iff.rfl

/-- For an open ideal `J ⊆ R`, the lifted ideal is open. -/
lemma liftIdeal_isOpen (J : _root_.Ideal R) (hJ : IsOpen (J : Set R)) :
    IsOpen ((liftIdeal (σ := σ) J : Set (MvPowerSeries.Restricted R (1 : σ → ℝ)))) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨δ, δ_pos, hδ⟩ := Metric.isOpen_iff.mp hJ 0 J.zero_mem
  refine ⟨δ, δ_pos, fun g hg v => ?_⟩
  show MvPowerSeries.coeff v g.1 ∈ J
  have h_diff : MvPowerSeries.coeff v g.1 - MvPowerSeries.coeff v f.1 ∈ J := by
    apply hδ
    rw [Metric.mem_ball, dist_zero_right]
    have h_eq : MvPowerSeries.coeff v g.1 - MvPowerSeries.coeff v f.1 =
        MvPowerSeries.coeff v (g - f).1 := by
      show _ = MvPowerSeries.coeff v (g.1 - f.1)
      rw [map_sub]
    rw [h_eq]
    have h := MvPowerSeries.le_gaussNorm norm (1 : σ → ℝ) (g - f).1
      (MvRestricted.hasGaussNorm (1 : σ → ℝ) (g - f)) v
    have h_prod : v.prod (fun (i : σ) (e : ℕ) => ((1 : σ → ℝ) i) ^ e) = 1 := by
      show v.support.prod (fun a => ((1 : σ → ℝ) a) ^ (v a)) = 1
      exact Finset.prod_eq_one (fun _ _ => by simp)
    rw [h_prod, mul_one, ← MvRestricted.norm_eq] at h
    have hg' : ‖g - f‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hg
    exact h.trans_lt hg'
  have h_add : MvPowerSeries.coeff v g.1 =
      MvPowerSeries.coeff v f.1 + (MvPowerSeries.coeff v g.1 - MvPowerSeries.coeff v f.1) :=
    by ring
  rw [h_add]
  exact J.add_mem (hf v) h_diff

/-- `IsLinearTopology` for `MvPowerSeries.Restricted R (1 : σ → ℝ)` propagates from the
base ring `R`. -/
instance isLinearTopology :
    IsLinearTopology (MvPowerSeries.Restricted R (1 : σ → ℝ))
      (MvPowerSeries.Restricted R (1 : σ → ℝ)) := by
  refine IsLinearTopology.mk_of_hasBasis'
    (R := MvPowerSeries.Restricted R (1 : σ → ℝ))
    (p := fun J : _root_.Ideal R => IsOpen (J : Set R))
    (s := fun J : _root_.Ideal R => liftIdeal (σ := σ) J) ?_ ?_
  · -- The lifted ideals form a basis of `𝓝 0`.
    refine ⟨fun U => ⟨?_, ?_⟩⟩
    · -- (⇒) `U ∈ 𝓝 0` ⇒ ∃ open ideal `J` with `liftIdeal J ⊆ U`.
      intro hU
      obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.mp hU
      -- Pick an open ideal `J ⊆ R` with `J ⊆ Metric.ball 0 ε`.
      obtain ⟨J, hJ_open, hJ_sub⟩ :=
        (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp
          (Metric.ball_mem_nhds 0 ε_pos)
      refine ⟨J, hJ_open, fun f hf => hε ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      -- f ∈ liftIdeal J ⇒ all coeffs ∈ J ⊆ B(0,ε) ⇒ Gauss norm < ε. (For restricted f the
      -- sup is achieved at some `a`, and `‖coeff_a f.1‖ < ε` from `coeff_a f.1 ∈ J`.)
      obtain ⟨a, ha⟩ := MvRestricted.gaussNorm_achieved (1 : σ → ℝ)
        (fun _ => zero_le_one) f
      have h_prod : a.prod (fun (i : σ) (e : ℕ) => ((1 : σ → ℝ) i) ^ e) = 1 := by
        show a.support.prod (fun x => ((1 : σ → ℝ) x) ^ (a x)) = 1
        exact Finset.prod_eq_one (fun _ _ => by simp)
      have h_norm : ‖MvPowerSeries.coeff a f.1‖ = ‖f‖ := by
        rw [MvRestricted.norm_eq]
        have := ha
        rw [show MvPowerSeries.AchievesGaussNorm norm (1 : σ → ℝ) f.1 a ↔
            ‖MvPowerSeries.coeff a f.1‖ *
              (a.prod (fun (i : σ) (e : ℕ) => ((1 : σ → ℝ) i) ^ e)) =
            MvPowerSeries.gaussNorm norm (1 : σ → ℝ) f.1 from Iff.rfl] at this
        rw [h_prod, mul_one] at this
        exact this
      have h_coeff_lt : ‖MvPowerSeries.coeff a f.1‖ < ε := by
        have := hJ_sub (hf a)
        rwa [Metric.mem_ball, dist_zero_right] at this
      rw [← h_norm]
      exact h_coeff_lt
    · -- (⇐) An open ideal `J` with `liftIdeal J ⊆ U` gives `U ∈ 𝓝 0`.
      rintro ⟨J, hJ_open, hJ_sub⟩
      exact Filter.mem_of_superset
        ((liftIdeal_isOpen J hJ_open).mem_nhds (liftIdeal J).zero_mem) hJ_sub
  · -- Smul closure: automatic for ideals.
    intros I r m hm
    exact I.smul_mem r hm

end MvPowerSeries.Restricted

/-- `IsLinearTopology` for `PowerSeries.Restricted R 1` is a special case (with `σ = Unit`)
of the multivariate result. -/
instance PowerSeries.Restricted.isLinearTopology
    {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [IsLinearTopology R R] :
    IsLinearTopology (PowerSeries.Restricted R 1) (PowerSeries.Restricted R 1) :=
  show IsLinearTopology (MvPowerSeries.Restricted R (1 : Unit → ℝ))
    (MvPowerSeries.Restricted R (1 : Unit → ℝ))
  from MvPowerSeries.Restricted.isLinearTopology

variable {c} in
abbrev distinguished_restricted (f : PowerSeries.Restricted (MvPowerSeries.Restricted R
  (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) (s : ℕ) : Prop := distinguished norm 1 f.1 s

def distinguished_MvRestricted (f : (MvPowerSeries.Restricted R (1 : Fin (n + 1) → ℝ))) (s : ℕ) :
  Prop := distinguished_restricted (MvRestricted.finSuccEquiv _ _ _ f) s

/-! ### Scaffold for `weierstrassDivision_existance` (PDF Lemma 4.11)

The PDF proof of Weierstrass division for `c = 1` constructs the additive subgroup
`B = { g*q + r : q ∈ T, r ∈ S[X] with deg r < s }` and shows `B = T` by combining:
* closedness of `B` in `T`,
* `ε`-density of `B` in `T` via the `τ_ε` reduction and Euclidean division in the residue
  ring `(R̃_ε[x₁,…,x_{n-1}])[x_n]`.

The scaffold below extracts these as named sub-lemmas. Each non-trivial step is left as a
`sorry` for incremental discharging.

Throughout, write `S := MvPowerSeries.Restricted R (Fin.tail 1)` and `T := PowerSeries.Restricted S 1`.

NOTE: The existing definition `norm_max_achiever` (line 17) compares `v (coeff s f)` with
itself rather than `v (coeff t f) < v (coeff s f)`, which makes `distinguished_restricted`
vacuously false. The scaffold assumes the intended definition; with the current typo, the
sublemmas that use `hg` are trivially true by `exfalso`. -/

section WeierstrassDivisionScaffold

/-- The candidate set `B = { g * q + ↑r : q ∈ T, r ∈ S[X] with deg r < s }` from the PDF
proof of Lemma 4.11. -/
def divCarrier
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) :
    Set (PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) :=
  {f | ∃ q, ∃ r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))),
    Polynomial.degree r < s ∧ f = g * q + Polynomial.toRestricted 1 r}

/-- `divCarrier g s` packaged as an additive subgroup of `T`.

Closure proofs:
* `zero_mem`: take `q = 0`, `r = 0`; needs `Polynomial.degree 0 = ⊥ < (s : WithBot ℕ)`.
* `add_mem`: combine via `Polynomial.degree_add_le` and additivity of `Polynomial.toRestricted`.
* `neg_mem`: negate via `Polynomial.degree_neg` and negation of `Polynomial.toRestricted`. -/
def divSubgroup
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) :
    AddSubgroup (PowerSeries.Restricted (MvPowerSeries.Restricted R
      (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) where
  carrier := divCarrier g s
  zero_mem' := by
    refine ⟨0, 0, ?_, ?_⟩
    · simp [Polynomial.degree_zero]
    · simp
  add_mem' := by
    rintro _ _ ⟨qa, ra, hra, rfl⟩ ⟨qb, rb, hrb, rfl⟩
    refine ⟨qa + qb, ra + rb, ?_, ?_⟩
    · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hra hrb)
    · rw [Polynomial.toRestricted_add, mul_add]; abel
  neg_mem' := by
    rintro _ ⟨q, r, hr, rfl⟩
    refine ⟨-q, -r, ?_, ?_⟩
    · rwa [Polynomial.degree_neg]
    · rw [Polynomial.toRestricted_neg, mul_neg]; abel

lemma divSubgroup_coe
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) : ((divSubgroup g s : AddSubgroup _) : Set _) = divCarrier g s := rfl

/-! ### Residue-field machinery for the bounds (PDF Lemma 4.9)

The proof uses the standard residue-field machinery already defined in `PowerBounded.lean`:

* `TopologicalRing.powerBoundedSubring.toSubring T : Subring T` — the subring of
  power-bounded elements of `T`. In our ultrametric `[NormMulClass]` setting this coincides
  with `{f : T | ‖f‖ ≤ 1}` (PDF "T°").

* `TopologicalRing.IsTopologicallyNilpotent_ideal T : Ideal _` — the ideal of topologically
  nilpotent elements (PDF "T°°", equal to `{f : T | ‖f‖ < 1}`).

* `TopologicalRing.IsPowerBounded.residueField T` — the quotient (PDF "T̃").

To reference these in our setting, we need `[CommRing T]` and `[IsLinearTopology T T]`.
The first follows from `[NormedCommRing R]` once we provide `CommRing` instances for
`MvPowerSeries.Restricted` (added immediately below). The second — `IsLinearTopology T T`
— is not automatic from ultrametric: non-archimedean balls aren't generally ideals.
It is given by `IsLinearTopology R R` for the base `R` propagating through, and we take
it as an explicit hypothesis on `R` for the bounds. -/

/-- `MvPowerSeries.Restricted R c` inherits `NormMulClass` from `R`, via the existing
`MvRestricted.isAbsoluteValue` lemma which packages the Gauss-norm multiplicativity. -/
noncomputable instance MvPowerSeries.Restricted.normMulClass {R₀ : Type*} [NormedRing R₀]
    [IsUltrametricDist R₀] [NormMulClass R₀] {σ : Type*} [LinearOrder σ] (c : σ → ℝ)
    [StrongPos c] :
    NormMulClass (MvPowerSeries.Restricted R₀ c) where
  norm_mul a b :=
    (MvRestricted.isAbsoluteValue (R := R₀) c NormMulClass.norm_mul).abv_mul' a b

/-- `PowerSeries.Restricted R c` inherits `NormMulClass`, via the `σ = Unit` case of the
multivariate instance. -/
noncomputable instance PowerSeries.Restricted.normMulClass {R₀ : Type*} [NormedRing R₀]
    [IsUltrametricDist R₀] [NormMulClass R₀] (c : ℝ) [StrongPos (fun _ : Unit ↦ c)] :
    NormMulClass (PowerSeries.Restricted R₀ c) :=
  show NormMulClass (MvPowerSeries.Restricted R₀ (fun _ : Unit ↦ c)) from inferInstance

/-- `MvPowerSeries.Restricted R c` is nontrivial when `R` is: `0 ≠ 1` in the ambient
`MvPowerSeries σ R` (since the constant inclusion `R ↪ MvPowerSeries σ R` is injective). -/
instance MvPowerSeries.Restricted.nontrivial {R₀ : Type*} [NormedRing R₀] [IsUltrametricDist R₀]
    [Nontrivial R₀] {σ : Type*} (c : σ → ℝ) :
    Nontrivial (MvPowerSeries.Restricted R₀ c) := by
  haveI : Nontrivial (MvPowerSeries σ R₀) := inferInstance
  refine ⟨0, 1, fun h => zero_ne_one (α := MvPowerSeries σ R₀) ?_⟩
  exact congr_arg Subtype.val h

/-! ### Sub-lemmas for the residue contradiction -/

/-- For distinguished `g`, the inverse of `coeff_s g.1` exists in `S` (a unit). -/
noncomputable def distinguished_restricted.coeff_inv
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    {s : ℕ} (hg : distinguished_restricted g s) :
    MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)) :=
  (hg.unit : IsUnit _).unit⁻¹.val

/-- The "normalized" version of `g`: multiply by the constant `(coeff_s g.1)⁻¹`, so the new
leading coefficient is `1` and the new Gauss norm is `1`. -/
noncomputable def distinguished_restricted.normalize
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    {s : ℕ} (hg : distinguished_restricted g s) :
    PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 :=
  let u_inv := hg.coeff_inv
  ⟨PowerSeries.C u_inv, PowerSeries.isRestricted_C 1 u_inv⟩ * g



/-- `g ≠ 0` when `g` is distinguished of degree `s`: the `s`-th coefficient is a unit
(in the nontrivial ring), hence nonzero. -/
lemma distinguished_restricted.ne_zero
    [Nontrivial R]
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    {s : ℕ} (hg : distinguished_restricted g s) : g ≠ 0 := by
  intro h_zero
  have hcoeff : PowerSeries.coeff s g.1 = 0 := by
    have h1 : g.1 = 0 := congr_arg Subtype.val h_zero
    rw [h1]
    exact LinearMap.map_zero _
  exact hg.unit.ne_zero hcoeff

/-- `StrongPos` instance for `Fin.tail (1 : Fin (n+1) → ℝ)`, i.e. the constant-1 function
on `Fin n`. Required to instantiate `NormMulClass`/`StrongPos`-based instances on
`MvPowerSeries.Restricted R (Fin.tail 1)`. -/
instance strongPos_finTail_one : StrongPos (Fin.tail (1 : Fin (n + 1) → ℝ)) :=
  ⟨fun _ => by simp [Fin.tail]⟩

/-- **PDF Lemma 4.9 residue contradiction (un-normalized).** If `f = q*g + toR r` with `g`
distinguished of degree `s`, `deg r < s`, and `‖f‖ < max(‖g*q‖, ‖toR r‖)` (i.e., the
non-archimedean inequality is *not tight*), then we have a contradiction.


-- Note Claude was complaining that the PDF method required a lot more API
-- instead it said it could be proved directly coefficient wise
-- this is below... but I should probably redo this so that it works nicely!

Proof outline (PDF):

* **Step 1 (normalization).** Let `u_inv = (coeff_s g.1)⁻¹ : S` (a unit by `hg.unit`,
  nonzero by `[Nontrivial R]`). Let `Cu_inv = C(u_inv) : T` (constant power series), and
  `g' = Cu_inv * g = hg.normalize` (provided by the auxiliary defs above). Then `‖g'‖ = 1`
  and `coeff_s g'.1 = 1`.
* **Step 2 (scaling).** Find `α : S` with `‖α‖ = M⁻¹` where `M = max(‖g*q‖, ‖toR r‖)`.
  (Requires the value group of `S` to contain `M`; holds automatically when `R` is a
  complete non-archimedean valued *field* with surjective valuation.)
* **Step 3 (lift to `T°`).** With `α`, the scaled equation has all elements in
  `T° = TopologicalRing.powerBoundedSubring.toSubring T`. Lift to `Restricted S° 1` via the
  natural equivalence (each coefficient lands in `S°`).
* **Step 4 (apply residue).** Apply `Restricted.residueRingHom` to map the scaled, lifted
  equation into `Polynomial S̃[x]`. Since `‖α·f‖ < 1`, `[α·f] = 0`.
* **Step 5 (polynomial degrees).** In `S̃[x]`: `0 = [g']·[α·q'] + [α·toR r]`. Since `[g']`
  is monic of degree `s` (from `coeff_s g'.1 = 1` and the strict inequality
  `‖coeff_v g'.1‖ < 1` for `v > s` from `distinguished`) and `deg [α·toR r] ≤ deg r < s`,
  the polynomial degrees force `[α·q'] = 0 = [α·toR r]`.
* **Step 6 (contradiction).** `[α·q'] = 0` ⇒ `‖α·q'‖ < 1` ⇒ `‖q'‖ < M`. Similarly
  `‖toR r‖ < M`. With `‖q'‖ = ‖g*q‖` (multiplicativity + normalization), we get
  `max(‖g'·q'‖, ‖toR r‖) < M = max(‖g*q‖, ‖toR r‖)`. Contradiction. -/
lemma residueContradiction_unnorm
    [NormMulClass R] [Nontrivial R] [CompleteSpace R] [IsLinearTopology R R]
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (f q : PowerSeries.Restricted (MvPowerSeries.Restricted R
      (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + Polynomial.toRestricted 1 r)
    (hf_lt : ‖f‖ < max ‖g * q‖ ‖Polynomial.toRestricted 1 r‖) :
    False := by
  -- **c = 1 implementation.** Since the Gauss norm equals the max coefficient norm,
  -- we work coefficient-wise (no `α` of arbitrary norm is needed). The strategy:
  --   * Find the largest peak `u` of `q` (where `‖coeff_u q.1‖ = ‖q‖`).
  --   * Show `‖coeff_{u+s} (g*q).1‖ = ‖g‖·‖q‖` by the convolution-dominance argument:
  --     the `(s, u)` term contributes `coeff_s g.1 · coeff_u q.1` with norm `‖g‖·‖q‖`;
  --     all other terms `(a, b)` with `a + b = u + s` are strictly smaller, since either
  --     `a > s` (forcing `‖coeff_a g.1‖ < ‖g‖` from `distinguished`) or `b > u` (forcing
  --     `‖coeff_b q.1‖ < ‖q‖` from `u` being the *largest* peak).
  --   * `coeff_{u+s} (toR r).1 = 0` since `u + s ≥ s > deg r`.
  --   * Therefore `‖coeff_{u+s} f.1‖ = ‖g*q‖`, bounded by `‖f‖` (Gauss-norm bound),
  --     so `‖g*q‖ ≤ ‖f‖`. Combined with `hf_lt` (`‖f‖ < max(...)`), this and the
  --     non-archimedean inequality on `toR r = f - g*q` give a contradiction.
  -- Handle `q = 0` first.
  by_cases hq_zero : q = 0
  · subst hq_zero
    rw [mul_zero, zero_add] at hf
    rw [hf, mul_zero, norm_zero, max_eq_right (norm_nonneg _)] at hf_lt
    exact lt_irrefl _ hf_lt
  -- `q ≠ 0`, so `‖q‖ > 0`.
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq_zero
  -- Find the largest peak `u` of `q`.
  -- Use restrictedness to get a bound on the peak set.
  have h_restr_q : Filter.Tendsto
      (fun a : ℕ => ‖PowerSeries.coeff a q.1‖) Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff 1 q.1).mp q.2
    rw [Nat.cofinite_eq_atTop] at h
    refine h.congr fun t => ?_
    simp
  -- Eventually `‖coeff a q.1‖ < ‖q‖`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ a ≥ N, ‖PowerSeries.coeff a q.1‖ < ‖q‖ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr_q ‖q‖ hq_pos
    refine ⟨N, fun a ha => ?_⟩
    have := hN a ha
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  -- Peak set `{a | ‖coeff a q.1‖ = ‖q‖}` is finite (subset of `Finset.Iio N`).
  have h_peak_finite : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ = ‖q‖}).Finite := by
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intros a ha
    by_contra h_ge
    have : N ≤ a := Nat.le_of_not_lt h_ge
    exact (lt_self_iff_false ‖q‖).mp (ha ▸ hN a this)
  -- Peak set is nonempty (use `gaussNorm_achieved'`).
  have h_peak_nonempty : ({a : ℕ | ‖PowerSeries.coeff a q.1‖ = ‖q‖}).Nonempty := by
    obtain ⟨a₀, ha₀⟩ := Restricted.gaussNorm_achieved' (R := MvPowerSeries.Restricted R
      (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 (by norm_num) q
    refine ⟨a₀, ?_⟩
    show ‖PowerSeries.coeff a₀ q.1‖ = ‖q‖
    rw [one_pow, mul_one] at ha₀
    -- ha₀ : ‖coeff a₀ q.1‖ = Restricted.gaussNorm _ 1 q
    -- We want : ‖coeff a₀ q.1‖ = ‖q‖
    rw [ha₀]
    rfl
  -- Take the largest peak.
  let M_set := h_peak_finite.toFinset
  have hM_ne : M_set.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact h_peak_nonempty
  let u := M_set.max' hM_ne
  have hu_peak : ‖PowerSeries.coeff u q.1‖ = ‖q‖ := by
    have hu_mem := M_set.max'_mem hM_ne
    simp [M_set] at hu_mem
    exact hu_mem
  have hu_max : ∀ a, u < a → ‖PowerSeries.coeff a q.1‖ < ‖q‖ := by
    intros a ha_gt
    by_contra h_not_lt
    rw [not_lt] at h_not_lt
    have h_bd : ‖PowerSeries.coeff a q.1‖ ≤ ‖q‖ := by
      have h_bd := PowerSeries.le_gaussNorm norm 1 q.1 (Restricted.hasGaussNorm 1 q) a
      rwa [one_pow, mul_one, ← Restricted.norm_eq] at h_bd
    have h_eq : ‖PowerSeries.coeff a q.1‖ = ‖q‖ := le_antisymm h_bd h_not_lt
    have h_a_in : a ∈ M_set := by simp [M_set]; exact h_eq
    have h_a_le_u : a ≤ u := M_set.le_max' a h_a_in
    omega
  -- Now compute `‖coeff_{u+s} (g*q).1‖ = ‖g‖·‖q‖` via convolution dominance.
  -- The convolution is `∑_{(a,b) ∈ antidiagonal (u+s)} coeff_a g.1 · coeff_b q.1`.
  -- The (s, u) term has norm `‖g‖·‖q‖`; all others are strictly smaller, so the
  -- ultrametric sum norm equals the dominant.
  have h_peak_gq : ‖PowerSeries.coeff (u + s) (g * q).1‖ = ‖g‖ * ‖q‖ := by
    show ‖PowerSeries.coeff (u + s) (g.1 * q.1)‖ = ‖g‖ * ‖q‖
    rw [PowerSeries.coeff_mul]
    -- ‖g‖ > 0 from distinguished + Nontrivial.
    have hg_pos : (0 : ℝ) < ‖g‖ :=
      norm_pos_iff.mpr (distinguished_restricted.ne_zero g hg)
    -- ‖coeff_s g.1‖ = ‖g‖ (the `s`-th coefficient achieves the Gauss norm).
    have h_coeff_s_g : ‖PowerSeries.coeff s g.1‖ = ‖g‖ := by
      have h := hg.norm_eq
      show _ = Restricted.gaussNorm _ (1 : ℝ) g
      rw [← h]
    -- (s, u) is in the antidiagonal of u + s.
    have h_su_mem : (s, u) ∈ Finset.antidiagonal (u + s) := by
      rw [Finset.mem_antidiagonal]; ring
    -- Split the sum into the peak term `(s, u)` and the rest.
    rw [← Finset.sum_erase_add _ _ h_su_mem]
    -- Each non-peak term has norm strictly less than `‖g‖ * ‖q‖`.
    have h_rest_lt : ∀ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
        ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ < ‖g‖ * ‖q‖ := by
      rintro ⟨a, b⟩ hp
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
      obtain ⟨hne, hmem⟩ := hp
      rw [norm_mul]
      rcases lt_trichotomy a s with hlt | heq | hgt
      · -- `a < s` ⟹ `b > u` ⟹ `‖coeff_b q.1‖ < ‖q‖`.
        have hbu : u < b := by omega
        have hb_lt : ‖PowerSeries.coeff b q.1‖ < ‖q‖ := hu_max b hbu
        have ha_le : ‖PowerSeries.coeff a g.1‖ ≤ ‖g‖ := by
          have := PowerSeries.le_gaussNorm norm 1 g.1 (Restricted.hasGaussNorm 1 g) a
          rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
        calc ‖PowerSeries.coeff a g.1‖ * ‖PowerSeries.coeff b q.1‖
            ≤ ‖g‖ * ‖PowerSeries.coeff b q.1‖ :=
              mul_le_mul_of_nonneg_right ha_le (norm_nonneg _)
          _ < ‖g‖ * ‖q‖ := by gcongr
      · -- `a = s` ⟹ `b = u`, contradicting `(a, b) ≠ (s, u)`.
        exfalso; apply hne; ext
        · exact heq
        · simp only; omega
      · -- `a > s` ⟹ `‖coeff_a g.1‖ < ‖g‖` from `distinguished`.
        have ha_lt : ‖PowerSeries.coeff a g.1‖ < ‖g‖ := by
          have := hg.norm_max a hgt
          rwa [h_coeff_s_g] at this
        have hb_le : ‖PowerSeries.coeff b q.1‖ ≤ ‖q‖ := by
          have := PowerSeries.le_gaussNorm norm 1 q.1 (Restricted.hasGaussNorm 1 q) b
          rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
        calc ‖PowerSeries.coeff a g.1‖ * ‖PowerSeries.coeff b q.1‖
            ≤ ‖PowerSeries.coeff a g.1‖ * ‖q‖ :=
              mul_le_mul_of_nonneg_left hb_le (norm_nonneg _)
          _ < ‖g‖ * ‖q‖ := by gcongr
    -- Norm of the (sum-of-rest), strictly less than `‖g‖ * ‖q‖`.
    have h_rest_norm_lt :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
          PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ < ‖g‖ * ‖q‖ := by
      by_cases h_ne_empty : ((Finset.antidiagonal (u + s)).erase (s, u)).Nonempty
      · -- Nonempty: ultrametric sum bound `‖∑‖ ≤ sup' ‖each‖`, and `sup'` of values
        -- each `<` the bound is itself `<` the bound.
        calc ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
                PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖
            ≤ ((Finset.antidiagonal (u + s)).erase (s, u)).sup' h_ne_empty
                (fun p => ‖PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖) :=
              h_ne_empty.norm_sum_le_sup'_norm _
          _ < ‖g‖ * ‖q‖ := (Finset.sup'_lt_iff h_ne_empty).mpr h_rest_lt
      · -- Empty: sum is `0`, with norm `0 < ‖g‖ * ‖q‖`.
        rw [Finset.not_nonempty_iff_eq_empty] at h_ne_empty
        rw [h_ne_empty, Finset.sum_empty, norm_zero]
        exact mul_pos hg_pos hq_pos
    -- Norm of the peak term equals `‖g‖ * ‖q‖`.
    have h_peak_norm :
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ = ‖g‖ * ‖q‖ := by
      rw [norm_mul, h_coeff_s_g, hu_peak]
    -- Ultrametric isosceles: `‖rest + peak‖ = ‖peak‖` (since `‖rest‖ < ‖peak‖`).
    have h_ne :
        ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
            PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1‖ ≠
        ‖PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ := by
      rw [h_peak_norm]; exact ne_of_lt h_rest_norm_lt
    show ‖∑ p ∈ (Finset.antidiagonal (u + s)).erase (s, u),
            PowerSeries.coeff p.1 g.1 * PowerSeries.coeff p.2 q.1 +
          PowerSeries.coeff s g.1 * PowerSeries.coeff u q.1‖ = ‖g‖ * ‖q‖
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, h_peak_norm]
    exact max_eq_right h_rest_norm_lt.le
  -- `coeff_{u+s} (toR r).1 = 0` (degree).
  have h_toR_zero : PowerSeries.coeff (u + s) (Polynomial.toRestricted 1 r).1 = 0 := by
    show PowerSeries.coeff (u + s) r.toPowerSeries = 0
    rw [Polynomial.coeff_coe]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have : (s : WithBot ℕ) ≤ ((u + s : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.le_add_left s u
    exact hr.trans_le this
  -- `coeff_{u+s} f.1 = coeff_{u+s} (g*q).1`, hence has norm `‖g‖·‖q‖`.
  have h_coeff_f : ‖PowerSeries.coeff (u + s) f.1‖ = ‖g‖ * ‖q‖ := by
    rw [hf]
    show ‖PowerSeries.coeff (u + s) ((g * q + Polynomial.toRestricted 1 r).1)‖ = _
    rw [show (g * q + Polynomial.toRestricted 1 r).1 =
        (g * q).1 + (Polynomial.toRestricted 1 r).1 from rfl, map_add, h_toR_zero, add_zero]
    exact h_peak_gq
  -- Bound by `‖f‖`.
  have h_f_bd : ‖PowerSeries.coeff (u + s) f.1‖ ≤ ‖f‖ := by
    have := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm 1 f) (u + s)
    rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
  -- `‖g*q‖ ≤ ‖f‖` via `[NormMulClass T]`.
  have h_gq_bd : ‖g * q‖ ≤ ‖f‖ := by
    rw [norm_mul]
    rw [h_coeff_f] at h_f_bd
    exact h_f_bd
  -- Combine with `hf_lt` for contradiction.
  rcases lt_max_iff.mp hf_lt with h1 | h2
  · -- `‖f‖ < ‖g*q‖` contradicts `‖g*q‖ ≤ ‖f‖`.
    exact (lt_irrefl _) (h1.trans_le h_gq_bd)
  · -- `‖f‖ < ‖toR r‖`. But `toR r = f - g*q`, so `‖toR r‖ ≤ max(‖f‖, ‖g*q‖) ≤ ‖f‖`.
    have h_toR_r_eq : Polynomial.toRestricted 1 r = f - g * q := by
      rw [hf]; abel
    have h_toR_bd : ‖Polynomial.toRestricted 1 r‖ ≤ ‖f‖ := by
      rw [h_toR_r_eq]
      have h_ult : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖ := by
        have := IsUltrametricDist.norm_add_le_max f (-(g * q))
        rwa [← sub_eq_add_neg, norm_neg] at this
      exact h_ult.trans (max_le le_rfl h_gq_bd)
    exact (lt_irrefl _) (h2.trans_le h_toR_bd)

/-- **PDF Lemma 4.9: bound on `q`.** From `f = g*q + toR r` (with `g` distinguished of
degree `s` and `deg r < s`), `‖q‖ ≤ ‖g‖⁻¹ · ‖f‖`.

Proof: by contradiction, if `‖q‖·‖g‖ > ‖f‖` then by `[NormMulClass]` `‖g*q‖ > ‖f‖`, so
`‖f‖ < max(‖g*q‖, ‖toR r‖)` and `residueContradiction_unnorm` gives `False`. -/
lemma weierstrassDivision_bounds_q
    [NormMulClass R] [Nontrivial R] [CompleteSpace R] [IsLinearTopology R R]
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted 1 r)) :
    Restricted.gaussNorm _ 1 q ≤ (Restricted.gaussNorm _ 1 g)⁻¹ *
    (Restricted.gaussNorm _ 1 f) := by
  rw [show Restricted.gaussNorm _ (1 : ℝ) q = ‖q‖ from (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) g = ‖g‖ from (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) f = ‖f‖ from (Restricted.norm_eq 1 _).symm]
  -- `‖g‖ > 0` from the distinguished hypothesis (via `Nontrivial`).
  have hg_pos : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr (distinguished_restricted.ne_zero g hg)
  by_contra h_bd
  rw [not_le] at h_bd  -- h_bd : ‖g‖⁻¹ * ‖f‖ < ‖q‖
  -- Multiply both sides by ‖g‖: ‖f‖ < ‖q‖ * ‖g‖.
  have h_norm : ‖f‖ < ‖q‖ * ‖g‖ := by
    have h1 : ‖g‖⁻¹ * ‖f‖ * ‖g‖ < ‖q‖ * ‖g‖ :=
      mul_lt_mul_of_pos_right h_bd hg_pos
    have h2 : ‖g‖⁻¹ * ‖f‖ * ‖g‖ = ‖f‖ := by field_simp
    linarith
  -- ‖g * q‖ = ‖q‖ * ‖g‖ by `[NormMulClass]` + commutativity.
  have h_gq : ‖g * q‖ = ‖q‖ * ‖g‖ := by rw [norm_mul, mul_comm]
  -- So ‖f‖ < max(‖g*q‖, ‖toR r‖). Apply `residueContradiction_unnorm`.
  exact residueContradiction_unnorm g s hg f q r hr hf
    (lt_max_iff.mpr (Or.inl (h_gq ▸ h_norm)))

/-- **PDF Lemma 4.9: bound on `r`.** `‖toR r‖ ≤ ‖f‖`.

Proof: by contradiction, if `‖toR r‖ > ‖f‖` then `‖f‖ < max(‖g*q‖, ‖toR r‖)` and
`residueContradiction_unnorm` gives `False`. -/
lemma weierstrassDivision_bounds_r
    [NormMulClass R] [Nontrivial R] [CompleteSpace R] [IsLinearTopology R R]
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted 1 r)) :
    Restricted.gaussNorm _ 1 (Polynomial.toRestricted 1 r) ≤
    Restricted.gaussNorm _ 1 f := by
  rw [show Restricted.gaussNorm _ (1 : ℝ) (Polynomial.toRestricted 1 r) =
        ‖Polynomial.toRestricted 1 r‖ from (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) f = ‖f‖ from (Restricted.norm_eq 1 _).symm]
  by_contra h_bd
  rw [not_le] at h_bd  -- h_bd : ‖f‖ < ‖toR r‖
  exact residueContradiction_unnorm g s hg f q r hr hf
    (lt_max_iff.mpr (Or.inr h_bd))

/-! ### Polynomial subspace closedness -/

/-- The "extract the v-th coefficient" map `T → S` is continuous (contractive). -/
lemma coeff_continuous (v : ℕ) :
    Continuous fun f : PowerSeries.Restricted (MvPowerSeries.Restricted R
        (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 => PowerSeries.coeff v f.1 := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩
  rw [dist_eq_norm]
  have heq : PowerSeries.coeff v g.1 - PowerSeries.coeff v f.1 =
      PowerSeries.coeff v (g - f).1 := by
    show _ = PowerSeries.coeff v (g.1 - f.1)
    exact (LinearMap.map_sub (PowerSeries.coeff v) g.1 f.1).symm
  rw [heq]
  have h := PowerSeries.le_gaussNorm norm 1 (g - f).1
    (Restricted.hasGaussNorm 1 (g - f)) v
  rw [one_pow, mul_one, ← Restricted.norm_eq] at h
  exact h.trans_lt (by rwa [← dist_eq_norm])

/-- The set of `f ∈ T` whose coefficients above degree `s` all vanish is closed.
This is precisely the image of `Polynomial.toRestricted 1` on polynomials of degree `< s`. -/
lemma polySubspace_isClosed (s : ℕ) :
    IsClosed
      {f : PowerSeries.Restricted (MvPowerSeries.Restricted R
          (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 |
        ∀ v, s ≤ v → PowerSeries.coeff v f.1 = 0} := by
  refine IsSeqClosed.isClosed fun f_seq f hf_mem hf_lim v hv => ?_
  -- coeff v (f_seq n).1 = 0 for all n, and continuity gives the limit is also 0.
  have h_lim : Filter.Tendsto (fun n => PowerSeries.coeff v (f_seq n).1)
      Filter.atTop (nhds (PowerSeries.coeff v f.1)) :=
    ((coeff_continuous v).tendsto _).comp hf_lim
  have h_zero : (fun n => PowerSeries.coeff v (f_seq n).1) = (fun _ => 0) :=
    funext fun n => hf_mem n v hv
  rw [h_zero] at h_lim
  exact tendsto_nhds_unique h_lim tendsto_const_nhds

/-! ### Closedness of B -/

/-- **Sub-lemma (closedness of B).** The set `divCarrier g s` is closed in `T`.

The proof proceeds by showing sequential closedness:
* Pick a sequence `bₙ ∈ B` converging to some `b ∈ T`, with witnesses `bₙ = g*qₙ + toR rₙ`.
* `‖g‖ > 0` is assumed as `hg_norm_pos` (it follows from `hg.unit` once one adds
  `[Nontrivial R]`; we pass it explicitly here to keep the lemma decoupled).
* Both `(qₙ)` and `(toR rₙ)` are Cauchy in `T`, by `weierstrassDivision_bounds_q` and
  `weierstrassDivision_bounds_r` applied to the difference `bₙ - bₘ = g·(qₙ-qₘ) + toR(rₙ-rₘ)`.
* `T` is complete, so they converge to `q` and `r_T`.
* The limit `r_T` lies in the polynomial subspace (closed by `polySubspace_isClosed`), so it
  is of the form `toR r` for some polynomial `r` with `deg r < s`.
* By uniqueness of limits, `b = g*q + toR r ∈ divCarrier g s`. -/
lemma divSubgroup_isClosed [CompleteSpace R] [NormMulClass R] [Nontrivial R]
    [IsLinearTopology R R]
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (hg_norm_pos : (0 : ℝ) < ‖g‖) :
    IsClosed (divCarrier g s) := by
  -- Make `CompleteSpace T` available explicitly (the instance chain via `Fin (n+1)` doesn't
  -- automatically unify with our `Fin.tail 1` shape).
  haveI : CompleteSpace (PowerSeries.Restricted
      (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) :=
    MvRestricted.isCompleteSpace' R n (1 : Fin (n + 1) → ℝ)
  -- It suffices to show sequential closedness (metric spaces are Fréchet–Urysohn).
  refine IsSeqClosed.isClosed ?_
  intro b_seq b hb_mem hb_lim
  -- Pick witnesses for each `b_seq n ∈ divCarrier g s`.
  choose q_seq r_seq hr_seq hb_eq using hb_mem
  -- `b_seq` converges, hence is Cauchy.
  have hb_cauchy : CauchySeq b_seq := hb_lim.cauchySeq
  -- Helper: the difference identity `b n - b m = g·(q n - q m) + toR (r n - r m)`.
  have h_diff_eq : ∀ n m, b_seq n - b_seq m =
      g * (q_seq n - q_seq m) + Polynomial.toRestricted 1 (r_seq n - r_seq m) := fun n m => by
    rw [hb_eq n, hb_eq m, Polynomial.toRestricted_sub, mul_sub]
    abel
  have h_diff_deg : ∀ n m, (r_seq n - r_seq m).degree < s := fun n m =>
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (hr_seq n) (hr_seq m))
  -- `(q_seq)` is Cauchy: ‖q n - q m‖ ≤ ‖g‖⁻¹ · ‖b n - b m‖.
  have hq_cauchy : CauchySeq q_seq := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.mp hb_cauchy (ε * ‖g‖) (mul_pos hε hg_norm_pos)
    refine ⟨N, fun n hn m hm => ?_⟩
    -- bounds_q on the difference.
    have h_bd := weierstrassDivision_bounds_q g s hg (b_seq n - b_seq m)
      (q_seq n - q_seq m) (r_seq n - r_seq m) (h_diff_deg n m) (h_diff_eq n m)
    rw [show Restricted.gaussNorm _ (1 : ℝ) (q_seq n - q_seq m) =
      ‖q_seq n - q_seq m‖ from (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) g = ‖g‖ from (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) (b_seq n - b_seq m) =
        ‖b_seq n - b_seq m‖ from (Restricted.norm_eq 1 _).symm] at h_bd
    have h_uij : ‖b_seq n - b_seq m‖ < ε * ‖g‖ := by
      have := hN n hn m hm; rwa [dist_eq_norm] at this
    rw [dist_eq_norm]
    calc ‖q_seq n - q_seq m‖
        ≤ ‖g‖⁻¹ * ‖b_seq n - b_seq m‖ := h_bd
      _ < ‖g‖⁻¹ * (ε * ‖g‖) := by gcongr
      _ = ε := by field_simp
  -- `(toR ∘ r_seq)` is Cauchy: ‖toR (r n) - toR (r m)‖ ≤ ‖b n - b m‖.
  have hr_cauchy : CauchySeq (fun n => Polynomial.toRestricted 1 (r_seq n)) := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb_cauchy ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have h_bd := weierstrassDivision_bounds_r g s hg (b_seq n - b_seq m)
      (q_seq n - q_seq m) (r_seq n - r_seq m) (h_diff_deg n m) (h_diff_eq n m)
    rw [show Restricted.gaussNorm _ (1 : ℝ)
        (Polynomial.toRestricted 1 (r_seq n - r_seq m)) =
      ‖Polynomial.toRestricted 1 (r_seq n - r_seq m)‖ from
        (Restricted.norm_eq 1 _).symm,
      show Restricted.gaussNorm _ (1 : ℝ) (b_seq n - b_seq m) =
        ‖b_seq n - b_seq m‖ from (Restricted.norm_eq 1 _).symm] at h_bd
    rw [Polynomial.toRestricted_sub] at h_bd
    have h_uij : ‖b_seq n - b_seq m‖ < ε := by
      have := hN n hn m hm; rwa [dist_eq_norm] at this
    rw [dist_eq_norm]
    exact h_bd.trans_lt h_uij
  -- Limits in the complete space `T`.
  obtain ⟨q, hq_lim⟩ := cauchySeq_tendsto_of_complete hq_cauchy
  obtain ⟨r_T, hr_T_lim⟩ := cauchySeq_tendsto_of_complete hr_cauchy
  -- `r_T` has coefficients zero above degree `s` — preserved under the limit since each
  -- `toR (r_seq n)` does (deg < s) and `polySubspace_isClosed` says the constraint is closed.
  have h_r_T_in : r_T ∈
      {f : PowerSeries.Restricted _ 1 | ∀ v, s ≤ v → PowerSeries.coeff v f.1 = 0} := by
    refine (polySubspace_isClosed s).mem_of_tendsto hr_T_lim
      (Filter.Eventually.of_forall fun n v hv => ?_)
    -- (toR (r_seq n)).1 = r_seq n, deg r_seq n < s, so coeff v = 0 for v ≥ s.
    show PowerSeries.coeff v (Polynomial.toRestricted 1 (r_seq n)).1 = 0
    simp only [Polynomial.toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt ((hr_seq n).trans_le (by exact_mod_cast hv))
  -- Extract a polynomial `r` of degree `< s` with `toR r = r_T`.
  let r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) :=
    ∑ v ∈ Finset.range s, Polynomial.monomial v (PowerSeries.coeff v r_T.1)
  have hr_coeff : ∀ v, r.coeff v = if v < s then PowerSeries.coeff v r_T.1 else 0 := fun v => by
    simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    split_ifs with hv
    · rw [Finset.sum_eq_single v]
      · simp
      · intros; simp_all
      · simp [Finset.mem_range, hv]
    · refine Finset.sum_eq_zero fun w hw => ?_
      simp only [Finset.mem_range] at hw
      have : w ≠ v := fun h => hv (h ▸ hw)
      simp [this]
  have hr_deg : r.degree < s := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun v hv => ?_
    rw [hr_coeff, if_neg (not_lt.mpr hv)]
  have hr_toR : Polynomial.toRestricted 1 r = r_T := by
    apply Subtype.ext
    ext v
    show PowerSeries.coeff v r.toPowerSeries = PowerSeries.coeff v r_T.1
    rw [Polynomial.coeff_coe, hr_coeff]
    split_ifs with hv
    · rfl
    · exact (h_r_T_in v (not_lt.mp hv)).symm
  refine ⟨q, r, hr_deg, ?_⟩
  rw [hr_toR]
  -- `b_seq n = g*q_seq n + toR(r_seq n) → g*q + r_T`, and `b_seq → b`, so by uniqueness `b = g*q + r_T`.
  refine tendsto_nhds_unique hb_lim ?_
  have h_alt : b_seq =
      fun n => g * q_seq n + Polynomial.toRestricted 1 (r_seq n) := funext hb_eq
  rw [h_alt]
  exact (hq_lim.const_mul g).add hr_T_lim

/-- **Sub-lemma (ε from distinguished hypothesis, normalized case).** If `g` is distinguished
of degree `s` and `‖coeff s g.1‖ = 1` (the PDF's `|g| = 1` normalization step), then there
exists `ε ∈ (0, 1)` bounding `‖coeff t g.1‖` for all `t > s`.

PDF: ε = max over s < t of |g_t|. The maximum exists and is < 1 because the gauss norm is
attained at `s` and strictly bigger than `|g_t|` for `t > s`. The proof combines
* the strict-inequality from `distinguished` (`norm_max`),
* restrictedness (`‖coeff t g.1‖ → 0` as `t → ∞`) to make the relevant set finite.

For an un-normalized `g`, the caller in `divSubgroup_dense` first scales by `(coeff s g.1)⁻¹`. -/
lemma exists_epsilon_of_distinguished
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (hg1 : ‖PowerSeries.coeff s g.1‖ = 1) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ ≤ ε := by
  -- Restrictedness ⇒ `‖coeff t g.1‖ → 0` along `atTop` on `ℕ`.
  have h_restr :
      Filter.Tendsto (fun t : ℕ => ‖PowerSeries.coeff t g.1‖) Filter.atTop (nhds 0) := by
    have h := (PowerSeries.isRestricted_iff 1 g.1).mp g.2
    rw [Nat.cofinite_eq_atTop] at h
    refine h.congr fun t => ?_
    simp
  -- So eventually `‖coeff t g.1‖ < 1/2`: pick such an `N`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ t ≥ N, ‖PowerSeries.coeff t g.1‖ < 1/2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_restr (1/2) (by norm_num)
    refine ⟨N, fun t ht => ?_⟩
    have := hN t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  -- From `norm_max` + `hg1`, each `‖coeff t g.1‖ < 1` for `t > s`.
  have h_lt_one : ∀ t, s < t → ‖PowerSeries.coeff t g.1‖ < 1 := fun t ht => by
    have := hg.norm_max t ht
    rwa [hg1] at this
  -- Finite finset `F = {‖coeff t g.1‖ : s < t < N}`, each < 1.
  let F : Finset ℝ := (Finset.Ioo s N).image (fun t => ‖PowerSeries.coeff t g.1‖)
  -- Take `M = max F` (default 0 if empty); then `M < 1`.
  by_cases hF : F.Nonempty
  · let M := F.max' hF
    have hM_lt : M < 1 := by
      obtain ⟨t, ht_mem, ht_eq⟩ := Finset.mem_image.mp (F.max'_mem hF)
      rw [Finset.mem_Ioo] at ht_mem
      simpa [M, ← ht_eq] using h_lt_one t ht_mem.1
    have hM_nn : 0 ≤ M := by
      obtain ⟨t, _, ht_eq⟩ := Finset.mem_image.mp (F.max'_mem hF)
      simp [M, ← ht_eq, norm_nonneg]
    refine ⟨max M (1/2), ⟨lt_max_iff.mpr (Or.inr (by norm_num)), max_lt hM_lt (by norm_num)⟩, ?_⟩
    intro t ht
    rcases lt_or_ge t N with htN | htN
    · -- `t < N` and `s < t`, so `‖coeff t g.1‖ ∈ F`, hence `≤ M`.
      have h_mem : ‖PowerSeries.coeff t g.1‖ ∈ F :=
        Finset.mem_image.mpr ⟨t, Finset.mem_Ioo.mpr ⟨ht, htN⟩, rfl⟩
      exact (F.le_max' _ h_mem).trans (le_max_left _ _)
    · -- `t ≥ N`: by `hN`, `‖coeff t g.1‖ < 1/2 ≤ ε`.
      exact (hN t htN).le.trans (le_max_right _ _)
  · -- `F` empty: every `t > s` satisfies `t ≥ N`. Use `ε = 1/2`.
    refine ⟨1/2, ⟨by norm_num, by norm_num⟩, fun t ht => ?_⟩
    have htN : N ≤ t := by
      by_contra h
      exact hF ⟨_, Finset.mem_image.mpr
        ⟨t, Finset.mem_Ioo.mpr ⟨ht, Nat.lt_of_not_ge h⟩, rfl⟩⟩
    exact (hN t htN).le

end WeierstrassDivisionScaffold

-- we now need NormedField assumption

section Final

variable {R : Type*} [NormedField R] [IsUltrametricDist R]

/-- `IsLinearTopology` for `MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n+1) → ℝ))`,
derived from the `(1 : σ → ℝ)` instance via `Fin.tail 1 = 1` (definitionally for ℝ-valued
constants, so `convert` succeeds). -/
instance instIsLinearTopology_FinTail_one [IsLinearTopology R R] [CompleteSpace R] (n : ℕ) :
    IsLinearTopology (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n+1) → ℝ)))
        (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n+1) → ℝ))) := by
  convert MvPowerSeries.Restricted.isLinearTopology (σ := Fin n)
  assumption

set_option maxHeartbeats 1600000 in
/-- **PDF Lemma 4.11 density of `divSubgroup g s`.** Under `[NormedField R]`, the subgroup
`divSubgroup g s` is dense in `T = Restricted S 1` (with `S = Restricted R (Fin.tail 1)`).

The proof outline (Steps 1-5 of PDF Lemma 4.11) is:
* **Step 1 (normalize g).** `u_inv := (coeff_s g.1)⁻¹ : S`; `g' := C(u_inv) * g : T` has
  `‖g'‖ = 1`, `coeff_s g'.1 = 1`, and `‖coeff_v g'.1‖ < 1` for `v > s`.
* **Step 2 (ε).** Apply `exists_epsilon_of_distinguished` to `g'` (which is again
  distinguished, with `hg1 = 1`) to extract `ε ∈ (0, 1)` such that all higher coefficients
  of `g'` are `≤ ε`.
* **Step 3 (τ_ε(g'°) monic).** Lift `g'` to `g'° : T°` via `toPowerBounded`. Apply
  `residueRingHom_ε` (with `R := S` as the base): `τ_ε(g'°)` is monic of degree `s`
  (`[coeff_s g'°.1] = [1] = 1`, `[coeff_v g'°.1] = 0` for `v > s`).
* **Step 4 (division mod ε).** For each `f : T` (after rescaling), apply
  `exists_div_by_τε_monic` (from `EuclideanDiv.lean`) to get `qC, rC` with
  `‖f° - g'° · qC - toR rC‖_{T°} ≤ ε`.
* **Step 5 (rescaling).** For general `f : T`, scale by `α := (R-coeff achieving ‖f‖)⁻¹`
  (NormedField R), apply Step 4 on `Cα * f` (now in `T°`), include back to `T` via
  `includeOfPowerBounded`, unscale by `α⁻¹` to get `‖f - b‖ ≤ ε · ‖f‖`. -/
lemma divSubgroup_dense [IsLinearTopology R R] [CompleteSpace R] {n : ℕ}
    -- `h_pb_norm_S` is the `IsPowerBounded ⟹ ‖·‖ ≤ 1` direction for `S`. Not automatic
    -- (S is not a NormedField), so taken as a hypothesis.
    (h_pb_norm_S : ∀ b : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)),
      TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s) :
    Dense (divCarrier g s) := by
  -- Reduce to ε-density of `divSubgroup g s`.
  rw [← divSubgroup_coe g s]
  suffices h_eps_dense :
      ∃ ε ∈ Set.Ioo (0 : ℝ) 1,
        SeminormedAddGroup.epsilonDense _ (divSubgroup g s) ε by
    obtain ⟨ε, hε, hd⟩ := h_eps_dense
    exact SeminormedAddGroup.dense_epsilonDense _ _ ε hε hd
  -- ===================================================================================
  -- Step 1 (normalize g). `u : Sˣ` with `u.val = coeff_s g.1`; `u_inv := u⁻¹.val : S`;
  -- `g' := C(u_inv) * g : T` with `‖g'‖ = 1` and `coeff_s g'.1 = 1`.
  -- ===================================================================================
  obtain ⟨u, hu_eq⟩ := hg.unit
  set u_inv : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)) :=
    (u⁻¹).val with hu_inv_def
  -- ‖g‖ = ‖coeff_s g.1‖ from `hg.norm_eq`.
  have hg_norm_eq : ‖g‖ = ‖PowerSeries.coeff s g.1‖ := by
    have := hg.norm_eq
    show Restricted.gaussNorm _ (1 : ℝ) g = _
    rw [← this]
  have hg_ne : g ≠ 0 := distinguished_restricted.ne_zero g hg
  have hg_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
  -- ‖u.val‖ = ‖g‖.
  have hu_norm : ‖u.val‖ = ‖g‖ := by rw [hu_eq]; exact hg_norm_eq.symm
  have hu_inv_uv : u_inv * u.val = 1 := by simp [hu_inv_def]
  have hu_uv_inv : u.val * u_inv = 1 := by simp [hu_inv_def]
  -- `‖(1 : S)‖ = 1` (inline: in NormMulClass + Nontrivial + faithful, `‖1‖² = ‖1‖`,
  -- and `‖1‖ ≠ 0`, so `‖1‖ = 1`).
  have h_one_S : ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ = 1 := by
    have h_sq :
        ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ *
          ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ =
        ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ := by
      rw [← norm_mul, one_mul]
    have h_ne :
        ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ ≠ 0 := by
      rw [Ne, norm_eq_zero]; exact one_ne_zero
    have : ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ *
          ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ =
        ‖(1 : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)))‖ * 1 := by
      rw [h_sq, mul_one]
    exact mul_left_cancel₀ h_ne this
  -- `‖u_inv‖ = ‖g‖⁻¹` (NormMulClass on S).
  have hu_inv_norm : ‖u_inv‖ = ‖g‖⁻¹ := by
    have hmul : ‖u.val‖ * ‖u_inv‖ = 1 := by
      rw [← norm_mul, hu_uv_inv, h_one_S]
    rw [hu_norm] at hmul
    field_simp
    linarith [hg_pos, hmul]
  -- ===================================================================================
  -- Step 1 (continued): construct g' = Cu_inv * g with ‖g'‖ = 1, coeff_s g'.1 = 1.
  -- ===================================================================================
  set Cu_inv : PowerSeries.Restricted
      (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 :=
    ⟨PowerSeries.C u_inv, PowerSeries.isRestricted_C 1 u_inv⟩ with hCu_inv_def
  set g' : PowerSeries.Restricted
      (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 := Cu_inv * g
    with hg'_def
  -- `coeff_s g'.1 = u_inv * coeff_s g.1 = u_inv * u.val = 1`.
  have hg'_coeff_s : PowerSeries.coeff s g'.1 = 1 := by
    show PowerSeries.coeff s (Cu_inv.1 * g.1) = 1
    rw [PowerSeries.coeff_C_mul, ← hu_eq, hu_inv_uv]
  -- For `v > s`, `‖coeff_v g'.1‖ < 1` (distinguished + normalization).
  have hg'_coeff_strict : ∀ v, s < v → ‖PowerSeries.coeff v g'.1‖ < 1 := by
    intro v hv
    show ‖PowerSeries.coeff v (Cu_inv.1 * g.1)‖ < 1
    rw [PowerSeries.coeff_C_mul, norm_mul, hu_inv_norm]
    have h_strict := hg.norm_max v hv
    rw [← hg_norm_eq] at h_strict
    have h_lhs : ‖g‖⁻¹ * ‖PowerSeries.coeff v g.1‖ < ‖g‖⁻¹ * ‖g‖ :=
      mul_lt_mul_of_pos_left h_strict (by positivity)
    have h_rhs : ‖g‖⁻¹ * ‖g‖ = 1 := by field_simp
    linarith
  -- ===================================================================================
  -- ‖g'‖ = 1, by showing each coefficient has norm ≤ 1 and using `le_gaussNorm` at s.
  -- ===================================================================================
  have hg'_norm_le : ‖g'‖ ≤ 1 := by
    obtain ⟨a, ha⟩ := Restricted.gaussNorm_achieved' (R := MvPowerSeries.Restricted R
        (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 zero_le_one g'
    rw [one_pow, mul_one] at ha
    show Restricted.gaussNorm _ 1 g' ≤ 1
    rw [← ha]
    rcases lt_trichotomy a s with hlt | heq | hgt
    · -- a < s
      show ‖PowerSeries.coeff a (Cu_inv.1 * g.1)‖ ≤ 1
      rw [PowerSeries.coeff_C_mul, norm_mul, hu_inv_norm]
      have h_coeff_le_g : ‖PowerSeries.coeff a g.1‖ ≤ ‖g‖ := by
        have := PowerSeries.le_gaussNorm norm 1 g.1 (Restricted.hasGaussNorm 1 g) a
        rwa [one_pow, mul_one, ← Restricted.norm_eq] at this
      have h1 : ‖g‖⁻¹ * ‖PowerSeries.coeff a g.1‖ ≤ ‖g‖⁻¹ * ‖g‖ :=
        mul_le_mul_of_nonneg_left h_coeff_le_g (by positivity)
      have h2 : ‖g‖⁻¹ * ‖g‖ = 1 := by field_simp
      linarith
    · -- a = s
      subst heq
      rw [hg'_coeff_s, h_one_S]
    · -- a > s
      exact (hg'_coeff_strict a hgt).le
  have hg'_norm_ge : 1 ≤ ‖g'‖ := by
    have h := PowerSeries.le_gaussNorm norm 1 g'.1 (Restricted.hasGaussNorm 1 g') s
    rw [one_pow, mul_one, hg'_coeff_s, h_one_S, ← Restricted.norm_eq] at h
    exact h
  have hg'_norm : ‖g'‖ = 1 := le_antisymm hg'_norm_le hg'_norm_ge
  -- ===================================================================================
  -- Build `hg' : distinguished_restricted g' s`.
  -- ===================================================================================
  have hg' : distinguished_restricted g' s := {
    unit := by
      show IsUnit (PowerSeries.coeff s g'.1)
      rw [hg'_coeff_s]; exact isUnit_one
    norm_eq := by
      show Restricted.gaussNorm _ (1 : ℝ) g' = _
      change ‖g'‖ = _
      rw [hg'_norm, hg'_coeff_s, h_one_S]
    norm_max := by
      intro v hv
      have h_lt := hg'_coeff_strict v hv
      rw [hg'_coeff_s, h_one_S]
      exact h_lt
  }
  have hg'1 : ‖PowerSeries.coeff s g'.1‖ = 1 := by rw [hg'_coeff_s, h_one_S]
  -- ===================================================================================
  -- Step 2 (apply `exists_epsilon_of_distinguished` to get ε).
  -- ===================================================================================
  obtain ⟨ε, hε, hε_bd⟩ := exists_epsilon_of_distinguished g' s hg' hg'1
  refine ⟨ε, hε, ?_⟩
  -- ===================================================================================
  -- Per-f rescaling. For each f ∈ T, build b ∈ divSubgroup g s with ‖-f + b‖ ≤ ε * ‖f‖.
  -- ===================================================================================
  intro f
  -- The construction proceeds via:
  --   * (i) f = 0 case: take b = 0.
  --   * (ii) f ≠ 0: α-construction, lift to T° via `toPowerBounded`, apply
  --     `exists_div_by_τε_monic`, include back via `includeOfPowerBounded`, unscale.
  -- The full implementation is ~200 lines using the `EuclideanDiv.lean` API:
  --   `exists_div_by_τε_monic` for the T°-level division,
  --   `toPowerBounded` / `includeOfPowerBounded` for the T°↔T transit,
  --   `gaussNorm_achieved'` + `MvRestricted.gaussNorm_achieved` for α-construction,
  --   `Polynomial.toRestricted` for embedding the remainder polynomial.
  by_cases hf_zero : f = 0
  · -- f = 0: take b = 0. `‖-0 + 0‖ = 0 ≤ ε * 0 = 0`.
    subst hf_zero
    refine ⟨⟨0, AddSubgroup.zero_mem _⟩, ?_⟩
    show ‖-(0 : PowerSeries.Restricted _ 1) + (0 : PowerSeries.Restricted _ 1)‖
      ≤ ε * ‖(0 : PowerSeries.Restricted _ 1)‖
    simp
  · -- f ≠ 0: per-f rescaling using α := (R-coeff achieving ‖f‖)⁻¹ via `NormedField R`.
    -- =================================================================================
    -- (a) α-construction: drill into coefficients of `f` to find `α₀ : R` with `‖α₀‖ = ‖f‖`.
    -- =================================================================================
    have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf_zero
    -- Step (a.1): `f : T` has a coefficient (in S) with norm `= ‖f‖`.
    obtain ⟨v, hv⟩ := Restricted.gaussNorm_achieved' (R := MvPowerSeries.Restricted R
        (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 zero_le_one f
    rw [one_pow, mul_one] at hv
    -- hv : ‖PowerSeries.coeff v f.1‖ = Restricted.gaussNorm S 1 f = ‖f‖.
    have hv_norm : ‖PowerSeries.coeff v f.1‖ = ‖f‖ := by rw [hv]; rfl
    -- Step (a.2): drill into the S-coefficient to find R-coefficient with same norm.
    obtain ⟨w, hw⟩ := MvRestricted.gaussNorm_achieved
        (Fin.tail (1 : Fin (n + 1) → ℝ)) (fun _ => zero_le_one)
        (PowerSeries.coeff v f.1)
    -- α₀ := coeff w (coeff v f.1).1 : R.
    set α₀ : R := MvPowerSeries.coeff w (PowerSeries.coeff v f.1).1 with hα₀_def
    have hα₀_norm : ‖α₀‖ = ‖f‖ := by
      -- From hw (AchievesGaussNorm), `‖coeff w (...).1‖ * w.prod (c^_) = gaussNorm = ‖coeff v f.1‖ = ‖f‖`.
      have h := hw
      rw [show MvPowerSeries.AchievesGaussNorm norm (Fin.tail (1 : Fin (n + 1) → ℝ))
          (PowerSeries.coeff v f.1).1 w ↔
        ‖MvPowerSeries.coeff w (PowerSeries.coeff v f.1).1‖ *
          w.prod (fun i e => Fin.tail (1 : Fin (n + 1) → ℝ) i ^ e) =
        MvPowerSeries.gaussNorm norm (Fin.tail (1 : Fin (n + 1) → ℝ))
          (PowerSeries.coeff v f.1).1 from Iff.rfl] at h
      have hprod : w.prod (fun i e => Fin.tail (1 : Fin (n + 1) → ℝ) i ^ e) = 1 := by
        show w.support.prod (fun a => Fin.tail (1 : Fin (n + 1) → ℝ) a ^ (w a)) = 1
        exact Finset.prod_eq_one (fun i _ => by simp [Fin.tail])
      rw [hprod, mul_one] at h
      rw [hα₀_def, h]
      show MvRestricted.gaussNorm _ _ (PowerSeries.coeff v f.1) = ‖f‖
      change ‖PowerSeries.coeff v f.1‖ = ‖f‖
      exact hv_norm
    have hα₀_ne : α₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hα₀_norm
      linarith
    -- Step (a.3): α := α₀⁻¹ : R, with ‖α‖ = ‖f‖⁻¹.
    set α : R := α₀⁻¹ with hα_def
    have hα_norm : ‖α‖ = ‖f‖⁻¹ := by rw [hα_def, norm_inv, hα₀_norm]
    -- =================================================================================
    -- (b) Scaling: build `Cα : T` from α; show `‖Cα‖ ≤ ‖α‖`, so `‖Cα * f‖ ≤ 1`.
    -- =================================================================================
    set Cα_S : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)) :=
      ⟨MvPowerSeries.C α, MvPowerSeries.isRestricted_C _ α⟩ with hCα_S_def
    set Cα : PowerSeries.Restricted (MvPowerSeries.Restricted R
        (Fin.tail (1 : Fin (n + 1) → ℝ))) 1 :=
      ⟨PowerSeries.C Cα_S, PowerSeries.isRestricted_C 1 Cα_S⟩ with hCα_def
    -- `‖Cα_S‖_S ≤ ‖α‖`: only the constant coefficient is nonzero, with value α.
    have hCα_S_norm_le : ‖Cα_S‖ ≤ ‖α‖ := by
      obtain ⟨a, ha⟩ := MvRestricted.gaussNorm_achieved
          (Fin.tail (1 : Fin (n + 1) → ℝ)) (fun _ => zero_le_one) Cα_S
      have h := ha
      rw [show MvPowerSeries.AchievesGaussNorm norm (Fin.tail (1 : Fin (n + 1) → ℝ))
          Cα_S.1 a ↔
        ‖MvPowerSeries.coeff a Cα_S.1‖ *
          a.prod (fun i e => Fin.tail (1 : Fin (n + 1) → ℝ) i ^ e) =
        MvPowerSeries.gaussNorm norm (Fin.tail (1 : Fin (n + 1) → ℝ)) Cα_S.1 from
          Iff.rfl] at h
      have hprod : a.prod (fun i e => Fin.tail (1 : Fin (n + 1) → ℝ) i ^ e) = 1 := by
        show a.support.prod (fun x => Fin.tail (1 : Fin (n + 1) → ℝ) x ^ (a x)) = 1
        exact Finset.prod_eq_one (fun i _ => by simp [Fin.tail])
      rw [hprod, mul_one] at h
      change MvPowerSeries.gaussNorm norm (Fin.tail (1 : Fin (n + 1) → ℝ)) Cα_S.1 ≤ ‖α‖
      rw [← h]
      -- coeff a (C α) = if a = 0 then α else 0.
      show ‖MvPowerSeries.coeff a (MvPowerSeries.C α : MvPowerSeries _ R)‖ ≤ ‖α‖
      by_cases ha0 : a = 0
      · subst ha0; rw [MvPowerSeries.coeff_zero_C]
      · rw [MvPowerSeries.coeff_C, if_neg ha0, norm_zero]; exact norm_nonneg _
    -- `‖Cα‖ ≤ ‖Cα_S‖ ≤ ‖α‖`: same reasoning at the PowerSeries level.
    have hCα_norm_le : ‖Cα‖ ≤ ‖α‖ := by
      obtain ⟨a, ha⟩ := Restricted.gaussNorm_achieved'
          (R := MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1
          zero_le_one Cα
      rw [one_pow, mul_one] at ha
      show Restricted.gaussNorm _ 1 Cα ≤ ‖α‖
      rw [← ha]
      -- `coeff a Cα.1 = coeff a (PowerSeries.C Cα_S) = if a = 0 then Cα_S else 0`.
      show ‖PowerSeries.coeff a (PowerSeries.C Cα_S)‖ ≤ ‖α‖
      by_cases ha0 : a = 0
      · subst ha0; rw [PowerSeries.coeff_zero_C]; exact hCα_S_norm_le
      · rw [PowerSeries.coeff_C, if_neg ha0, norm_zero]; exact norm_nonneg _
    -- `‖Cα * f‖ ≤ 1`.
    have hCαf_le : ‖Cα * f‖ ≤ 1 := by
      calc ‖Cα * f‖ ≤ ‖Cα‖ * ‖f‖ := norm_mul_le _ _
        _ ≤ ‖α‖ * ‖f‖ := mul_le_mul_of_nonneg_right hCα_norm_le (norm_nonneg _)
        _ = ‖f‖⁻¹ * ‖f‖ := by rw [hα_norm]
        _ = 1 := by field_simp
    -- =============================================================================
    -- (c)-(h) ASSEMBLY (currently a focused sorry).  The drafted code that builds
    -- `xLift`, `gLift`, verifies `τ_ε(gLift).Monic`, applies `exists_div_by_τε_monic`,
    -- includes back, and unscales by `Cα₀` is preserved in git history; it requires
    -- additional infrastructure not yet in place:
    --   * `CompleteSpace (MvPowerSeries.Restricted R (Fin.tail 1))` — the existing
    --     `MvRestricted.isCompleteSpace` instance is stated for `c : Fin (n+1) → ℝ`,
    --     not for `c = Fin.tail 1 : Fin n → ℝ`; the case split + foo_isom /
    --     finSuccIsometry pattern from `MvRestricted.isCompleteSpace`'s body is needed.
    --   * Cleaner unification heuristics (the `Restricted.toPowerBounded` elaboration
    --     timed out at 1.6M heartbeats during typeclass synthesis).
    -- The high-level (a) α-construction + (b) scaling above are fully proven.
    sorry

lemma weierstrassDivision_existance [CompleteSpace R] [IsLinearTopology R R]
    (h_pb_norm_S : ∀ b : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)),
      TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) :
    ∃ q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1,
    ∃ r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))),
    ∃ h : Polynomial.degree r < s,
    f = g * q + (Polynomial.toRestricted 1 r) := by
  -- Closedness and density of B together force B = T, so f ∈ B; extract the witnesses.
  -- `‖g‖ > 0` follows from `hg.unit` plus the new `Nontrivial R` hypothesis.
  have hg_norm_pos : (0 : ℝ) < ‖g‖ :=
    norm_pos_iff.mpr (distinguished_restricted.ne_zero g hg)
  have h_closed := divSubgroup_isClosed g s hg hg_norm_pos
  have h_dense := divSubgroup_dense h_pb_norm_S g s hg
  have hB_univ : divCarrier g s = Set.univ := by
    rw [← h_closed.closure_eq, h_dense.closure_eq]
  have hf_mem : f ∈ divCarrier g s := hB_univ ▸ Set.mem_univ f
  obtain ⟨q, r, hr, hf_eq⟩ := hf_mem
  exact ⟨q, r, hr, hf_eq⟩

/-- **PDF Lemma 4.10.** Two valid Weierstrass-division representations agree: from
`f = g*q + toR r` and `f = g*q' + toR r'`, the difference equation
`0 = g*(q' - q) + toR (r' - r)` (with `deg (r' - r) < s`) gives `‖q' - q‖ ≤ ‖g‖⁻¹·‖0‖ = 0`
via `weierstrassDivision_bounds_q`, hence `q' = q`; then `toR r' = toR r` and `Polynomial.coe`
injectivity finishes `r' = r`. -/
lemma weierstrassDivision_unique [CompleteSpace R] [IsLinearTopology R R]
    (h_pb_norm_S : ∀ b : MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ)),
      TopologicalRing.IsPowerBounded b → ‖b‖ ≤ 1)
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) :
    ∃! q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1,
    ∃! r : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))),
    ∃ h : Polynomial.degree r < s,
    f = g * q + (Polynomial.toRestricted 1 r) := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_existance h_pb_norm_S g s hg f
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · -- Inner uniqueness: with `q = q₀` fixed, the polynomial `r` is unique.
    rintro r' ⟨hr', hf'⟩
    -- Subtract: `toR r' = toR r₀` via additive cancellation.
    have h_toR_eq : Polynomial.toRestricted 1 r' = Polynomial.toRestricted 1 r₀ :=
      add_left_cancel (hf'.symm.trans hf₀)
    -- `toRestricted` is injective: equal Subtype values, then `Polynomial.coe_inj`.
    have h_pow_eq : r'.toPowerSeries = r₀.toPowerSeries :=
      congr_arg Subtype.val h_toR_eq
    exact Polynomial.coe_inj.mp h_pow_eq
  · -- Outer uniqueness: `q` is unique. Use `bounds_q` on the difference equation.
    rintro q' ⟨r', ⟨hr', hf'⟩, _⟩
    -- The difference equation `0 = g*(q' - q₀) + toR (r' - r₀)`.
    have h_diff_eq :
        (0 : PowerSeries.Restricted (MvPowerSeries.Restricted R
              (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) =
        g * (q' - q₀) + Polynomial.toRestricted 1 (r' - r₀) := by
      rw [mul_sub, Polynomial.toRestricted_sub]
      have h := hf'.symm.trans hf₀
      have h_abel : g * q' - g * q₀ +
            (Polynomial.toRestricted 1 r' - Polynomial.toRestricted 1 r₀) =
          (g * q' + Polynomial.toRestricted 1 r') -
            (g * q₀ + Polynomial.toRestricted 1 r₀) := by abel
      rw [h_abel, h, sub_self]
    have h_deg : (r' - r₀).degree < s :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr' hr₀)
    -- Apply `bounds_q` with the difference equation. The RHS has factor `‖0‖ = 0`.
    have h_bd := weierstrassDivision_bounds_q g s hg 0 (q' - q₀) (r' - r₀) h_deg h_diff_eq
    have h_norm_zero : Restricted.gaussNorm _ (1 : ℝ)
        (0 : PowerSeries.Restricted (MvPowerSeries.Restricted R
          (Fin.tail (1 : Fin (n + 1) → ℝ))) 1) = 0 := by
      show ‖(0 : PowerSeries.Restricted (MvPowerSeries.Restricted R
        (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)‖ = 0
      exact norm_zero
    rw [h_norm_zero, mul_zero,
        show Restricted.gaussNorm _ (1 : ℝ) (q' - q₀) = ‖q' - q₀‖ from
          (Restricted.norm_eq 1 _).symm] at h_bd
    -- `‖q' - q₀‖ ≤ 0`, combined with `‖_‖ ≥ 0`, gives `‖q' - q₀‖ = 0`, hence `q' - q₀ = 0`.
    have h_zero : ‖q' - q₀‖ = 0 := le_antisymm h_bd (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)

lemma weierstrassPreparation_exists
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) : ∃ ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))),
    ∃ hω : ω.Monic, ∃ e : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail
    (1 : Fin (n + 1) → ℝ))) 1, ∃ he : IsUnit e, g = e * (Polynomial.toRestricted 1 ω) := by

  sorry

lemma weierstrassPreparation_unique
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1)
    (s : ℕ) : ∃! ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))),
    ∃ hω : ω.Monic,
    ∃! e : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail (1 : Fin (n + 1) → ℝ))) 1,
    ∃ he : IsUnit e, g = e * (Polynomial.toRestricted 1 ω) := by

  sorry

end Final
