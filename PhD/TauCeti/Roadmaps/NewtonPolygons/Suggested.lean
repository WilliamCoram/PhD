import Mathlib

/-!
# Newton polygons: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures that
can already be stated against the pinned Mathlib API. It is not an exhaustive list of the results in
any layer, and where the roadmap and this file disagree the roadmap wins.

The point of the file is to pin the design decisions that are easy to get wrong and expensive to
undo: a Newton polygon is its height function `ℕ → WithTop ℝ` (README convention 1); the input is an
additive valuation `v : AddValuation K (WithTop Γ)` with `Γ = ℤ, ℚ, ℝ`, pushed into `ℝ` along a
strictly monotone `e : Γ →+ ℝ`, and tied to the norm by a base `b` with `‖x‖ = b ^ (-(e (v x)))`
(convention 2), so that over `ℚ_p` with `v p = 1` the slopes of a polynomial are rational numbers;
the `ℚ`-valued valuation is normalised at an element, through a Prop class (convention 3); and roots
are measured by the valuation the spectral norm induces, not by a hypothesised one (convention 8).
-/

namespace TauCetiRoadmap.NewtonPolygons

open scoped Classical NNReal

/-! ## Layer 0: convex minorants and the polygon of a sequence -/

/-- Convexity of a sequence of extended reals, in the midpoint form, which needs no subtraction and
has the right behaviour at `⊤`: the condition is vacuous where `h k` or `h (k + 2)` is `⊤`, and
fails where `h (k + 1)` is `⊤` but its neighbours are not. So a convex sequence automatically has an
interval as its finiteness set (README convention 5). -/
def IsConvexSeq (h : ℕ → WithTop ℝ) : Prop :=
  ∀ k, h (k + 1) + h (k + 1) ≤ h k + h (k + 2)

/-- The `j`-th unit slope of a height function, `h (j + 1) - h j`, with the convention that it is
`⊤` as soon as either end is `⊤`. For a convex sequence this is monotone, which is the content of
convexity. -/
noncomputable def unitSlope (h : ℕ → WithTop ℝ) (j : ℕ) : WithTop ℝ :=
  if h j = ⊤ ∨ h (j + 1) = ⊤ then ⊤
  else (((h (j + 1)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ)

theorem unitSlope_mono {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) : Monotone (unitSlope h) :=
  sorry

/-- The chord inequality: a convex sequence lies on or below the chord through two of its points.
Stated as a comparison with the affine interpolation, scaled to avoid division. -/
theorem le_chord {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) {i k n : ℕ} (hik : i ≤ n) (hnk : n ≤ k) :
    (k - i : ℕ) • h n ≤ (k - n : ℕ) • h i + (n - i : ℕ) • h k :=
  sorry

/-- The pointwise supremum of a family of convex sequences is convex (§0.1.3): the fact that makes
the greatest convex minorant exist. -/
theorem isConvexSeq_iSup {ι : Type*} [Nonempty ι] {h : ι → ℕ → WithTop ℝ}
    (hh : ∀ i, IsConvexSeq (h i)) : IsConvexSeq fun k ↦ ⨆ i, h i k :=
  sorry

/-- The bridge to Mathlib's convexity, in the direction that is actually usable: a convex sequence
that is finite everywhere is the restriction to `ℕ` of a `ConvexOn` function on `[0, ∞)`. -/
theorem exists_convexOn_of_isConvexSeq {h : ℕ → ℝ} (hh : IsConvexSeq fun k ↦ (h k : WithTop ℝ)) :
    ∃ H : ℝ → ℝ, ConvexOn ℝ (Set.Ici (0 : ℝ)) H ∧ ∀ k : ℕ, H k = h k :=
  sorry

/-- `v` is admissible when some line through its first finite point lies on or below every later
point: exactly the condition for a convex minorant to exist. The failing example is `v k = -k ^ 2`. -/
def IsAdmissible (v : ℕ → WithTop ℝ) : Prop :=
  ∀ i, v i ≠ ⊤ → ∃ s : ℝ, ∀ k, i ≤ k → v i + (k - i : ℕ) • (s : WithTop ℝ) ≤ v k

/-- `IsNewtonPolygonOf v h`: `h` is *the* Newton polygon of the points `(k, v k)` — the greatest
convex minorant anchored at the first point. The four conditions are kept separate because later
layers use them separately; `le_points` and `greatest` are the two halves of the existence proof. -/
structure IsNewtonPolygonOf (v h : ℕ → WithTop ℝ) : Prop where
  /-- The polygon is convex. -/
  convex : IsConvexSeq h
  /-- The polygon is `⊤` exactly to the left of the first point of `v`, and agrees with `v` there. -/
  anchor : ∀ i, (∀ k < i, v k = ⊤) → v i ≠ ⊤ → (h i = v i ∧ ∀ k < i, h k = ⊤)
  /-- The polygon lies on or below every point. -/
  le_points : ∀ k, h k ≤ v k
  /-- It is the greatest such: any convex minorant with the same anchor lies below it. -/
  greatest : ∀ g, IsConvexSeq g → (∀ k, g k ≤ v k) → (∀ i, h i = ⊤ → g i = ⊤) → ∀ k, g k ≤ h k

/-- **Uniqueness**, on the nose. This is the statement that convention 1 buys: with a
segment-decorated structure as the primary object it is false, and only height equality survives. -/
theorem IsNewtonPolygonOf.unique {v h₁ h₂ : ℕ → WithTop ℝ} (h₁' : IsNewtonPolygonOf v h₁)
    (h₂' : IsNewtonPolygonOf v h₂) : h₁ = h₂ :=
  sorry

/-- The Newton polygon of a sequence, as a total function. Junk outside the hypotheses of
`isNewtonPolygonOf_newtonPolygon`; every later statement goes through the characterisation. -/
noncomputable def newtonPolygon (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  sorry

/-- **Existence.** The construction is the vertex walk; admissibility is exactly what it needs. -/
theorem isNewtonPolygonOf_newtonPolygon {v : ℕ → WithTop ℝ} (hv : IsAdmissible v)
    (hv' : ∃ i, v i ≠ ⊤) : IsNewtonPolygonOf v (newtonPolygon v) :=
  sorry

/-- Admissibility is necessary as well as sufficient. -/
theorem IsNewtonPolygonOf.isAdmissible {v h : ℕ → WithTop ℝ} (hh : IsNewtonPolygonOf v h) :
    IsAdmissible v :=
  sorry

/-! ### Slopes, faces, and the slope multiset -/

/-- A polygon is pure of slope `m` when every unit slope is `m`. -/
def IsPure (h : ℕ → WithTop ℝ) (m : ℝ) : Prop :=
  ∀ j, unitSlope h j ≠ ⊤ → unitSlope h j = (m : WithTop ℝ)

/-- The number of unit slopes at most `σ`: the right endpoint of the face of slope `σ`, and the
number of roots of valuation `≥ -σ` once `h` is the polygon of a polynomial. -/
noncomputable def faceRight (h : ℕ → WithTop ℝ) (σ : ℝ) : ℕ :=
  sInf {n : ℕ | (σ : WithTop ℝ) < unitSlope h n}

/-- The number of unit slopes strictly less than `σ`. -/
noncomputable def faceLeft (h : ℕ → WithTop ℝ) (σ : ℝ) : ℕ :=
  sInf {n : ℕ | (σ : WithTop ℝ) ≤ unitSlope h n}

/-- The unit slopes are unbounded: the polygon is finite, or its slopes tend to `+∞`. This is the
hypothesis the product formula of Layer 5 cannot do without. -/
def SlopesUnbounded (h : ℕ → WithTop ℝ) : Prop :=
  ∀ σ : ℝ, ∃ n, (σ : WithTop ℝ) < unitSlope h n

/-- The slope multiset of a polygon with finitely many unit slopes. -/
noncomputable def slopeMultiset (h : ℕ → WithTop ℝ) (d : ℕ) : Multiset ℝ :=
  (Multiset.range d).map fun j ↦ (unitSlope h j).untop₀

/-- **The supporting-line lemma.** An affine function lying on or below every point lies on or below
the polygon. The workhorse of every later layer. -/
theorem line_le_of_le_points {v h : ℕ → WithTop ℝ} (hh : IsNewtonPolygonOf v h) (y σ : ℝ)
    (hle : ∀ k : ℕ, ((y + σ * (k : ℝ) : ℝ) : WithTop ℝ) ≤ v k) (k : ℕ) :
    ((y + σ * k : ℝ) : WithTop ℝ) ≤ h k :=
  sorry

/-- **The competitor lemma.** The two-slope form, which is the instance later layers consume. -/
theorem twoSlope_le_of_le_points {v h : ℕ → WithTop ℝ} (hh : IsNewtonPolygonOf v h) (y σ τ : ℝ)
    (hστ : σ ≤ τ) (n : ℕ)
    (hle : ∀ k : ℕ, ((y + σ * (min k n : ℕ) + τ * ((k - min k n : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v k)
    (k : ℕ) :
    ((y + σ * (min k n : ℕ) + τ * ((k - min k n : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ h k :=
  sorry

/-- The multiplicity of `σ` as a slope is the width of its face. -/
theorem faceRight_sub_faceLeft {v h : ℕ → WithTop ℝ} (hh : IsNewtonPolygonOf v h)
    (hu : SlopesUnbounded h) (d : ℕ) (σ : ℝ) :
    (slopeMultiset h d).count σ = faceRight h σ - faceLeft h σ :=
  sorry

/-! ### Minkowski sums -/

/-- The Minkowski sum (min-convolution) of two polygons, as a finite infimum: `WithTop ℝ` is not a
complete lattice, so `Finset.inf` rather than `⨅`. -/
noncomputable def minkowski (h₁ h₂ : ℕ → WithTop ℝ) (n : ℕ) : WithTop ℝ :=
  (Finset.range (n + 1)).inf fun i ↦ h₁ i + h₂ (n - i)

theorem isConvexSeq_minkowski {h₁ h₂ : ℕ → WithTop ℝ} (h₁' : IsConvexSeq h₁)
    (h₂' : IsConvexSeq h₂) : IsConvexSeq (minkowski h₁ h₂) :=
  sorry

theorem faceRight_minkowski {h₁ h₂ : ℕ → WithTop ℝ} (h₁' : SlopesUnbounded h₁)
    (h₂' : SlopesUnbounded h₂) (σ : ℝ) :
    faceRight (minkowski h₁ h₂) σ = faceRight h₁ σ + faceRight h₂ σ :=
  sorry

/-! ## Layer 1: additive valuations of a nonarchimedean field

`Valuation.addVal : Valuation R Mᵐ⁰ → AddValuation R (WithTop M)` and the `WithZero.negLog` it goes
through are §1.1, coordinated with mathlib4#43578 and mathlib4#43580; they are not in Mathlib at the
pin, so they are not prototyped against here. What follows are the `ℤ`- and `ℚ`-valued members of
the family and their normalisations, which sit on top of §1.1. -/

section AddVal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Rational rank one, normalised at an element** (§1.4.1). A Prop, deliberately: a dense rank-one
value group has no canonical generator, so the `ℚ`-valued additive valuation only becomes canonical
once a normalising element is chosen, and that element is `π`. For `ℂ_p` one takes `π = p`. There is
no data-carrying version of this class (README convention 3). -/
class IsCommensurable (v : Valuation R Γ₀) (π : R) : Prop where
  /-- `π` has nonzero valuation. -/
  val_pos : 0 < v π
  /-- `π` has valuation `< 1`, so that it plays the role of a uniformiser. -/
  val_lt_one : v π < 1
  /-- Every nonzero value of `v` is commensurable with `v π`. -/
  exists_zpow_eq (x : R) (hx : v x ≠ 0) : ∃ m n : ℤ, 0 < n ∧ v x ^ n = v π ^ m

/-- The `ℚ`-valued additive valuation of `v`, normalised by `addValQ v π π = 1` (§1.4.2). -/
noncomputable def addValQ (v : Valuation R Γ₀) (π : R) [IsCommensurable v π] :
    AddValuation R (WithTop ℚ) :=
  sorry

theorem addValQ_self (v : Valuation R Γ₀) (π : R) [IsCommensurable v π] : addValQ v π π = 1 :=
  sorry

/-- **The workhorse** (§1.4.3): a witness `v x ^ n = v π ^ m` computes `addValQ v π x = m / n`. -/
theorem addValQ_eq_of_zpow (v : Valuation R Γ₀) (π : R) [IsCommensurable v π] {x : R} {m n : ℤ}
    (hx : v x ≠ 0) (hn : 0 < n) (h : v x ^ n = v π ^ m) :
    addValQ v π x = ((m / n : ℚ) : WithTop ℚ) :=
  sorry

/-- **Uniqueness** (§1.4.4): the element pins the valuation. -/
theorem addValQ_unique (v : Valuation R Γ₀) (π : R) [IsCommensurable v π]
    (w : AddValuation R (WithTop ℚ)) (hw : ∀ x y, w x ≤ w y ↔ v y ≤ v x) (hπ : w π = 1) :
    w = addValQ v π :=
  sorry

/-- The `ℤ`-valued additive valuation of a discrete valuation (§1.3.1). -/
noncomputable def addValZ (v : Valuation R Γ₀) [v.IsRankOneDiscrete] :
    AddValuation R (WithTop ℤ) :=
  sorry

theorem addValZ_eq_iff (v : Valuation R Γ₀) [v.IsRankOneDiscrete] (x : R) (k : ℤ) :
    addValZ v x = (k : WithTop ℤ) ↔ v x = ((Valuation.IsRankOneDiscrete.generator v ^ k : Γ₀ˣ) : Γ₀) :=
  sorry

/-- A discrete valuation is commensurable at any uniformiser (§1.4.1), and its `ℚ`-valued valuation
is then the `ℤ`-valued one composed with `Int.cast` (§1.4.5). -/
theorem isCommensurable_of_isUniformizer (v : Valuation R Γ₀) [v.IsRankOneDiscrete] {π : R}
    (hπ : v.IsUniformizer π) : IsCommensurable v π :=
  sorry

end AddVal

section NormedAddVal

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The unnormalised real additive valuation `x ↦ -log ‖x‖` of an ultrametric normed field (§1.2.2).
The fallback instance of convention 2, never the definition. -/
noncomputable def normAddVal : AddValuation K (WithTop ℝ) :=
  sorry

theorem normAddVal_apply {x : K} (hx : x ≠ 0) :
    normAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) :=
  sorry

/-- The `ℤ`-valued additive valuation of a discretely valued ultrametric normed field (§1.3.4). -/
noncomputable def normAddValZ [(NormedField.valuation (K := K)).IsRankOneDiscrete] :
    AddValuation K (WithTop ℤ) :=
  sorry

/-- The `ℚ`-valued additive valuation of an ultrametric normed field of rational rank one,
normalised at `π` (§1.4.6). -/
noncomputable def normAddValQ (π : K) [IsCommensurable (NormedField.valuation (K := K)) π] :
    AddValuation K (WithTop ℚ) :=
  sorry

/-- **Norm recovery** (§1.4.6): `‖x‖ = ‖π‖ ^ (v x)`. No exponential base and no factorisation
hypothesis — normalising at `π` pins the base to `‖π‖⁻¹`. -/
theorem norm_eq_norm_rpow_normAddValQ (π : K) [IsCommensurable (NormedField.valuation (K := K)) π]
    {x : K} {q : ℚ} (hq : normAddValQ K π x = (q : WithTop ℚ)) :
    ‖x‖ = ‖π‖ ^ (q : ℝ) :=
  sorry

variable {K}

/-- **`ℚ_p`** (§1.3.5): the general construction reproduces Mathlib's `Padic.addValuation`. The
discreteness instance is itself a milestone of §1.3.5, taken here as a hypothesis. -/
theorem normAddValZ_padic (p : ℕ) [Fact p.Prime]
    [(NormedField.valuation (K := ℚ_[p])).IsRankOneDiscrete] (x : ℚ_[p]) :
    normAddValZ ℚ_[p] x = Padic.addValuation x :=
  sorry

/-- **`ℂ_p`** (§1.5.4): its valuation is commensurable at `p`, so `normAddValQ ℂ_[p] p` exists with
`normAddValQ ℂ_[p] p p = 1`. -/
theorem isCommensurable_padicComplex (p : ℕ) [Fact p.Prime] :
    IsCommensurable (NormedField.valuation (K := ℂ_[p])) (p : ℂ_[p]) :=
  sorry

end NormedAddVal

/-! ## Layer 2: the polygon of a polynomial and of a power series -/

section Arithmetic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- **A normed additive valuation** (Layer 2 preamble): an additive valuation `v` into `WithTop Γ`,
a strictly monotone `e : Γ →+ ℝ`, and a base `b > 1` with `‖x‖ = b ^ (-(e (v x)))`. The three
members of Layer 1's family are instances: `(normAddValZ K, Int.cast, ‖π‖⁻¹)`,
`(normAddValQ K π, Rat.cast, ‖π‖⁻¹)` and `(normAddVal K, id, exp 1)`. -/
structure IsNormAddVal (v : AddValuation K (WithTop Γ)) (e : Γ →+ ℝ) (b : ℝ) : Prop where
  one_lt : 1 < b
  strictMono : StrictMono e
  norm_eq : ∀ x : K, x ≠ 0 → ∃ γ : Γ, v x = (γ : WithTop Γ) ∧ ‖x‖ = b ^ (-(e γ))

/-- The coefficient valuation sequence of a power series, pushed into `ℝ` (§2.1.1). -/
noncomputable def coeffVal (v : AddValuation K (WithTop Γ)) (e : Γ →+ ℝ) (f : PowerSeries K)
    (i : ℕ) : WithTop ℝ :=
  WithTop.map e (v (f.coeff i))

/-- The Newton polygon of a power series with respect to an additive valuation. -/
noncomputable def _root_.PowerSeries.newtonPolygon (v : AddValuation K (WithTop Γ)) (e : Γ →+ ℝ)
    (f : PowerSeries K) : ℕ → WithTop ℝ :=
  TauCetiRoadmap.NewtonPolygons.newtonPolygon (coeffVal v e f)

/-- The Newton polygon of a polynomial with respect to an additive valuation. -/
noncomputable def _root_.Polynomial.newtonPolygon (v : AddValuation K (WithTop Γ)) (e : Γ →+ ℝ)
    (f : Polynomial K) : ℕ → WithTop ℝ :=
  TauCetiRoadmap.NewtonPolygons.newtonPolygon (coeffVal v e (f : PowerSeries K))

/-- The slope multiset of a polynomial: its `natDegree` unit slopes when `coeff 0 f = 1`, which will
be the negatives of the valuations of the roots. -/
noncomputable def _root_.Polynomial.newtonSlopes (v : AddValuation K (WithTop Γ)) (e : Γ →+ ℝ)
    (f : Polynomial K) : Multiset ℝ :=
  slopeMultiset (f.newtonPolygon v e) f.natDegree

variable {v : AddValuation K (WithTop Γ)} {e : Γ →+ ℝ} {b : ℝ}

/-- A polynomial's coefficient sequence is admissible, so it has a Newton polygon. -/
theorem isAdmissible_coeffVal_polynomial (hv : IsNormAddVal v e b) (f : Polynomial K) :
    IsAdmissible (coeffVal v e (f : PowerSeries K)) :=
  sorry

/-- A series restricted at some positive radius has a Newton polygon. -/
theorem isAdmissible_coeffVal (hv : IsNormAddVal v e b) {f : PowerSeries K} {c : ℝ} (hc : 0 < c)
    (hf : PowerSeries.IsRestricted c f) : IsAdmissible (coeffVal v e f) :=
  sorry

/-- **Integrality** (§2.2.3): the height of the polygon at a vertex lies in the image of `e`. -/
theorem exists_height_eq_of_vertex (hv : IsNormAddVal v e b) (f : Polynomial K) (k : ℕ)
    (hk : unitSlope (f.newtonPolygon v e) k ≠ unitSlope (f.newtonPolygon v e) (k - 1)) :
    ∃ γ : Γ, f.newtonPolygon v e k = ((e γ : ℝ) : WithTop ℝ) :=
  sorry

/-- **Rationality** (§2.2.3): with `Γ = ℤ` every slope of a polynomial is a rational number. This is
the statement convention 2 exists for; it is false for power series (convention 4). -/
theorem newtonSlopes_rat {v : AddValuation K (WithTop ℤ)} (hv : IsNormAddVal v (Int.castAddHom ℝ) b)
    (f : Polynomial K) {m : ℝ} (hm : m ∈ f.newtonSlopes v (Int.castAddHom ℝ)) :
    ∃ q : ℚ, m = q :=
  sorry

/-- **The Gauss-norm dictionary**, in the attained form (§2.3.1): at the radius `b ^ m` the Gauss
norm is the term at the right endpoint of the face of slope `m`, and dominates every other term.

⚠ `PowerSeries.gaussNorm` takes a bare `K → ℝ` while `Polynomial.gaussNorm` takes a `FunLike`
bundle; `Polynomial.gaussNorm_coe_powerSeries` is the bridge. -/
theorem gaussNorm_eq_term_faceRight (hv : IsNormAddVal v e b) (f : PowerSeries K) (m : ℝ)
    (hf : PowerSeries.IsRestricted (b ^ m) f) (n : ℕ) (hn : n = faceRight (f.newtonPolygon v e) m) :
    PowerSeries.gaussNorm norm (b ^ m) f = ‖f.coeff n‖ * (b ^ m) ^ n ∧
      ∀ k, ‖f.coeff k‖ * (b ^ m) ^ k ≤ ‖f.coeff n‖ * (b ^ m) ^ n :=
  sorry

/-- Distinguished at radius `c` of degree `i`: the Gauss norm is attained at `i` and nowhere later
(§2.4.3). A radius-level notion; it does not see the valuation. -/
def IsDistinguishedAt (f : PowerSeries K) (c : ℝ) (i : ℕ) : Prop :=
  ‖f.coeff i‖ * c ^ i = PowerSeries.gaussNorm norm c f ∧
    ∀ k > i, ‖f.coeff k‖ * c ^ k < PowerSeries.gaussNorm norm c f

theorem isDistinguishedAt_of_firstBreak (hv : IsNormAddVal v e b) {f : PowerSeries K} {i : ℕ}
    {m : ℝ} (h0 : f.coeff 0 = 1) (hbreak : unitSlope (f.newtonPolygon v e) i ≠ (m : WithTop ℝ))
    (hlt : ∀ j < i, unitSlope (f.newtonPolygon v e) j = (m : WithTop ℝ)) :
    IsDistinguishedAt f (b ^ m) i :=
  sorry

/-! ## Layer 3: Weierstrass factorisation along the polygon -/

variable [CompleteSpace K]

/-- **Weierstrass division at an arbitrary radius** (§3.1.1). Not a rescaling of the radius-`1` case
when the value group is neither divisible nor dense. A radius-level statement. -/
theorem exists_weierstrassDivision {f g : PowerSeries K} {c : ℝ} {i : ℕ} (hc : 0 < c)
    (hf : PowerSeries.IsRestricted c f) (hg : PowerSeries.IsRestricted c g)
    (hgd : IsDistinguishedAt g c i) :
    ∃! qr : PowerSeries K × Polynomial K,
      f = g * qr.1 + (qr.2 : PowerSeries K) ∧ qr.2.natDegree < i ∧
        PowerSeries.IsRestricted c qr.1 :=
  sorry

/-- **Factorisation at a vertex** (§3.3): the polynomial factor carries exactly the slopes up to the
vertex, and the cofactor is a unit of the disc algebra. ⚠ The bound on `f - g` is relative to the
Gauss norm of `f`, not to `1`. -/
theorem exists_factorisation_at_vertex (hv : IsNormAddVal v e b) {f : PowerSeries K} {j₀ : ℕ}
    {m : ℝ} (h0 : f.coeff 0 = 1) (hf : PowerSeries.IsRestricted (b ^ m) f)
    (hvertex : unitSlope (f.newtonPolygon v e) j₀ ≠ unitSlope (f.newtonPolygon v e) (j₀ - 1))
    (hslope : ∀ j < j₀, unitSlope (f.newtonPolygon v e) j ≤ (m : WithTop ℝ)) :
    ∃ (g : Polynomial K) (u : PowerSeries K),
      f = (g : PowerSeries K) * u ∧ g.natDegree = j₀ ∧ g.coeff 0 = 1 ∧
        PowerSeries.IsRestricted (b ^ m) u ∧
        PowerSeries.gaussNorm norm (b ^ m) (u - 1) < 1 ∧
        PowerSeries.gaussNorm norm (b ^ m) (f - (g : PowerSeries K))
          < PowerSeries.gaussNorm norm (b ^ m) f ∧
        ∀ j ≤ j₀, unitSlope ((g : PowerSeries K).newtonPolygon v e) j
          = unitSlope (f.newtonPolygon v e) j :=
  sorry

/-! ## Layer 4: roots, zeros, and convergence -/

/-- The additive valuation on the algebraic closure extending `v`, normalised at the same element,
pushed into `ℝ` (§1.5, convention 8). It is the valuation induced by `spectralNorm`, so its existence
and its properties are milestones of §1.5, not hypotheses of the root counts below. -/
noncomputable def closureAddVal (hv : IsNormAddVal v e b) :
    AddValuation (AlgebraicClosure K) (WithTop ℝ) :=
  sorry

theorem closureAddVal_algebraMap (hv : IsNormAddVal v e b) (x : K) :
    closureAddVal hv (algebraMap K (AlgebraicClosure K) x) = WithTop.map e (v x) :=
  sorry

/-- **The slope multiset is the multiset of root valuations, negated** (§4.1.3). This is the
statement other developments should cite. -/
theorem newtonSlopes_eq_roots_map (hv : IsNormAddVal v e b) (f : Polynomial K)
    (h0 : f.coeff 0 = 1) :
    f.newtonSlopes v e
      = ((f.map (algebraMap K (AlgebraicClosure K))).roots).map
          fun x ↦ -(closureAddVal hv x).untop₀ :=
  sorry

/-- **The root count on a sphere** (§4.1.1): a segment of slope `m` and length `l` contributes
exactly `l` roots of valuation `-m`. -/
theorem card_roots_eq_length (hv : IsNormAddVal v e b) (f : Polynomial K) (h0 : f.coeff 0 = 1)
    {j₀ l : ℕ} {m : ℝ}
    (hm : ∀ j, j₀ ≤ j → j < j₀ + l → unitSlope (f.newtonPolygon v e) j = (m : WithTop ℝ))
    (hlt : unitSlope (f.newtonPolygon v e) (j₀ + l) ≠ (m : WithTop ℝ)) :
    (Multiset.filter (fun x ↦ closureAddVal hv x = ((-m : ℝ) : WithTop ℝ))
      (f.map (algebraMap K (AlgebraicClosure K))).roots).card = l :=
  sorry

/-- **A face counts roots in a ball** (§4.1.2): valuation at least `-σ` is the closed ball of radius
`b ^ σ`. -/
theorem faceRight_eq_card_roots_le (hv : IsNormAddVal v e b) (f : Polynomial K)
    (h0 : f.coeff 0 = 1) (σ : ℝ) :
    faceRight (f.newtonPolygon v e) σ
      = (Multiset.filter (fun x ↦ ((-σ : ℝ) : WithTop ℝ) ≤ closureAddVal hv x)
          (f.map (algebraMap K (AlgebraicClosure K))).roots).card :=
  sorry

/-- Purity is the statement that all roots have the same valuation (§4.2.1). -/
theorem isPure_iff_forall_val_eq (hv : IsNormAddVal v e b) (f : Polynomial K)
    (h0 : f.coeff 0 = 1) (m : ℝ) :
    IsPure (f.newtonPolygon v e) m ↔ ∀ x ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots,
      closureAddVal hv x = ((-m : ℝ) : WithTop ℝ) :=
  sorry

/-- **The radius of convergence is `b ^ (sup of the slopes)`** (§4.4.2), upper bound — the half that
needs no density hypothesis. `L` is a complete ultrametric extension; `ℂ_[p]` is the model case. -/
theorem not_hasSum_of_lt_slope (hv : IsNormAddVal v e b) {L : Type*} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (f : PowerSeries K) {m : ℝ}
    (hslope : ∀ j, unitSlope (f.newtonPolygon v e) j ≤ (m : WithTop ℝ)) (x : L)
    (hx : b ^ m < ‖x‖) :
    ¬ ∃ s, HasSum (fun n ↦ algebraMap K L (f.coeff n) * x ^ n) s :=
  sorry

/-! ## Layer 5: products -/

/-- **The polygon of a product is the Minkowski sum** (§5.1). ⚠ `SlopesUnbounded` for both factors
cannot be dropped: `(1 - X) * ∑ Xⁱ = 1`. -/
theorem newtonPolygon_mul (hv : IsNormAddVal v e b) (f g : PowerSeries K) (hf0 : f.coeff 0 = 1)
    (hg0 : g.coeff 0 = 1) (hf : SlopesUnbounded (f.newtonPolygon v e))
    (hg : SlopesUnbounded (g.newtonPolygon v e)) :
    (f * g).newtonPolygon v e = minkowski (f.newtonPolygon v e) (g.newtonPolygon v e) :=
  sorry

/-- **The Gauss norm of a product of power series** (§5.4). Mathlib has `Polynomial.gaussNorm_mul`
and, for power series, only `MvPowerSeries.gaussNorm_mul_le`. A radius-level statement. -/
theorem gaussNorm_mul {f g : PowerSeries K} {c : ℝ} (hc : 0 < c)
    (hf : PowerSeries.IsRestricted c f) (hg : PowerSeries.IsRestricted c g) :
    PowerSeries.gaussNorm norm c (f * g)
      = PowerSeries.gaussNorm norm c f * PowerSeries.gaussNorm norm c g :=
  sorry

/-! ## Layer 6: discretely valued fields -/

/-- **The pure-with-coprime-slope criterion** (§6.2.1), over a discretely valued field with its
`ℤ`-valued valuation; Eisenstein is the case `a = -1`. -/
theorem irreducible_of_isPure {v : AddValuation K (WithTop ℤ)}
    (hv : IsNormAddVal v (Int.castAddHom ℝ) b) (f : Polynomial K) (h0 : f.coeff 0 = 1)
    (a : ℤ) (l : ℕ) (hl : 0 < l) (hal : IsCoprime a (l : ℤ)) (hdeg : f.natDegree = l)
    (hpure : IsPure (f.newtonPolygon v (Int.castAddHom ℝ)) ((a : ℝ) / l)) :
    Irreducible f :=
  sorry

end Arithmetic

end TauCetiRoadmap.NewtonPolygons
