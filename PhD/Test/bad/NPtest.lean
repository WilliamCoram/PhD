import PhD.ToPR.NewtonPolygon
import PhD.ToPR.GaussNorm
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Properties of Newton polygons (blueprint §5.4 – §5.8)

This file states results 5.4 – 5.8 of the blueprint.  §5.8 is proved in full; the foundational
valuation API and the geometric core (`firstBreak_slope_le`) are proved and reused.  §5.5, §5.6,
§5.7 are stated with `sorry` proofs: they depend on theory not yet formalised — *polynomial*-level
Weierstrass preparation and root counting (the blueprint itself flags the polynomial Weierstrass
results as still to do).

## The valued ring `R`

The blueprint works over a `p`-adic field `K`.  We generalise `K` to a field `R` together with a
**rank-one (i.e. `ℝ≥0`-valued) valuation** `v : Valuation R ℝ≥0`, taken simply as a hypothesis.  This
is the most flexible primitive: such a `v` can be produced from a `ValuativeRel R` of rank ≤ 1
(`(ValuativeRel.valuation R).map emb`) or from a nonarchimedean normed field (its norm), so the
results apply in either setting without committing to one.  From `v` we read off **both** valuations
the blueprint uses:

* the **multiplicative** valuation `v` itself (as `normVal`, coerced to `ℝ`) — this is `|a|`, used for
  the Gauss norm.  Being a `Valuation`, it carries `map_mul`, `map_one`, `zero_iff`, the
  non-archimedean inequality, … for free; and
* the **additive** valuation `ν a = - logb p |a| : WithTop ℝ` (with `⊤` when `a = 0`), assembled as a
  bona fide `addValuation : AddValuation R (WithTop ℝ)`.  Mathlib's generic `Valuation → AddValuation`
  conversion only relates value groups of the same shape (`AddValuation R Γ₀ :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)`); landing in `WithTop ℝ` (for *real* slopes) is the analytic
  `-logb` step, which we package as `negLogb` and feed to `AddValuation.of`.  So the additive
  valuation has the full `AddValuation` API; its underlying function is `addVal`, which is what the
  Newton-polygon algorithm consumes.

So there is no `IsExpCompatible` hypothesis relating two independent valuations: both come from the
same `v`, and the blueprint's bridge `c = p ^ m` holds by construction (`v a = p ^ (- addVal a)`).
The base `p > 1` only fixes the scale of the `y`-axis; the combinatorics of the polygon are
independent of it.  The additive value group is `Γ = ℝ`, so the machinery of `NewtonPolygon.lean`
runs at `Γ = ℝ` (with trivial `Algebra ℝ ℝ`).

## Building the input to the algorithm

The algorithm consumes a function `ℕ → WithTop ℝ`; we take `coeffVal v p f i = addVal v p (coeff i f)`.
Since `v a = 0 ↔ a = 0` (the valuation of a field has trivial support), an index outside the support
(`coeff i f = 0`) is sent to `⊤` automatically — "send to `⊤` outside the support" with no extra
case split.

## Design choice: how to phrase "the Newton polygon of `f` is …"

We phrase a *local* hypothesis like "the first break is at `(j₀, j₁)` with slope `m`" directly on
the **raw algorithm output** (see `HasFirstBreak`): the constructor `.nextVertex j₀ j₁ l m` already
records the whole break datum — `x`-coordinate, coefficient valuation `j₁`, projected length `l`,
slope `m` — exactly the blueprint's "`(i, mi)`", and there is a rich API for it in
`NewtonPolygon.lean`.  For a *global/shape* property (purity = "only one slope", 5.4) we phrase the
hypothesis on the packaged `NP' (coeffVal v p f)` via its `slopes` sequence.  Route 3
(`IsNewtonPolygon`) adds an existential layer that buys nothing when a concrete `f` is in hand.
-/

@[expose] public section

namespace NewtonPolygon

variable {R : Type*} [Field R] (v : Valuation R NNReal) ℂ_p

/-- The Gauss-norm valuation `R → ℝ` (the multiplicative valuation `v`, coerced to `ℝ`). -/
noncomputable def normVal (a : R) : ℝ := v a

@[simp] theorem normVal_zero : normVal v (0 : R) = 0 := by simp [normVal]

theorem normVal_nonneg (a : R) : 0 ≤ normVal v a := (v a).coe_nonneg

/-- `|a| = p ^ (logb p |a|)`: the bridge between the multiplicative and additive valuations. -/
theorem normVal_eq_rpow {p : ℝ} (hp : 1 < p) {a : R} (ha : a ≠ 0) :
    normVal v a = p ^ (Real.logb p (v a)) := by
  rw [normVal]
  exact (Real.rpow_logb (by linarith) (by linarith) (NNReal.coe_pos.mpr (v.pos_iff.mpr ha))).symm

/-! ### The `-logb` map `ℝ≥0 → WithTop ℝ`

The order-reversing map taking the multiplicative valuation to the additive one.  Mathlib's generic
`Valuation → AddValuation` conversion only moves between value groups of the *same* shape
(`AddValuation R Γ₀ := Valuation R (Multiplicative Γ₀ᵒᵈ)`); landing in `WithTop ℝ` is this analytic
`-logb` step, which we package here so that `addVal` becomes a bona fide `AddValuation`. -/

/-- `negLogb p x = - logb p x`, with `0 ↦ ⊤`. -/
noncomputable def negLogb (p : ℝ) (x : NNReal) : WithTop ℝ :=
  if x = 0 then ⊤ else ((- Real.logb p x : ℝ) : WithTop ℝ)

theorem negLogb_zero (p : ℝ) : negLogb p 0 = ⊤ := if_pos rfl

theorem negLogb_of_ne (p : ℝ) {x : NNReal} (hx : x ≠ 0) :
    negLogb p x = ((- Real.logb p x : ℝ) : WithTop ℝ) := if_neg hx

theorem negLogb_eq_top_iff (p : ℝ) (x : NNReal) : negLogb p x = ⊤ ↔ x = 0 := by
  rw [negLogb]; split_ifs with h
  · simp [h]
  · exact iff_of_false (by simp) h

@[simp] theorem negLogb_one (p : ℝ) : negLogb p 1 = 0 := by rw [negLogb_of_ne p one_ne_zero]; simp

theorem negLogb_mul (p : ℝ) (x y : NNReal) : negLogb p (x * y) = negLogb p x + negLogb p y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [negLogb_zero]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [negLogb_zero]
  rw [negLogb_of_ne p hx, negLogb_of_ne p hy, negLogb_of_ne p (mul_ne_zero hx hy), ← WithTop.coe_add]
  congr 1
  rw [NNReal.coe_mul, Real.logb_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]; ring

/-- For base `p > 1`, `negLogb` reverses order. -/
theorem negLogb_antitone {p : ℝ} (hp : 1 < p) : Antitone (negLogb p) := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha
  · simp [negLogb_zero]
  · have hb : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) (zero_le _))
    rw [negLogb_of_ne p ha, negLogb_of_ne p hb, WithTop.coe_le_coe]
    have : Real.logb p a ≤ Real.logb p b :=
      Real.logb_le_logb_of_le hp (by positivity) (by exact_mod_cast hab)
    linarith

/-- **The additive valuation `ν = - logb p |·|`, as a bona fide `AddValuation R (WithTop ℝ)`.**
Built with `AddValuation.of` directly from `v`'s `Valuation` axioms and the `negLogb` API, so all the
additive-valuation API (`map_mul : ν (xy) = ν x + ν y`, `map_add : min ≤ ν (x+y)`,
`map_zero : ν 0 = ⊤`, `map_one : ν 1 = 0`) is available. -/
noncomputable def addValuation (p : ℝ) (hp : 1 < p) : AddValuation R (WithTop ℝ) :=
  AddValuation.of (fun a => negLogb p (v a))
    (show negLogb p (v 0) = ⊤ by rw [map_zero v, negLogb_zero])
    (show negLogb p (v 1) = 0 by rw [map_one v, negLogb_one])
    (fun x y => by
      show min (negLogb p (v x)) (negLogb p (v y)) ≤ negLogb p (v (x + y))
      calc min (negLogb p (v x)) (negLogb p (v y))
            = negLogb p (max (v x) (v y)) := ((negLogb_antitone hp).map_sup _ _).symm
        _ ≤ negLogb p (v (x + y)) := (negLogb_antitone hp) (v.map_add x y))
    (fun x y => by
      show negLogb p (v (x * y)) = negLogb p (v x) + negLogb p (v y)
      rw [v.map_mul, negLogb_mul])

/-- The **additive** valuation `ν a = - logb p |a| : WithTop ℝ` as a plain function (the underlying
function of `addValuation`; this is what the Newton-polygon algorithm consumes). -/
noncomputable def addVal (p : ℝ) (a : R) : WithTop ℝ := negLogb p (v a)

@[simp] theorem addValuation_apply (p : ℝ) (hp : 1 < p) (a : R) :
    addValuation v p hp a = addVal v p a := rfl

/-- The valuation sequence fed to the Newton-polygon algorithm. -/
noncomputable def coeffVal (p : ℝ) (f : PowerSeries R) : ℕ → WithTop ℝ :=
  fun i => addVal v p (PowerSeries.coeff i f)

theorem addVal_eq_top_iff (p : ℝ) (a : R) : addVal v p a = ⊤ ↔ a = 0 := by
  rw [addVal, negLogb_eq_top_iff]; exact v.zero_iff

theorem addVal_of_ne_zero (p : ℝ) {a : R} (ha : a ≠ 0) :
    addVal v p a = ((- Real.logb p (v a) : ℝ) : WithTop ℝ) := by
  rw [addVal, negLogb_of_ne p (v.ne_zero_iff.mpr ha)]

@[simp] theorem addVal_one (p : ℝ) : addVal v p (1 : R) = 0 := by rw [addVal, map_one v, negLogb_one]

theorem coeffVal_zero_finite (p : ℝ) (f : PowerSeries R) (hf0 : PowerSeries.coeff 0 f = 1) :
    coeffVal v p f 0 = ((0 : ℝ) : WithTop ℝ) := by
  simp only [coeffVal, hf0]; rw [addVal_one]; rfl

omit [Field R] in
@[simp] theorem slopeReal_real (x₀ x₁ : ℕ) (y₀ y₁ : ℝ) :
    slopeReal x₀ x₁ y₀ y₁ = (y₁ - y₀) / (x₁ - x₀) := by
  simp [slopeReal, Algebra.algebraMap_self]

/-! ### Reading the first break off the algorithm -/

/-- **The Newton polygon of `f` has its first break at `(j₀, j₁)`**, reached by a first segment of
projected length `l` and slope `m`.  The blueprint's normalisation `a₀ = 1` (start at the origin) is
captured by taking the length equal to `j₀`. -/
def HasFirstBreak (p : ℝ) (f : PowerSeries R) (j₀ : ℕ) (j₁ : ℝ) (l : ℕ) (m : ℝ) : Prop :=
  newtonPolygon (coeffVal v p f) 0 = some (.nextVertex j₀ j₁ l m)

theorem findFirstFinite_zero (p : ℝ) (f : PowerSeries R) (hf0 : PowerSeries.coeff 0 f = 1) :
    findFirstFinite (coeffVal v p f) 0 = some (0, 0) := by
  classical
  have hfin : finite (coeffVal v p f) 0 := by
    show coeffVal v p f 0 ≠ ⊤
    rw [coeffVal_zero_finite v p f hf0]; exact WithTop.coe_ne_top
  have hex : ∃ i ≥ 0, finite (coeffVal v p f) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  unfold findFirstFinite
  rw [dif_pos hex]
  simp only [hzero, coeffVal_zero_finite v p f hf0]

/-- With `a₀ = 1` the algorithm starts at the origin, so step `0` is `nextStep … 0 0`. -/
theorem newtonPolygon_zero_eq (p : ℝ) (f : PowerSeries R) (hf0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal v p f) 0 = nextStep (coeffVal v p f) 0 0 := by
  conv_lhs => rw [newtonPolygon, findFirstFinite_zero v p f hf0]

/-- **Geometric core.**  Every later finite point lies on/above the first segment of slope `m`,
i.e. `m·k ≤ ν(aₖ)` for all `k > 0`. -/
theorem firstBreak_slope_le (p : ℝ) (f : PowerSeries R)
    {j₀ l : ℕ} {j₁ m : ℝ}
    (hbreak : nextStep (coeffVal v p f) 0 0 = .nextVertex j₀ j₁ l m)
    {k : ℕ} (hk : 0 < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * k ≤ - Real.logb p (v (PowerSeries.coeff k f)) := by
  set vk : ℝ := - Real.logb p (v (PowerSeries.coeff k f)) with hvk
  have hmem : (vk / (k - 0 : ℝ)) ∈ slopeSet (coeffVal v p f) 0 0 := by
    refine ⟨k, hk, ?_, vk, ?_, ?_⟩
    · show coeffVal v p f k ≠ ⊤
      simp only [coeffVal]; rw [ne_eq, addVal_eq_top_iff]; exact hak
    · simp only [coeffVal]; rw [addVal_of_ne_zero v p hak]
    · rw [slopeReal_real]; norm_num
  have hle : m ≤ vk / (k - 0 : ℝ) := by
    rw [nextVertex_slope_eq_sInf'' _ hbreak]
    exact csInf_le (nextVertex_bddBelow _ hbreak) hmem
  rw [sub_zero, le_div_iff₀ (by exact_mod_cast hk)] at hle
  linarith

end NewtonPolygon

/-!
## 5.4  Pure polynomials

"Only one slope" on the packaged `NewtonPolygon`: the `0`-th slope is the real number `m`, and there
is no further (finite) slope.  (As slopes are increasing and `⊤` is absorbing, `slopes 1 = ⊤`
already forces `slopes n = ⊤` for all `n ≥ 1`.)
-/

/-- **Blueprint Definition 5.4.**  A Newton polygon is *pure of slope `m`* when it is a single
segment: its first slope is `m` and it has no later slope. -/
def NewtonPolygon.IsPure (NP : NewtonPolygon) (m : ℝ) : Prop :=
  NP.slopes 0 = (m : WithTopBot ℝ) ∧ NP.slopes 1 = ⊤

namespace NewtonPolygon

variable {R : Type*} [Field R] (v : Valuation R NNReal)

/-- A power series `f` is *pure of slope `m`* if the Newton polygon built from its coefficients
(with base `p`) is pure of slope `m`. -/
def IsPureSeries (p : ℝ) (f : PowerSeries R) (m : ℝ) : Prop :=
  (NP' (coeffVal v p f)).IsPure m

/-!
## 5.5  Irreducible polynomials are pure

Intrinsically about *polynomials*, so we take `f : Polynomial R` and feed its power-series coercion
to the algorithm.  The blueprint argument ("a break at an interior point gives a proper factor")
produces *one* slope without pinning down which, so purity is existential.

`sorry`: needs the factorisation theory (5.7) below. -/
theorem isPureSeries_of_irreducible (p : ℝ) (hp : 1 < p) (f : Polynomial R) (hf : Irreducible f) :
    ∃ m : ℝ, IsPureSeries v p (f : PowerSeries R) m := by
  sorry

/-!
## 5.6  Purity ↔ distinguished

At `c = p ^ m` (genuinely `p ^ m`, since the multiplicative and additive valuations come from the
same `v`), `f` is pure of slope `m` iff its Gauss norm is `1` and is realised by the top coefficient
`b_n` (`|f|_c = |b_n| c^n = 1`), i.e. `f` is `n`-distinguished.

`sorry`: needs the polynomial Gauss-norm/`natDegree` correspondence and the "last achiever"
characterisation of a single segment. -/
theorem isPureSeries_iff_distinguished (p : ℝ) (hp : 1 < p) (f : Polynomial R) (m : ℝ)
    (c : ℝ) (hc : c = p ^ m) :
    IsPureSeries v p (f : PowerSeries R) m ↔
      (PowerSeries.gaussNorm (normVal v) c (f : PowerSeries R)
          = normVal v (PowerSeries.coeff f.natDegree (f : PowerSeries R)) * c ^ f.natDegree
        ∧ PowerSeries.gaussNorm (normVal v) c (f : PowerSeries R) = 1) := by
  sorry

/-!
## 5.7  Factorisation at the first break

The blueprint factors `f` over `ℂ_p`; "no zeros in the closed ball of radius `p^m`" refers to roots
in `ℂ_p`.  We measure roots in the **algebraic closure** `AlgebraicClosure R`, with a chosen
valuation `w : Valuation (AlgebraicClosure R) ℝ≥0` extending `v` (`hw`).  (Completeness of the
closure is *not* assumed yet — it is needed only later, for power series.)

`sorry`: needs polynomial Weierstrass preparation and the root-counting that the blueprint defers. -/
theorem exists_factorisation_of_firstBreak (p : ℝ) (hp : 1 < p) (f : Polynomial R)
    (w : Valuation (AlgebraicClosure R) NNReal)
    (hw : ∀ a : R, w (algebraMap R (AlgebraicClosure R) a) = v a)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak v p (f : PowerSeries R) i j₁ i m)
    (c : ℝ) (hc : c = p ^ m) :
    ∃ g h : Polynomial R,
      f = g * h ∧
      g.natDegree = i ∧
      IsPureSeries v p (g : PowerSeries R) m ∧
      (∀ x : AlgebraicClosure R, (w x : ℝ) ≤ c → Polynomial.aeval x h ≠ 0) := by
  sorry

/-!
## 5.8  Gauss-norm bound below the first slope

With the first break at `(i, mi)` and `a₀ = 1` (the blueprint normalisation `f = 1 + a₁x + …`), for
any positive `c` strictly below `p ^ m` the Gauss norm is `1` and `f` differs from `1` by something
of Gauss norm `< 1`.  **Proved in full.** -/
theorem gaussNorm_eq_one_of_lt_firstBreak (p : ℝ) (hp : 1 < p) (f : PowerSeries R)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak v p f i j₁ i m)
    (c : ℝ) (hc0 : 0 < c) (hc : c < p ^ m) :
    PowerSeries.gaussNorm (normVal v) c f = 1 ∧ PowerSeries.gaussNorm (normVal v) c (f - 1) < 1 := by
  have hp0 : (0:ℝ) < p := by linarith
  have hbreak' : nextStep (coeffVal v p f) 0 0 = .nextVertex i j₁ i m :=
    Option.some_inj.mp ((newtonPolygon_zero_eq v p f hf0).symm.trans hbreak)
  set B : ℝ := p ^ (Real.logb p c - m) with hB
  have hL2 : Real.logb p c < m := (Real.logb_lt_iff_lt_rpow hp hc0).mpr hc
  have hBlt : B < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hBpos : 0 < B := Real.rpow_pos_of_pos hp0 _
  -- per-coefficient bound for `k ≥ 1`
  have term_le_B : ∀ k, 1 ≤ k → normVal v (PowerSeries.coeff k f) * c ^ k ≤ B := by
    intro k hk
    by_cases hak : PowerSeries.coeff k f = 0
    · simp only [hak, normVal_zero, zero_mul]; exact le_of_lt hBpos
    · have hck : c ^ k = p ^ (Real.logb p c * (k : ℝ)) := by
        rw [Real.rpow_mul (le_of_lt hp0), Real.rpow_logb hp0 (by linarith) hc0,
          Real.rpow_natCast]
      have hprod : normVal v (PowerSeries.coeff k f) * c ^ k
          = p ^ (Real.logb p (v (PowerSeries.coeff k f)) + Real.logb p c * (k:ℝ)) := by
        rw [normVal_eq_rpow v hp hak, hck, ← Real.rpow_add hp0]
      rw [hprod, hB]
      apply (Real.rpow_le_rpow_left_iff hp).mpr
      have hL1 := firstBreak_slope_le v p f hbreak' hk hak
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [hL1, hL2, hk1]
  -- `gaussNorm f = 1`
  have hsup1 : PowerSeries.gaussNorm (normVal v) c f = 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le_one : ∀ k, normVal v (PowerSeries.coeff k f) * c ^ k ≤ 1 := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [hf0, normVal]
      · exact le_trans (term_le_B k hk) (le_of_lt hBlt)
    have hbdd : BddAbove (Set.range fun k => normVal v (PowerSeries.coeff k f) * c ^ k) :=
      ⟨1, by rintro _ ⟨k, rfl⟩; exact term_le_one k⟩
    refine le_antisymm (ciSup_le term_le_one) ?_
    have h0 : normVal v (PowerSeries.coeff 0 f) * c ^ 0 = 1 := by simp [hf0, normVal]
    calc (1:ℝ) = normVal v (PowerSeries.coeff 0 f) * c ^ 0 := h0.symm
      _ ≤ _ := le_ciSup hbdd 0
  -- `gaussNorm (f - 1) < 1`
  have hsup2 : PowerSeries.gaussNorm (normVal v) c (f - 1) < 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le : ∀ k, normVal v (PowerSeries.coeff k (f - 1)) * c ^ k ≤ B := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have : PowerSeries.coeff 0 (f - 1) = 0 := by
          rw [map_sub, hf0, PowerSeries.coeff_one]; simp
        simp only [this, normVal_zero, zero_mul]; exact le_of_lt hBpos
      · have hcoe : PowerSeries.coeff k (f - 1) = PowerSeries.coeff k f := by
          rw [map_sub, PowerSeries.coeff_one]; simp [hk.ne']
        rw [hcoe]; exact term_le_B k hk
    calc (⨆ k, normVal v (PowerSeries.coeff k (f - 1)) * c ^ k) ≤ B := ciSup_le term_le
      _ < 1 := hBlt
  exact ⟨hsup1, hsup2⟩

end NewtonPolygon

-- Todo: Port the mathlib Polynomial.gaussNorm file over
-- Finish the Weierstrass div/prep statements for polynomials
