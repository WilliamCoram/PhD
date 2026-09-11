/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«06_Vertices»

/-!
# Step III of [LWX, Theorem 1.3]: the ordinary dimension at the coefficient level — SKELETON

[LWX, Cor 3.21] is phrased as the degree of the ordinary locus over weight space, which drags in
the rigid-analytic packaging this development postpones.  The content actually used in
[LWX, §3.23 Step III] is the *control statement*: the slope-zero dimension is the same at every
character in the disc.  [LWX]'s own proof of Theorem 3.19 supplies exactly that at the coefficient
level (`lwx.txt:1717–1722`):

> "Let `d` be the maximal index such that `c_d(T)` is a unit in `ℤ_p⟦T⟧`, or equivalently, the
> constant term of `c_d(T)` is a `p`-adic unit in `ℤ_p`; such a `d` must exist by Corollary 3.18.
> We claim that `X^{ord}_ω` is finite and flat of degree `d` over `W_ω`."

So the ordinary dimension is `ordDim D ω`, the largest index whose characteristic-series
coefficient is a unit in the halo ring, and Step III's degree formulas are stated against it.
This is in the same register as `IsUnitCoeff` (`PhD/LWX/06_Vertices.lean`) and needs neither
Jacquet–Langlands nor any geometry; see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.

The theta exact sequence's right-exactness (hypothesis H2) is the *other* Step III input and is
not stated here.
-/

open TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The ordinary dimension, at the coefficient level** ([LWX, Thm 3.19 proof]): the maximal index
`d` such that `c_d` is a unit in the halo ring.  This is the content of [LWX, Cor 3.21] with the
weight-space geometry removed. -/
def ordDim (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : ℕ :=
  sSup {n : ℕ | IsUnit (charCoeff (D.op ω) n)}

/-! ### Ingredients -/

/-- A unit of a normed ring all of whose elements have norm at most one has norm exactly one:
`1 = ‖u·u⁻¹‖ ≤ ‖u‖·‖u⁻¹‖ ≤ ‖u‖`. -/
private theorem one_le_norm_of_isUnit_of_norm_le_one {R : Type*} [NormedRing R] [NormOneClass R]
    (hle : ∀ x : R, ‖x‖ ≤ 1) {x : R} (hx : IsUnit x) : 1 ≤ ‖x‖ := by
  obtain ⟨u, rfl⟩ := hx
  calc (1 : ℝ) = ‖((u * u⁻¹ : Rˣ) : R)‖ := by rw [mul_inv_cancel, Units.val_one, norm_one]
    _ = ‖(u : R) * ((u⁻¹ : Rˣ) : R)‖ := by rw [Units.val_mul]
    _ ≤ ‖(u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := norm_mul_le _ _
    _ ≤ ‖(u : R)‖ * 1 := mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
    _ = ‖(u : R)‖ := mul_one _

/-- **[D1a]** A unit of the halo ring has norm one.  Every element of `Λ^{>1/p}` has norm at most
one (`HaloInt.norm_le_one`), so a unit is forced to sit exactly on the unit sphere. -/
theorem HaloInt.one_le_norm_of_isUnit {f : HaloInt p} (hf : IsUnit f) : 1 ≤ ‖f‖ :=
  one_le_norm_of_isUnit_of_norm_le_one HaloInt.norm_le_one hf

/-- **[D1b]** `λ` is positive past the block size: for `t < n` the sum defining
`λ(n) = ∑_{k<n} (⌊k/t⌋ − ⌊k/pt⌋)` contains the term `k = t`, which equals `1`. -/
theorem lwxLambda_pos {p t n : ℕ} (hp : 1 < p) (ht : 0 < t) (htn : t < n) :
    0 < lwxLambda p t n := by
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨t, Finset.mem_range.2 htn, ?_⟩
  have htp : t < p * t := by
    calc t = 1 * t := (one_mul t).symm
      _ < p * t := by exact Nat.mul_lt_mul_of_lt_of_le hp le_rfl ht
  rw [Nat.div_self ht, Nat.div_eq_of_lt htp]
  omega

omit [Fintype ι] in
/-- **[D1c]** If every `n`-element principal minor vanishes then so does `c_n`. -/
theorem charCoeff_eq_zero_of_forall_minor
    {u : c(ι × ℕ, HaloInt p) →L[HaloInt p] c(ι × ℕ, HaloInt p)} {n : ℕ}
    (h : ∀ S : Finset (ι × ℕ), S.card = n → minor u S = 0) : charCoeff u n = 0 := by
  rw [charCoeff, tsum_congr (fun S : {S : Finset (ι × ℕ) // S.card = n} => h S S.2), tsum_zero,
    mul_zero]

/-! ### `ordDim` is well defined -/

/-- The set of unit-coefficient indices is bounded ("such a `d` must exist by Corollary 3.18"):
`‖c_n‖ ≤ p^{−λ(n)}` and `λ(n) → ∞`, so `c_n` is eventually a non-unit.  The two degenerate cases
carry no content: for `ι` empty no finset has positive cardinality, and at `p = 2` the operator
`UpDatum.op` is its junk value `0`; in both, `c_n = 0` for every `n > 0`. -/
theorem le_card_of_isUnit_charCoeff (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {n : ℕ}
    (hn : IsUnit (charCoeff (D.op ω) n)) : n ≤ Fintype.card ι := by
  haveI : Nontrivial (HaloInt p) := NormOneClass.nontrivial
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hcard : Fintype.card ι = 0 := Fintype.card_eq_zero
    by_contra hn0
    have hz : charCoeff (D.op ω) n = 0 :=
      charCoeff_eq_zero_of_forall_minor fun S hS => by
        obtain ⟨a, -⟩ := Finset.card_pos.1 (show 0 < S.card by omega)
        exact hι.elim a.1
    rw [hz] at hn
    exact not_isUnit_zero hn
  by_cases hp2 : p = 2
  · by_contra hn0
    have hop : D.op ω = 0 := by rw [UpDatum.op, dif_neg (not_not.2 hp2)]
    have hz : charCoeff (D.op ω) n = 0 :=
      charCoeff_eq_zero_of_forall_minor fun S hS => by
        haveI : Nonempty { x // x ∈ S } :=
          (Finset.card_pos.1 (show 0 < S.card by omega)).to_subtype
        have hmat : (Matrix.of fun j i : { x // x ∈ S } => matrixCoeff (D.op ω) j i) = 0 := by
          ext i j
          simp [hop]
        rw [minor, hmat, Matrix.det_zero]
    rw [hz] at hn
    exact not_isUnit_zero hn
  by_contra hlt
  rw [not_le] at hlt
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlam : 0 < lwxLambda p (Fintype.card ι) n :=
    lwxLambda_pos hp.out.one_lt (Fintype.card_pos_iff.2 hι) hlt
  have hpow : (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) n : ℤ)) ≤ (p : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ hp1.le (by omega)
  rw [zpow_neg_one] at hpow
  have hlt1 : ‖charCoeff (D.op ω) n‖ < 1 :=
    lt_of_le_of_lt ((norm_charCoeff_upOp_le hp2 D ω n).trans hpow) (inv_lt_one_of_one_lt₀ hp1)
  exact absurd (HaloInt.one_le_norm_of_isUnit hn) (not_le.2 hlt1)

/-- The set of unit-coefficient indices is bounded ("such a `d` must exist by Corollary 3.18"):
past the block size `λ` is positive, so the coefficient has norm `< 1` and cannot be a unit. -/
theorem bddAbove_isUnit_charCoeff (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    BddAbove {n : ℕ | IsUnit (charCoeff (D.op ω) n)} :=
  ⟨Fintype.card ι, fun _ hn => le_card_of_isUnit_charCoeff D ω hn⟩

/-- `c_{ordDim}` is a unit (`c₀ = 1` guarantees the set is nonempty). -/
theorem isUnit_charCoeff_ordDim (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsUnit (charCoeff (D.op ω) (ordDim D ω)) :=
  Nat.sSup_mem ⟨0, by simp⟩ (bddAbove_isUnit_charCoeff D ω)

/-- `r_ord(ω) ≤ t`: the ordinary dimension is at most the number of blocks
(`le_card_of_isUnit_charCoeff` at the unit coefficient `ordDim`). -/
theorem ordDim_le_card (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ordDim D ω ≤ Fintype.card ι :=
  le_card_of_isUnit_charCoeff D ω (isUnit_charCoeff_ordDim D ω)

/-- No coefficient beyond `ordDim` is a unit. -/
theorem not_isUnit_charCoeff_of_ordDim_lt (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {n : ℕ}
    (hn : ordDim D ω < n) : ¬ IsUnit (charCoeff (D.op ω) n) := fun h =>
  absurd (le_csSup (bddAbove_isUnit_charCoeff D ω) h) (not_le.2 hn)

end LWX
