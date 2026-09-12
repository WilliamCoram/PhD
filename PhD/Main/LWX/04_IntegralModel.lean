/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«03_UpMatrix»
import PhD.Main.QMF.Slash.«04_HeckeMatrix»
import PhD.Main.TateFredholm.«06_BlockOp»
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The integral model `S^D_int` (lwx-halo board, tranche H)

[LWX, §2.7] defines the space of integral `p`-adic automorphic forms as
`Iw_q`-equivariant functions valued in `Ind^{Iw_q}_{B(ℤ_p)}([−])`, identified via
(2.3.1) with `C(ℤ_p; Λ)` carrying the action (2.3.2)
`h‖_δ (z) = [cz + d]·h((az+b)/(cz+d))` of the monoid `M₁` (2.3.3).  The sequence
model `c(ℕ, Λ^{>1/p})` realises `C(ℤ_p, Λ^{>1/p})` through the **plain** Mahler
basis `{binom(z,n)}` (Mahler's theorem, applicable since `Λ^{>1/p}` is an
ultrametric `ℤ_p`-Banach algebra): these are the coordinates of [LWX, Prop 3.4],
in which the matrix of `‖_δ` is the entry stream `P_{m,n}(δ)` of `03_UpMatrix.lean`.
The `T`-rescaled submodule `⊕̂ₙ Tⁿ Λ^{>1/p}·binom(z,n)` of [LWX, (5.4.1)] is
realised by `mahlerEmbed`; the rescaling lives in the *estimates*
([LWX, Prop 3.14]), not in the model coordinates — the (2.3.2)-action does not
preserve c₀-coordinates in the rescaled basis (see the H4 section comment).

This tranche instantiates the repo's ring-generic slash layer
(`PhD/Main/QMF/Slash/03_HeckeMonoid.lean`, `04_HeckeMatrix.lean` — `AutomorphicFunction`,
`RightSlashAction`, `slashFixedPointsOfLE`, `heckeOperatorSlash`,
`bijective_evalAtRepsSlash`, all over an arbitrary `Semiring R`) at
`R = HaloInt p`, so that [LWX, (2.11.1)] and the Prop 3.1 display are **reused, not
re-proved**, and [LWX, Prop 3.4] — definitional in `03_UpMatrix.lean` — becomes a
theorem (`cfunSlash_mahlerON`).

Contents: the universal character `[·] : ℤ_p^× →* (Λ^{>1/p})^×` ([LWX, Notation
2.1]); the monoid `M₁` ([LWX, (2.3.3)]); the action (2.3.2) on `C(ℤ_p, HaloInt p)`;
the rescaled embedding `mahlerEmbed` ([LWX, (5.4.1)]) with coefficient extraction by
iterated forward differences; the plain Mahler model `mahlerON`/`mahlerCoeffs` and
the stability theorem `cfunSlash_mahlerON` ([LWX, Prop 3.4] + [LWX, Prop 3.14(2)]);
the transported action `seqSlashAction` on `c(ℕ, HaloInt p)`; the integral space as
`levelSubmoduleSlash`; and the seam `intEvalAtReps_comm` identifying the Hecke
block operator with `UpDatum.op`.

The identification of `M₁` with `QMF.Sigma0'` (they have the same carrier; `Sigma0'`
is stated for a `Valued` field) is optional polish recorded in the ticket, pending a
`Valued ℚ_[p]` instance choice.
-/

open Filter Topology TateFredholm QMF AbstractHeckeOperatorSlash
open scoped fwdDiff TateFredholm QMF

noncomputable section

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### H1 — the universal character ([LWX, Notation 2.1]) -/

/-- The binomial series `(1+T)^s = ∑ₖ binom(s,k) Tᵏ ∈ Λ^{>1/p}` for `s ∈ ℤ_p`
([LWX, Notation 2.1]: `T` corresponds to `[exp(q)] − 1`, so `[exp(qs)] = (1+T)^s`). -/
def oneAddTPow (s : ℤ_[p]) : HaloInt p :=
  ⟨fun j => if 0 ≤ j then Ring.choose s j.toNat else 0, fun j => by
    split_ifs with h
    · calc ‖Ring.choose s j.toNat‖ ≤ 1 := PadicInt.norm_le_one _
        _ = (p : ℝ) ^ (min 0 j) := by rw [min_eq_left h, zpow_zero]
    · rw [norm_zero]
      exact (zpow_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p) _).le⟩

/-- The coefficients of `(1+T)^s` are the binomial coefficients `C(s, j)`. -/
@[simp] theorem coeff_oneAddTPow (s : ℤ_[p]) (j : ℤ) :
    (oneAddTPow p s) j = if 0 ≤ j then Ring.choose s j.toNat else 0 := rfl

/-- `(1+T)^0 = 1`. -/
@[simp] theorem oneAddTPow_zero : oneAddTPow p 0 = 1 := by
  refine DFunLike.ext _ _ fun j => ?_
  rw [coeff_oneAddTPow, HaloInt.coeff_one]
  rcases eq_or_ne j 0 with rfl | hj
  · rw [if_pos le_rfl, if_pos rfl]
    exact Ring.choose_zero_right 0
  · rw [if_neg hj]
    split_ifs with h
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j.toNat = n + 1 := ⟨j.toNat - 1, by omega⟩
      rw [hn]
      exact Ring.choose_zero_succ ℤ_[p] n
    · rfl

/-- Chu–Vandermonde in `Λ^{>1/p}`: `(1+T)^{s+t} = (1+T)^s·(1+T)^t`
(`Ring.add_choose_eq` coefficientwise). -/
theorem oneAddTPow_add (s t : ℤ_[p]) :
    oneAddTPow p (s + t) = oneAddTPow p s * oneAddTPow p t := by
  refine DFunLike.ext _ _ fun k => ?_
  rw [HaloInt.coeff_mul, coeff_oneAddTPow]
  rcases lt_or_ge k 0 with hk | hk
  · rw [if_neg (by omega)]
    symm
    have hz : ∀ i : ℤ, (oneAddTPow p s) i * (oneAddTPow p t) (k - i) = 0 := by
      intro i
      rcases lt_or_ge i 0 with h1 | h1
      · rw [coeff_oneAddTPow, if_neg (by omega), zero_mul]
      · rw [coeff_oneAddTPow (p := p) t, if_neg (by omega : ¬ (0 : ℤ) ≤ k - i), mul_zero]
    rw [tsum_congr hz, tsum_zero]
  · rw [if_pos hk]
    rw [tsum_eq_sum (s := (Finset.range (k.toNat + 1)).map
      ⟨fun n : ℕ => (n : ℤ), Nat.cast_injective⟩) ?_]
    · rw [Finset.sum_map, Ring.add_choose_eq k.toNat (Commute.all s t),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => Ring.choose s i * Ring.choose t j) k.toNat]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      simp only [coeff_oneAddTPow, Function.Embedding.coeFn_mk]
      rw [if_pos (by omega : (0 : ℤ) ≤ (n : ℤ)),
        if_pos (by omega : (0 : ℤ) ≤ k - (n : ℤ))]
      congr 2
      all_goals omega
    · intro i hi
      rcases lt_or_ge i 0 with h1 | h1
      · rw [coeff_oneAddTPow, if_neg (by omega), zero_mul]
      · have h2 : k < i := by
          by_contra hcon
          rw [not_lt] at hcon
          exact hi (Finset.mem_map.mpr
            ⟨i.toNat, Finset.mem_range.mpr (by omega), by simp; omega⟩)
        rw [coeff_oneAddTPow (p := p) t, if_neg (by omega : ¬ (0 : ℤ) ≤ k - i), mul_zero]

variable {p}

/-- The `p ≠ 2`-free integrality margin for `qlog` on the disc (mirror of the
`UpMatrix` private, via the general `norm_padicLog_le`). -/
private theorem norm_qlog_le'' {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖qlog u‖ ≤ (p : ℝ)⁻¹ := by
  have hnp : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p, inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  have h1 : ‖(u : ℚ_[p]) - 1‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [Padic.norm_p,
      show ((u : ℚ_[p]) - 1) = ((u - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring,
      PadicInt.padic_norm_e_of_padicInt]
    exact hu
  have h2 := PadicExpLog.norm_padicLog_le hnp h1
  rw [Padic.norm_p] at h2
  exact h2

/-- The `ℤ_p`-valued normalised logarithm `ℓ(a) = qlog⟨a⟩/p` of a unit (def-hole;
integrality from `norm_qlog_le` at odd `p`; the margin is in fact `p ≠ 2`-free). -/
def logQuot (a : ℤ_[p]ˣ) : ℤ_[p] :=
  ⟨qlog (oneUnitPart a) / (p : ℚ_[p]), by
    rw [norm_div, Padic.norm_p,
      div_le_one (inv_pos.mpr (by exact_mod_cast hp.out.pos))]
    exact norm_qlog_le'' (norm_oneUnitPart_sub_one_le a)⟩

/-- The defining formula `ℓ⟨a⟩ = log(⟨a⟩)/p` of the normalised logarithm, in `ℚ_p`. -/
theorem coe_logQuot (_hp2 : p ≠ 2) (a : ℤ_[p]ˣ) :
    (logQuot a : ℚ_[p]) = qlog (oneUnitPart a) / (p : ℚ_[p]) := rfl

/-- The `ω`-component of the universal character ([LWX, Notation 2.1] at `q = p`,
one weight disc): `[a] = ω(ā)·(1+T)^{ℓ⟨a⟩}`. -/
def univChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a : ℤ_[p]ˣ) : HaloInt p :=
  HaloInt.const (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]) *
    oneAddTPow p (logQuot a)

/-- `ωT(1) = 1`, from multiplicativity by unit cancellation. -/
private theorem teichmuller_one : teichmuller (1 : ℤ_[p]ˣ) = 1 := by
  have h := teichmuller_mul (1 : ℤ_[p]ˣ) 1
  rw [mul_one] at h
  have h2 : teichmuller (1 : ℤ_[p]ˣ) * 1 = teichmuller 1 * teichmuller 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel h2).symm

private theorem oneUnitPart_one : oneUnitPart (1 : ℤ_[p]ˣ) = 1 := by
  rw [oneUnitPart, teichmuller_one]
  simp

private theorem logQuot_one : logQuot (1 : ℤ_[p]ˣ) = 0 := by
  refine Subtype.ext ?_
  show qlog (oneUnitPart 1) / (p : ℚ_[p]) = ((0 : ℤ_[p]) : ℚ_[p])
  rw [oneUnitPart_one, qlog, PadicInt.coe_one, PadicExpLog.padicLog_one, zero_div]
  rfl

/-- The universal character sends `1` to `1`. -/
@[simp] theorem univChar_one (_hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    univChar ω 1 = 1 := by
  rw [univChar, logQuot_one, oneAddTPow_zero, mul_one, map_one, map_one, Units.val_one]
  refine DFunLike.ext _ _ fun j => ?_
  rw [HaloInt.coeff_const, HaloInt.coeff_one]

/-- The one-unit part is multiplicative. -/
private theorem oneUnitPart_mul (a b : ℤ_[p]ˣ) :
    oneUnitPart (a * b) = oneUnitPart a * oneUnitPart b := by
  rw [oneUnitPart, oneUnitPart, oneUnitPart, teichmuller_mul, ← Units.val_mul]
  congr 1
  rw [mul_inv]
  exact mul_mul_mul_comm a b _ _

/-- `ℓ⟨·⟩` is additive. -/
private theorem logQuot_mul (hp2 : p ≠ 2) (a b : ℤ_[p]ˣ) :
    logQuot (a * b) = logQuot a + logQuot b := by
  refine Subtype.ext ?_
  show qlog (oneUnitPart (a * b)) / (p : ℚ_[p])
      = ((logQuot a + logQuot b : ℤ_[p]) : ℚ_[p])
  rw [PadicInt.coe_add, coe_logQuot hp2, coe_logQuot hp2, oneUnitPart_mul,
    qlog_mul hp2 (norm_oneUnitPart_sub_one_le a) (norm_oneUnitPart_sub_one_le b),
    add_div]

/-- `[·]` is multiplicative: `teichmuller_mul` + `qlog_mul` + `oneAddTPow_add`. -/
theorem univChar_mul (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a b : ℤ_[p]ˣ) :
    univChar ω (a * b) = univChar ω a * univChar ω b := by
  rw [univChar, univChar, univChar, logQuot_mul hp2, oneAddTPow_add, map_mul, map_mul,
    Units.val_mul, HaloInt.const_mul]
  ring

/-- The universal character takes values in the unit ball of `Λ^{>1/p}`. -/
theorem norm_univChar_le (_hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a : ℤ_[p]ˣ) :
    ‖univChar ω a‖ ≤ 1 :=
  HaloInt.norm_le_one _

/-! ### H2 — the monoid `M₁` and the action (2.3.2) on `C(ℤ_p, Λ^{>1/p})` -/

variable (p)

/-- The monoid `M₁` of [LWX, (2.3.3)] (at `q = p`): integral matrices with `p | c`,
`d` a unit, and nonzero determinant.  Same carrier shape as `QMF.Sigma0'` (the
`d`-unit monoid); stated with norms over `ℚ_[p]`. -/
def M1 : Submonoid (Matrix (Fin 2) (Fin 2) ℚ_[p]) where
  carrier :=
    {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
    have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact_mod_cast hp.out.one_le
    have hmul : ∀ {x y : ℚ_[p]} {cx cy : ℝ}, ‖x‖ ≤ cx → ‖y‖ ≤ cy →
        0 ≤ cy → ‖x * y‖ ≤ cx * cy := fun hx hy hcy =>
      (norm_mul_le _ _).trans (mul_le_mul hx hy (norm_nonneg _)
        ((norm_nonneg _).trans hx))
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using hmul (hg1 i 0) (hh1 0 j) zero_le_one
      · simpa using hmul (hg1 i 1) (hh1 1 j) zero_le_one
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · calc ‖g 1 0 * h 0 0‖ ≤ (p : ℝ)⁻¹ * 1 := hmul hg2 (hh1 0 0) zero_le_one
          _ = (p : ℝ)⁻¹ := mul_one _
      · calc ‖g 1 1 * h 1 0‖ ≤ 1 * (p : ℝ)⁻¹ :=
            hmul (hg1 1 1) hh2 (by positivity)
          _ = (p : ℝ)⁻¹ := one_mul _
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      have hsmall : ‖g 1 0 * h 0 1‖ < 1 := by
        calc ‖g 1 0 * h 0 1‖ ≤ (p : ℝ)⁻¹ * 1 := hmul hg2 (hh1 0 1) zero_le_one
          _ = (p : ℝ)⁻¹ := mul_one _
          _ < 1 := by
              rw [inv_lt_one_iff₀]
              right
              exact_mod_cast hp.out.one_lt
      have hbig : ‖g 1 1 * h 1 1‖ = 1 := by
        rw [norm_mul, hg3, hh3, mul_one]
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [hbig]; exact hsmall.ne), hbig, max_eq_right hsmall.le]
    · rw [Matrix.det_mul]
      exact mul_ne_zero hg4 hh4
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · simp
    · simp
    · simp

variable {p}

/-- The `(i,j)` entry of an `M₁` element, as an element of `ℤ_[p]`. -/
private def M1.entryInt (g : M1 p) (i j : Fin 2) : ℤ_[p] :=
  ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, g.2.1 i j⟩

@[simp] private theorem M1.coe_entryInt (g : M1 p) (i j : Fin 2) :
    ((M1.entryInt g i j : ℤ_[p]) : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := rfl

private theorem M1.isUnit_entryInt_d (g : M1 p) : IsUnit (M1.entryInt g 1 1) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_def, M1.coe_entryInt]
  exact g.2.2.2.1

/-- Record form of an `M₁` element (integral entries into `ℤ_[p]`, `d` as a unit). -/
def M1.toLocalMat (g : M1 p) : LocalMat p where
  a := M1.entryInt g 0 0
  b := M1.entryInt g 0 1
  c := M1.entryInt g 1 0
  d := (M1.isUnit_entryInt_d g).unit
  hc := by
    rw [PadicInt.norm_def, M1.coe_entryInt]
    exact g.2.2.1

/-- The `a`-entry of the `LocalMat` record of `g ∈ M₁` is `g 0 0`. -/
@[simp] theorem M1.coe_toLocalMat_a (g : M1 p) :
    ((M1.toLocalMat g).a : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 := rfl

/-- The `b`-entry of the `LocalMat` record of `g ∈ M₁` is `g 0 1`. -/
@[simp] theorem M1.coe_toLocalMat_b (g : M1 p) :
    ((M1.toLocalMat g).b : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 := rfl

/-- The `c`-entry of the `LocalMat` record of `g ∈ M₁` is `g 1 0`. -/
@[simp] theorem M1.coe_toLocalMat_c (g : M1 p) :
    ((M1.toLocalMat g).c : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 := rfl

/-- The `d`-entry of the `LocalMat` record of `g ∈ M₁` is `g 1 1`. -/
@[simp] theorem M1.coe_toLocalMat_d (g : M1 p) :
    (((M1.toLocalMat g).d : ℤ_[p]) : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 := by
  rw [show ((M1.toLocalMat g).d : ℤ_[p]) = M1.entryInt g 1 1 from
    (M1.isUnit_entryInt_d g).unit_spec, M1.coe_entryInt]

/-- The denominator `cz + d` as a unit of `ℤ_p` (from `isUnit_c_mul_add`). -/
def LocalMat.denUnit (δ : LocalMat p) (z : ℤ_[p]) : ℤ_[p]ˣ :=
  (δ.isUnit_c_mul_add z).unit

variable (p) in
/-- The function model: continuous `Λ^{>1/p}`-valued functions on `ℤ_p`
([LWX, (2.3.1)]: `Ind^{Iw_q}_{B(ℤ_p)}([−]) ≅ C(ℤ_p; Λ)`). -/
abbrev CFun := C(ℤ_[p], HaloInt p)

/-- `s ↦ (1+T)^s` is continuous: coefficientwise `continuous_choose`, uniform via
the gauge weights (`p`-power targets through `norm_le_zpow_iff`). -/
private theorem continuous_oneAddTPow : Continuous fun s : ℤ_[p] => oneAddTPow p s := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1R
  rw [Metric.continuous_iff]
  intro s ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hpinv1
  -- shrink to the `p`-power target
  have hKz : ((p : ℝ)⁻¹) ^ K = (p : ℝ) ^ (-(K : ℤ)) := by
    rw [zpow_neg, ← inv_zpow, zpow_natCast]
  -- a single δ works for the finitely many low coefficients
  have hcont : ∀ j : ℕ, ContinuousAt (fun x : ℤ_[p] => Ring.choose x j) s :=
    fun j => (PadicInt.continuous_choose j).continuousAt
  have hev : ∀ᶠ t in 𝓝 s, ∀ j ∈ Finset.range K,
      ‖Ring.choose t j - Ring.choose s j‖ ≤ (p : ℝ) ^ (-(K : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro j _
    have h1 : Tendsto (fun t => Ring.choose t j - Ring.choose s j) (𝓝 s) (𝓝 0) := by
      simpa using (hcont j).tendsto.sub (tendsto_const_nhds (x := Ring.choose s j))
    have h2 := (NormedAddGroup.tendsto_nhds_zero.1 h1) _
      (zpow_pos (by positivity : (0 : ℝ) < p) (-(K : ℤ)))
    exact h2.mono fun t ht => ht.le
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ0, fun {t} ht => ?_⟩
  have hcoeffs := hδ t (Metric.mem_ball.mpr ht)
  rw [dist_eq_norm]
  calc ‖oneAddTPow p t - oneAddTPow p s‖ ≤ (p : ℝ) ^ (-(K : ℤ)) := by
        rw [HaloInt.norm_le_zpow_iff]
        intro j
        rw [HaloInt.coeff_sub, coeff_oneAddTPow, coeff_oneAddTPow]
        rcases lt_or_ge j 0 with hj | hj
        · rw [if_neg (by omega), if_neg (by omega), sub_zero, norm_zero]
          exact (zpow_pos (by positivity : (0 : ℝ) < p) _).le
        · rw [if_pos hj, if_pos hj]
          rcases lt_or_ge j.toNat K with hjK | hjK
          · refine (hcoeffs j.toNat (Finset.mem_range.mpr hjK)).trans
              (zpow_le_zpow_right₀ hp1R.le (by omega))
          · calc ‖Ring.choose t j.toNat - Ring.choose s j.toNat‖ ≤ 1 := by
                  rw [sub_eq_add_neg]
                  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
                  · exact PadicInt.norm_le_one _
                  · rw [norm_neg]
                    exact PadicInt.norm_le_one _
              _ ≤ (p : ℝ) ^ (j - (K : ℤ)) := by
                  rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
                  exact zpow_le_zpow_right₀ hp1R.le (by omega)
    _ < ε := by
        rw [← hKz]
        exact hK

@[simp] private theorem denUnit_coe (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.denUnit z : ℤ_[p]ˣ) : ℤ_[p]) = δ.c * z + δ.d :=
  (δ.isUnit_c_mul_add z).unit_spec

private theorem norm_c_mul_le (δ : LocalMat p) (z : ℤ_[p]) :
    ‖δ.c * z‖ ≤ (p : ℝ)⁻¹ := by
  calc ‖δ.c * z‖ ≤ ‖δ.c‖ * ‖z‖ := norm_mul_le _ _
    _ ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul δ.hc (PadicInt.norm_le_one z) (norm_nonneg _)
        (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

/-- The Teichmüller part of the denominator is constant in `z`. -/
private theorem teichmuller_denUnit (δ : LocalMat p) (z : ℤ_[p]) :
    teichmuller (δ.denUnit z) = teichmuller (δ.denUnit 0) := by
  refine teichmuller_eq_of_norm_sub_le ?_
  rw [denUnit_coe, denUnit_coe,
    show δ.c * z + ↑δ.d - (δ.c * 0 + ↑δ.d) = δ.c * z by ring]
  exact norm_c_mul_le δ z

/-- The residue of the denominator is constant in `z`. -/
private theorem toZMod_denUnit (δ : LocalMat p) (z : ℤ_[p]) :
    Units.map (PadicInt.toZMod (p := p)).toMonoidHom (δ.denUnit z)
      = Units.map (PadicInt.toZMod (p := p)).toMonoidHom (δ.denUnit 0) := by
  have hc0 : PadicInt.toZMod δ.c = 0 := by
    have h1 : δ.c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
      have h2 : ‖δ.c‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
        rw [show (p : ℝ) ^ (-((1 : ℕ) : ℤ)) = (p : ℝ)⁻¹ by
          rw [zpow_neg, zpow_natCast, pow_one]]
        exact δ.hc
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
        pow_one] at h2
      exact h2
    exact h1
  refine Units.ext ?_
  show PadicInt.toZMod ((δ.denUnit z : ℤ_[p]ˣ) : ℤ_[p])
      = PadicInt.toZMod ((δ.denUnit 0 : ℤ_[p]ˣ) : ℤ_[p])
  rw [denUnit_coe, denUnit_coe, map_add, map_add, map_mul, map_mul, hc0, zero_mul,
    zero_mul]

/-- The one-unit part of the denominator is affine in `z`. -/
private theorem oneUnitPart_denUnit (δ : LocalMat p) (z : ℤ_[p]) :
    oneUnitPart (δ.denUnit z)
      = (δ.c * z + δ.d) * (((teichmuller (δ.denUnit 0))⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
  rw [oneUnitPart, teichmuller_denUnit, Units.val_mul, denUnit_coe]

private theorem continuous_logQuot_denUnit (δ : LocalMat p) :
    Continuous fun z : ℤ_[p] => logQuot (δ.denUnit z) := by
  refine Continuous.subtype_mk ?_ _
  have hlip : ∀ z w : ℤ_[p],
      dist (qlog (oneUnitPart (δ.denUnit z))) (qlog (oneUnitPart (δ.denUnit w)))
        ≤ dist z w := by
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    refine (norm_qlog_sub_qlog_le (norm_oneUnitPart_sub_one_le _)
      (norm_oneUnitPart_sub_one_le _)).trans ?_
    rw [oneUnitPart_denUnit, oneUnitPart_denUnit,
      show (δ.c * z + ↑δ.d) * ↑(teichmuller (δ.denUnit 0))⁻¹
          - (δ.c * w + ↑δ.d) * ↑(teichmuller (δ.denUnit 0))⁻¹
        = δ.c * (z - w) * ↑(teichmuller (δ.denUnit 0))⁻¹ by ring]
    calc ‖δ.c * (z - w) * (((teichmuller (δ.denUnit 0))⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖
        ≤ ‖δ.c * (z - w)‖ * ‖(((teichmuller (δ.denUnit 0))⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ :=
          norm_mul_le _ _
      _ ≤ ‖z - w‖ * 1 := by
          rw [PadicInt.norm_units]
          refine mul_le_mul ?_ le_rfl zero_le_one (norm_nonneg _)
          calc ‖δ.c * (z - w)‖ ≤ ‖δ.c‖ * ‖z - w‖ := norm_mul_le _ _
            _ ≤ 1 * ‖z - w‖ := mul_le_mul_of_nonneg_right
                (PadicInt.norm_le_one _) (norm_nonneg _)
            _ = ‖z - w‖ := one_mul _
      _ = ‖z - w‖ := mul_one _
  have hlip2 : LipschitzWith 1 fun z : ℤ_[p] => qlog (oneUnitPart (δ.denUnit z)) :=
    LipschitzWith.of_dist_le_mul fun z w => by
      rw [NNReal.coe_one, one_mul]
      exact hlip z w
  exact hlip2.continuous.div_const _

/-- `z ↦ [cz + d]` is continuous. -/
private theorem continuous_univChar_denUnit (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (δ : LocalMat p) : Continuous fun z : ℤ_[p] => univChar ω (δ.denUnit z) := by
  have hfun : (fun z : ℤ_[p] => univChar ω (δ.denUnit z))
      = fun z => HaloInt.const
          (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom (δ.denUnit 0)) : ℤ_[p])
        * oneAddTPow p (logQuot (δ.denUnit z)) := by
    funext z
    rw [univChar, toZMod_denUnit]
  rw [hfun]
  exact continuous_const.mul (continuous_oneAddTPow.comp (continuous_logQuot_denUnit δ))

/-- The Möbius map of a local matrix is `1`-Lipschitz. -/
private theorem lipschitzWith_one_mobiusFun (δ : LocalMat p) :
    LipschitzWith 1 δ.mobiusFun := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hinv_norm : ∀ v : ℤ_[p], ‖Ring.inverse (δ.c * v + (δ.d : ℤ_[p]))‖ = 1 := by
    intro v
    obtain ⟨u, hu⟩ := δ.isUnit_c_mul_add v
    rw [← hu, Ring.inverse_unit]
    exact PadicInt.norm_units _
  have hinv_diff : Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))
      - Ring.inverse (δ.c * w + (δ.d : ℤ_[p]))
      = Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))
        * Ring.inverse (δ.c * w + (δ.d : ℤ_[p])) * (δ.c * (w - z)) := by
    have h1 := Ring.inverse_mul_cancel _ (δ.isUnit_c_mul_add z)
    have h2 := Ring.inverse_mul_cancel _ (δ.isUnit_c_mul_add w)
    have h3 : δ.c * (w - z) = (δ.c * w + (δ.d : ℤ_[p])) - (δ.c * z + (δ.d : ℤ_[p])) := by
      ring
    rw [h3, mul_sub]
    calc Ring.inverse (δ.c * z + ↑δ.d) - Ring.inverse (δ.c * w + ↑δ.d)
        = Ring.inverse (δ.c * z + ↑δ.d)
            * (Ring.inverse (δ.c * w + ↑δ.d) * (δ.c * w + ↑δ.d))
          - (Ring.inverse (δ.c * z + ↑δ.d) * (δ.c * z + ↑δ.d))
            * Ring.inverse (δ.c * w + ↑δ.d) := by
          rw [h1, h2, mul_one, one_mul]
      _ = _ := by ring
  have hdiff : δ.mobiusFun z - δ.mobiusFun w
      = δ.a * (z - w) * Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))
        + (δ.a * w + δ.b) * (Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))
          - Ring.inverse (δ.c * w + (δ.d : ℤ_[p]))) := by
    rw [LocalMat.mobiusFun, LocalMat.mobiusFun]
    ring
  rw [hdiff]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc ‖δ.a * (z - w) * Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))‖
        ≤ ‖δ.a * (z - w)‖ * ‖Ring.inverse (δ.c * z + (δ.d : ℤ_[p]))‖ :=
          norm_mul_le _ _
      _ = ‖δ.a * (z - w)‖ := by rw [hinv_norm, mul_one]
      _ ≤ ‖δ.a‖ * ‖z - w‖ := norm_mul_le _ _
      _ ≤ 1 * ‖z - w‖ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _)
          (norm_nonneg _)
      _ = ‖z - w‖ := one_mul _
  · rw [hinv_diff]
    calc ‖(δ.a * w + δ.b) * (Ring.inverse (δ.c * z + ↑δ.d)
          * Ring.inverse (δ.c * w + ↑δ.d) * (δ.c * (w - z)))‖
        ≤ ‖δ.a * w + δ.b‖ * ‖Ring.inverse (δ.c * z + ↑δ.d)
            * Ring.inverse (δ.c * w + ↑δ.d) * (δ.c * (w - z))‖ := norm_mul_le _ _
      _ ≤ 1 * ‖Ring.inverse (δ.c * z + ↑δ.d)
            * Ring.inverse (δ.c * w + ↑δ.d) * (δ.c * (w - z))‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖Ring.inverse (δ.c * z + ↑δ.d) * Ring.inverse (δ.c * w + ↑δ.d)‖
            * ‖δ.c * (w - z)‖ := by
          rw [one_mul]
          exact norm_mul_le _ _
      _ ≤ 1 * ‖z - w‖ := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one
          · calc ‖Ring.inverse (δ.c * z + ↑δ.d) * Ring.inverse (δ.c * w + ↑δ.d)‖
                ≤ ‖Ring.inverse (δ.c * z + ↑δ.d)‖
                  * ‖Ring.inverse (δ.c * w + ↑δ.d)‖ := norm_mul_le _ _
              _ = 1 := by rw [hinv_norm, hinv_norm, mul_one]
          · calc ‖δ.c * (w - z)‖ ≤ ‖δ.c‖ * ‖w - z‖ := norm_mul_le _ _
              _ ≤ 1 * ‖w - z‖ := mul_le_mul_of_nonneg_right
                  (PadicInt.norm_le_one _) (norm_nonneg _)
              _ = ‖z - w‖ := by rw [one_mul, norm_sub_rev]
      _ = ‖z - w‖ := one_mul _

/-- The action [LWX, (2.3.2)]: `h‖_δ(z) = [cz+d]·h((az+b)/(cz+d))`. -/
def cfunSlash (_hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (h : CFun p) (g : M1 p) :
    CFun p :=
  ⟨fun z => univChar ω ((M1.toLocalMat g).denUnit z) * h ((M1.toLocalMat g).mobiusFun z),
    (continuous_univChar_denUnit ω _).mul
      (h.continuous.comp (lipschitzWith_one_mobiusFun _).continuous)⟩

private theorem coe_den_ne_zero (δ : LocalMat p) (z : ℤ_[p]) :
    (((δ.c * z + (δ.d : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) ≠ 0 := by
  intro hcon
  have h1 : δ.c * z + (δ.d : ℤ_[p]) = 0 := Subtype.coe_injective hcon
  have h2 : ‖δ.c * z + (δ.d : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp (δ.isUnit_c_mul_add z)
  rw [h1, norm_zero] at h2
  exact zero_ne_one h2

private theorem coe_ringInverse_den (δ : LocalMat p) (z : ℤ_[p]) :
    ((Ring.inverse (δ.c * z + (δ.d : ℤ_[p])) : ℤ_[p]) : ℚ_[p])
      = (((δ.c * z + (δ.d : ℤ_[p]) : ℤ_[p])) : ℚ_[p])⁻¹ := by
  obtain ⟨u, hu⟩ := δ.isUnit_c_mul_add z
  rw [← hu, Ring.inverse_unit]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← PadicInt.coe_mul, Units.mul_inv]
  simp

/-- The Möbius value over `ℚ_p`, division form. -/
private theorem coe_mobiusFun (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.mobiusFun z : ℤ_[p]) : ℚ_[p])
      = (((δ.a : ℤ_[p]) : ℚ_[p]) * z + ((δ.b : ℤ_[p]) : ℚ_[p]))
        / (((δ.c : ℤ_[p]) : ℚ_[p]) * z + (((δ.d : ℤ_[p])) : ℚ_[p])) := by
  rw [LocalMat.mobiusFun, PadicInt.coe_mul, coe_ringInverse_den, div_eq_mul_inv]
  push_cast
  ring_nf

/-- The split-form nonvanishing of a denominator over `ℚ_p`. -/
private theorem coe_den_ne_zero' (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.c : ℤ_[p]) : ℚ_[p]) * ((z : ℤ_[p]) : ℚ_[p]) + (((δ.d : ℤ_[p])) : ℚ_[p]) ≠ 0 := by
  have h := coe_den_ne_zero δ z
  push_cast at h
  exact h

/-- The denominator cocycle:
`den_{g₁g₂}(z) = den_{g₁}(möb_{g₂} z)·den_{g₂}(z)` as units of `ℤ_p`. -/
private theorem den_cocycle (g₁ g₂ : M1 p) (z : ℤ_[p]) :
    (M1.toLocalMat (g₁ * g₂)).denUnit z
      = (M1.toLocalMat g₁).denUnit ((M1.toLocalMat g₂).mobiusFun z)
        * (M1.toLocalMat g₂).denUnit z := by
  refine Units.ext (Subtype.coe_injective ?_)
  show ((((M1.toLocalMat (g₁ * g₂)).denUnit z : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
      = ((((M1.toLocalMat g₁).denUnit ((M1.toLocalMat g₂).mobiusFun z)
          * (M1.toLocalMat g₂).denUnit z : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
  rw [Units.val_mul, PadicInt.coe_mul, denUnit_coe, denUnit_coe, denUnit_coe]
  push_cast [coe_mobiusFun]
  simp only [M1.coe_toLocalMat_a, M1.coe_toLocalMat_b, M1.coe_toLocalMat_c,
    M1.coe_toLocalMat_d, Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hB0 := coe_den_ne_zero' (M1.toLocalMat g₂) z
  simp only [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d] at hB0
  field_simp
  ring

/-- Möbius composition: `möb_{g₁g₂} = möb_{g₁} ∘ möb_{g₂}`. -/
private theorem mobius_cocycle (g₁ g₂ : M1 p) (z : ℤ_[p]) :
    (M1.toLocalMat (g₁ * g₂)).mobiusFun z
      = (M1.toLocalMat g₁).mobiusFun ((M1.toLocalMat g₂).mobiusFun z) := by
  set A := M1.toLocalMat g₁ with hA
  set B := M1.toLocalMat g₂ with hB
  set C := M1.toLocalMat (g₁ * g₂) with hC
  -- the denominator cocycle at the level of `ℤ_p` elements
  have h1 : C.c * z + (C.d : ℤ_[p])
      = (A.c * B.mobiusFun z + (A.d : ℤ_[p])) * (B.c * z + (B.d : ℤ_[p])) := by
    have h2 := congrArg Units.val (den_cocycle g₁ g₂ z)
    rw [Units.val_mul] at h2
    rw [show ((C.denUnit z : ℤ_[p]ˣ) : ℤ_[p]) = C.c * z + (C.d : ℤ_[p]) from
        denUnit_coe C z,
      show ((A.denUnit (B.mobiusFun z) : ℤ_[p]ˣ) : ℤ_[p])
          = A.c * B.mobiusFun z + (A.d : ℤ_[p]) from denUnit_coe A _,
      show ((B.denUnit z : ℤ_[p]ˣ) : ℤ_[p]) = B.c * z + (B.d : ℤ_[p]) from
        denUnit_coe B z] at h2
    exact h2
  -- the numerator identity at the level of `ℤ_p` elements
  have h3 : C.a * z + (C.b : ℤ_[p])
      = (A.a * B.mobiusFun z + A.b) * (B.c * z + (B.d : ℤ_[p])) := by
    refine Subtype.coe_injective ?_
    show ((C.a * z + C.b : ℤ_[p]) : ℚ_[p])
        = (((A.a * B.mobiusFun z + A.b) * (B.c * z + (B.d : ℤ_[p])) : ℤ_[p]) : ℚ_[p])
    push_cast [coe_mobiusFun]
    simp only [hA, hB, hC, M1.coe_toLocalMat_a, M1.coe_toLocalMat_b,
      M1.coe_toLocalMat_c, M1.coe_toLocalMat_d, Submonoid.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    have hB0 := coe_den_ne_zero' (M1.toLocalMat g₂) z
    simp only [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d] at hB0 ⊢
    field_simp
    ring
  -- multiply out the Möbius values
  rw [LocalMat.mobiusFun, LocalMat.mobiusFun, h3, h1]
  obtain ⟨uB, huB⟩ := B.isUnit_c_mul_add z
  obtain ⟨uA, huA⟩ := A.isUnit_c_mul_add (B.mobiusFun z)
  rw [← huA, ← huB, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_inv,
    Units.val_mul]
  have hcancel : ((uB : ℤ_[p])) * (((uB⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A.a * B.mobiusFun z + A.b) * (uB : ℤ_[p])
        * (((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((uB⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
      = (A.a * B.mobiusFun z + A.b) * ((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        * ((uB : ℤ_[p]) * ((uB⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) := by ring
    _ = (A.a * B.mobiusFun z + A.b) * ((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
        rw [hcancel, mul_one]

set_option warn.classDefReducibility false in
/-- (2.3.2) is a right action of `M₁` — the cocycle: Möbius composition +
`univChar_mul` ([LWX]: "One checks that this action extends to an action of the
monoid `M₁`"). -/
def cfunSlashAction (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    RightSlashAction (M1 p) (CFun p) where
  slash h g := cfunSlash hp2 ω h g
  zero_slash g := by
    refine ContinuousMap.ext fun z => ?_
    show univChar ω ((M1.toLocalMat g).denUnit z)
        * (0 : CFun p) ((M1.toLocalMat g).mobiusFun z) = (0 : CFun p) z
    simp
  slash_one h := by
    refine ContinuousMap.ext fun z => ?_
    show univChar ω ((M1.toLocalMat 1).denUnit z)
        * h ((M1.toLocalMat 1).mobiusFun z) = h z
    have hden1 : (M1.toLocalMat 1).denUnit z = 1 := by
      refine Units.ext ?_
      rw [denUnit_coe, Units.val_one]
      refine Subtype.coe_injective ?_
      show (((M1.toLocalMat (1 : M1 p)).c * z
            + ((M1.toLocalMat (1 : M1 p)).d : ℤ_[p]) : ℤ_[p]) : ℚ_[p])
          = ((1 : ℤ_[p]) : ℚ_[p])
      push_cast
      simp [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d]
    have hmob1 : (M1.toLocalMat 1).mobiusFun z = z := by
      refine Subtype.coe_injective ?_
      show (((M1.toLocalMat (1 : M1 p)).mobiusFun z : ℤ_[p]) : ℚ_[p])
          = ((z : ℤ_[p]) : ℚ_[p])
      rw [coe_mobiusFun]
      simp [M1.coe_toLocalMat_a, M1.coe_toLocalMat_b, M1.coe_toLocalMat_c,
        M1.coe_toLocalMat_d]
    rw [hden1, hmob1, univChar_one hp2, one_mul]
  slash_mul h g₁ g₂ := by
    refine ContinuousMap.ext fun z => ?_
    show univChar ω ((M1.toLocalMat (g₁ * g₂)).denUnit z)
        * h ((M1.toLocalMat (g₁ * g₂)).mobiusFun z)
      = univChar ω ((M1.toLocalMat g₂).denUnit z)
        * (cfunSlash hp2 ω h g₁) ((M1.toLocalMat g₂).mobiusFun z)
    rw [den_cocycle, mobius_cocycle, univChar_mul hp2]
    show univChar ω _ * univChar ω _ * h _
        = univChar ω _ * (univChar ω _ * h _)
    ring
  add_slash h₁ h₂ g := by
    refine ContinuousMap.ext fun z => ?_
    show univChar ω ((M1.toLocalMat g).denUnit z)
        * (h₁ + h₂) ((M1.toLocalMat g).mobiusFun z)
      = univChar ω ((M1.toLocalMat g).denUnit z) * h₁ ((M1.toLocalMat g).mobiusFun z)
        + univChar ω ((M1.toLocalMat g).denUnit z) * h₂ ((M1.toLocalMat g).mobiusFun z)
    rw [ContinuousMap.add_apply]
    ring

set_option warn.classDefReducibility false in
set_option linter.defProp false in
/-- The scalar-compatibility class for the halo ring (pointwise commutativity). -/
def cfunSMulSlash (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    @RightSlashAction.SMulSlashClass (HaloInt p) (M1 p) (CFun p) _ _ _
      (cfunSlashAction hp2 ω) := by
  letI := cfunSlashAction hp2 ω
  refine { smul_slash := ?_ }
  intro r h g
  refine ContinuousMap.ext fun z => ?_
  show univChar ω ((M1.toLocalMat g).denUnit z)
      * (r • h) ((M1.toLocalMat g).mobiusFun z)
    = (r • (cfunSlash hp2 ω h g)) z
  rw [ContinuousMap.smul_apply, ContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul]
  show univChar ω ((M1.toLocalMat g).denUnit z)
      * (r * h ((M1.toLocalMat g).mobiusFun z))
    = r * (univChar ω ((M1.toLocalMat g).denUnit z)
        * h ((M1.toLocalMat g).mobiusFun z))
  ring

/-! ### the rescaled model ([LWX, (5.4.1)]) -/

private theorem norm_T_pow_mul_le (g : HaloInt p) (n : ℕ) :
    ‖HaloInt.T ^ n * g‖ ≤ ((p : ℝ)⁻¹) ^ n * ‖g‖ := by
  induction n with
  | zero => simp
  | succ n IH =>
      calc ‖HaloInt.T ^ (n + 1) * g‖ = ‖HaloInt.T * (HaloInt.T ^ n * g)‖ := by
            rw [pow_succ]
            ring_nf
      _ = (p : ℝ)⁻¹ * ‖HaloInt.T ^ n * g‖ := HaloInt.norm_T_mul _
      _ ≤ (p : ℝ)⁻¹ * (((p : ℝ)⁻¹) ^ n * ‖g‖) :=
          mul_le_mul_of_nonneg_left IH (by positivity)
      _ = ((p : ℝ)⁻¹) ^ (n + 1) * ‖g‖ := by ring

/-- The general term of the Mahler series, with its uniform bound. -/
private theorem norm_mahler_term_le (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) (n : ℕ) :
    ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)‖
      ≤ ‖a n‖ * ((p : ℝ)⁻¹) ^ n := by
  calc ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)‖
      = ‖HaloInt.T ^ n * (a n * HaloInt.const (Ring.choose z n))‖ := by ring_nf
    _ ≤ ((p : ℝ)⁻¹) ^ n * ‖a n * HaloInt.const (Ring.choose z n)‖ :=
        norm_T_pow_mul_le _ n
    _ ≤ ((p : ℝ)⁻¹) ^ n * (‖a n‖ * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [HaloInt.norm_const]
        exact PadicInt.norm_le_one _
    _ = ‖a n‖ * ((p : ℝ)⁻¹) ^ n := by ring

private theorem tendsto_mahler_term (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    Tendsto (fun n => a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n))
      cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun n => ‖a n‖ * ((p : ℝ)⁻¹) ^ n)
    (fun n => norm_mahler_term_le a z n) ?_
  have h1 : Tendsto (fun n : ℕ => ‖a n‖) atTop (𝓝 0) := by
    have := cSpace.tendsto_cofinite a
    rw [Nat.cofinite_eq_atTop] at this
    simpa using this.norm
  have h2 : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  simpa using h1.mul h2

private theorem summable_mahler_term (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    Summable fun n => a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n) :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_mahler_term a z)

private theorem continuous_mahler_sum (a : c(ℕ, HaloInt p)) :
    Continuous fun z : ℤ_[p] =>
      ∑' n : ℕ, a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n) := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Metric.continuous_iff]
  intro z ε hε
  have h1 : Tendsto (fun n : ℕ => ‖a n‖) atTop (𝓝 0) := by
    have := cSpace.tendsto_cofinite a
    rw [Nat.cofinite_eq_atTop] at this
    simpa using this.norm
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h1) (ε / 2) (by linarith)
  have htail : ∀ w : ℤ_[p], ∀ n, N ≤ n →
      ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n)‖ ≤ ε / 2 := by
    intro w n hn
    refine (norm_mahler_term_le a w n).trans ?_
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖a n‖ * ((p : ℝ)⁻¹) ^ n ≤ ‖a n‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by positivity) (by
              rw [inv_le_one_iff₀]
              right
              exact hp1R.le)) (norm_nonneg _)
      _ = ‖a n‖ := mul_one _
      _ ≤ ε / 2 := h2.le
  have hev : ∀ᶠ w in 𝓝 z, ∀ n ∈ Finset.range N,
      ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n)
        - a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hlip : LipschitzWith 1 fun x : ℤ_[p] => (HaloInt.const x : HaloInt p) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
          show (HaloInt.const x : HaloInt p) - HaloInt.const y
            = HaloInt.const (x - y) from by
            refine DFunLike.ext _ _ fun j => ?_
            rw [HaloInt.coeff_sub, HaloInt.coeff_const, HaloInt.coeff_const,
              HaloInt.coeff_const]
            split_ifs <;> simp,
          HaloInt.norm_const]
    have hc : Continuous fun w : ℤ_[p] =>
        a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n) :=
      continuous_const.mul ((hlip.continuous).comp (PadicInt.continuous_choose n))
    have h3 : Tendsto (fun w : ℤ_[p] =>
        a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n)
          - a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)) (𝓝 z) (𝓝 0) := by
      have h4 := (hc.tendsto z).sub (tendsto_const_nhds
        (x := a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)))
      rwa [sub_self] at h4
    exact ((NormedAddGroup.tendsto_nhds_zero.1 h3) (ε / 2)
      (by linarith)).mono fun w hw => hw.le
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ0, fun {w} hw => ?_⟩
  have hheads := hδ w (Metric.mem_ball.mpr hw)
  rw [dist_eq_norm, ← (summable_mahler_term a w).tsum_sub (summable_mahler_term a z)]
  have hbound : ∀ n : ℕ,
      ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n)
        - a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)‖ ≤ ε / 2 := by
    intro n
    rcases lt_or_ge n N with hn | hn
    · exact hheads n (Finset.mem_range.mpr hn)
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact htail w n hn
      · rw [norm_neg]
        exact htail z n hn
  refine lt_of_le_of_lt ((TateFredholm.norm_tsum_le_iSup ?_).trans
    (Real.iSup_le hbound (by linarith))) (by linarith)
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun n => max
    ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose w n)‖
    ‖a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)‖) (fun n => ?_) ?_
  · rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
  · have hw' := tendsto_mahler_term a w
    have hz' := tendsto_mahler_term a z
    rw [Nat.cofinite_eq_atTop] at hw' hz'
    simpa using hw'.norm.max hz'.norm

/-- The rescaled Mahler embedding `a ↦ ∑ₙ aₙ·Tⁿ·binom(z,n)` of [LWX, (5.4.1)]:
the sequence model `c(ℕ, Λ^{>1/p})` realised inside `C(ℤ_p, Λ^{>1/p})`. -/
def mahlerEmbed : c(ℕ, HaloInt p) →ₗ[HaloInt p] CFun p where
  toFun a := ⟨fun z => ∑' n : ℕ, a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n),
    continuous_mahler_sum a⟩
  map_add' a b := by
    refine ContinuousMap.ext fun z => ?_
    show (∑' n : ℕ, (a + b) n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n))
        = (∑' n : ℕ, a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n))
          + ∑' n : ℕ, b n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)
    rw [← (summable_mahler_term a z).tsum_add (summable_mahler_term b z)]
    refine tsum_congr fun n => ?_
    show (a n + b n) * HaloInt.T ^ n * HaloInt.const (Ring.choose z n) = _
    ring
  map_smul' r a := by
    refine ContinuousMap.ext fun z => ?_
    show (∑' n : ℕ, (r • a) n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n))
        = r * ∑' n : ℕ, a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n)
    rw [← Summable.tsum_mul_left r (summable_mahler_term a z)]
    refine tsum_congr fun n => ?_
    show r * a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n) = _
    ring

/-- The defining formula of the rescaled Mahler embedding, pointwise. -/
theorem mahlerEmbed_apply (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    mahlerEmbed a z = ∑' n : ℕ, a n * HaloInt.T ^ n * HaloInt.const (Ring.choose z n) :=
  rfl

private theorem const_one : (HaloInt.const 1 : HaloInt p) = 1 := by
  refine DFunLike.ext _ _ fun j => ?_
  rw [HaloInt.coeff_const, HaloInt.coeff_one]

private theorem hasSum_finset_sum {κ : Type*} {s : Finset κ} {F : κ → ℕ → HaloInt p}
    {S : κ → HaloInt p} (h : ∀ k ∈ s, HasSum (F k) (S k)) :
    HasSum (fun n => ∑ k ∈ s, F k n) (∑ k ∈ s, S k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k t hk IH =>
      have h1 := (h k (Finset.mem_insert_self k t)).add
        (IH fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hk,
        show (fun n => ∑ k' ∈ insert k t, F k' n)
          = fun n => F k n + ∑ k' ∈ t, F k' n from
        funext fun n => Finset.sum_insert hk]
      exact h1

/-- `const` as an additive monoid homomorphism. -/
private def constHom : ℤ_[p] →+ HaloInt p where
  toFun := HaloInt.const
  map_zero' := by
    refine DFunLike.ext _ _ fun j => ?_
    rw [HaloInt.coeff_const, HaloInt.coeff_zero]
    split_ifs <;> rfl
  map_add' x y := by
    refine DFunLike.ext _ _ fun j => ?_
    rw [HaloInt.coeff_add, HaloInt.coeff_const, HaloInt.coeff_const, HaloInt.coeff_const]
    split_ifs <;> simp

/-- Coefficient extraction by iterated differences: `Δ̃^m(embed a)(0) = aₘ·Tᵐ`
(finite signed sums only — `binom(0, k) = δ_{k0}`; no Mahler theorem needed). -/
theorem fwdDiff_mahlerEmbed (a : c(ℕ, HaloInt p)) (m : ℕ) :
    Δ_[1]^[m] (⇑(mahlerEmbed a)) 0 = a m * HaloInt.T ^ m := by
  -- the per-`n` collapsed difference values
  have hval : ∀ n : ℕ, Δ_[1]^[m] (fun z : ℤ_[p] => Ring.choose z n) 0
      = if n = m then 1 else 0 := by
    intro n
    rw [fwdDiff_iter_choose]
    rcases le_or_gt m n with h | h
    · rcases eq_or_ne n m with rfl | hne
      · rw [if_pos h]
        show Ring.choose (0 : ℤ_[p]) (n - n) = _
        rw [Nat.sub_self, if_pos rfl]
        exact Ring.choose_zero_right 0
      · rw [if_pos h]
        show Ring.choose (0 : ℤ_[p]) (n - m) = _
        rw [if_neg hne]
        obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
        rw [hk]
        exact Ring.choose_zero_succ ℤ_[p] k
    · rw [if_neg (by omega), if_neg (by omega)]
      rfl
  -- swap the finite signed combination with the series
  have hswap : Δ_[1]^[m] (⇑(mahlerEmbed a)) 0
      = ∑' n : ℕ, a n * HaloInt.T ^ n
          * HaloInt.const (Δ_[1]^[m] (fun z : ℤ_[p] => Ring.choose z n) 0) := by
    rw [fwdDiff_iter_eq_sum_shift]
    have hHS : ∀ k ∈ Finset.range (m + 1),
        HasSum (fun n => ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • (a n * HaloInt.T ^ n
              * HaloInt.const (Ring.choose ((0 : ℤ_[p]) + k • 1) n)))
          (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • mahlerEmbed a ((0 : ℤ_[p]) + k • 1)) :=
      fun k _ => (summable_mahler_term a _).hasSum.const_smul _
    rw [← (hasSum_finset_sum hHS).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [fwdDiff_iter_eq_sum_shift,
      show HaloInt.const (∑ k ∈ Finset.range (m + 1),
          ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • Ring.choose ((0 : ℤ_[p]) + k • 1) n)
        = ∑ k ∈ Finset.range (m + 1), ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • HaloInt.const (Ring.choose ((0 : ℤ_[p]) + k • 1) n) from by
        rw [show (HaloInt.const : ℤ_[p] → HaloInt p) = ⇑(constHom (p := p)) from rfl,
          map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact map_zsmul (constHom (p := p)) _ _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm]
  rw [hswap]
  rw [show (fun n : ℕ => a n * HaloInt.T ^ n
      * HaloInt.const (Δ_[1]^[m] (fun z : ℤ_[p] => Ring.choose z n) 0))
    = fun n => if n = m then a m * HaloInt.T ^ m else 0 from funext fun n => by
      rw [hval n]
      split_ifs with h
      · rw [h, const_one, mul_one]
      · rw [show (HaloInt.const 0 : HaloInt p) = 0 from
          DFunLike.ext _ _ fun j => by
            rw [HaloInt.coeff_const, HaloInt.coeff_zero]
            split_ifs <;> rfl, mul_zero]]
  rw [tsum_eq_single m fun n hn => if_neg hn]
  exact if_pos rfl

/-- The rescaled Mahler embedding is injective: `Δ̃^m`-extraction recovers `aₘ·Tᵐ`,
and multiplication by `Tᵐ` is injective on `Λ^{>1/p}`. -/
theorem mahlerEmbed_injective :
    Function.Injective (mahlerEmbed : c(ℕ, HaloInt p) →ₗ[HaloInt p] CFun p) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine DFunLike.ext _ _ fun m => ?_
  have h1 : Δ_[1]^[m] (⇑(mahlerEmbed a)) 0 = 0 := by
    rw [ha]
    show Δ_[1]^[m] (⇑(0 : CFun p)) 0 = 0
    rw [fwdDiff_iter_eq_sum_shift]
    simp
  have h2 := (fwdDiff_mahlerEmbed a m).symm.trans h1
  -- cancel the `T`-power coefficientwise
  refine DFunLike.ext _ _ fun j => ?_
  have h3 := DFunLike.congr_fun h2 (j + m)
  rw [mul_comm, HaloInt.coeff_T_pow_mul] at h3
  have hz : ((0 : c(ℕ, HaloInt p)) m) j = 0 := rfl
  rw [hz]
  simpa using h3

/-! ### H4 — the plain Mahler model and [LWX, Prop 3.4] as a theorem

The action (2.3.2) does **not** preserve the `T`-rescaled coordinates of
`mahlerEmbed` inside `c(ℕ, Λ^{>1/p})` (for `g = [[p,0],[p,1]]` the slash of the
constant `1` is `(1+T)^{ℓ(1+pz)}`, whose rescaled coefficients have norm `1` for
every `m`).  [LWX, Prop 3.4] expands the slash in the *plain* Mahler basis, where
the matrix is exactly the entry streams `P_{m,n}(δ)` of `03_UpMatrix.lean` — matching
`UpDatum.matrix` — and c₀-decay of the coefficients is Bojanić–Mahler
(`PadicInt.fwdDiff_tendsto_zero`); the `T`-rescaling lives in the *estimates*
([LWX, Prop 3.14]), not in the module coordinates. -/

private theorem tendsto_coeff_atTop (a : c(ℕ, HaloInt p)) :
    Tendsto (fun n : ℕ => (a n : HaloInt p)) atTop (𝓝 0) := by
  have h := cSpace.tendsto_cofinite a
  rwa [Nat.cofinite_eq_atTop] at h

private theorem summable_mahler_smul (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    Summable fun n : ℕ => mahler n z • (a n : HaloInt p) := by
  refine TateFredholm.summable_of_tendsto_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun n : ℕ => ‖(a n : HaloInt p)‖) (fun n => ?_) ?_
  · refine (norm_smul_le _ _).trans ?_
    calc ‖mahler n z‖ * ‖(a n : HaloInt p)‖
        ≤ 1 * ‖(a n : HaloInt p)‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖(a n : HaloInt p)‖ := one_mul _
  · simpa using (tendsto_coeff_atTop a).norm

/-- The plain Mahler realisation `a ↦ ∑ₙ aₙ·binom(z,n)` of the sequence model inside
`C(ℤ_p, Λ^{>1/p})` — the coordinates in which [LWX, Prop 3.4] is stated. -/
def mahlerON : c(ℕ, HaloInt p) →ₗ[HaloInt p] CFun p where
  toFun a := PadicInt.mahlerSeries fun n => (a n : HaloInt p)
  map_add' a b := by
    refine ContinuousMap.ext fun z => ?_
    show PadicInt.mahlerSeries (fun n => ((a + b) n : HaloInt p)) z
        = PadicInt.mahlerSeries (fun n => (a n : HaloInt p)) z
          + PadicInt.mahlerSeries (fun n => (b n : HaloInt p)) z
    rw [PadicInt.mahlerSeries_apply (tendsto_coeff_atTop _),
      PadicInt.mahlerSeries_apply (tendsto_coeff_atTop a),
      PadicInt.mahlerSeries_apply (tendsto_coeff_atTop b),
      ← (summable_mahler_smul a z).tsum_add (summable_mahler_smul b z)]
    refine tsum_congr fun n => ?_
    show mahler n z • ((a n : HaloInt p) + b n) = _
    rw [smul_add]
  map_smul' r a := by
    refine ContinuousMap.ext fun z => ?_
    show PadicInt.mahlerSeries (fun n => ((r • a) n : HaloInt p)) z
        = r * PadicInt.mahlerSeries (fun n => (a n : HaloInt p)) z
    rw [PadicInt.mahlerSeries_apply (tendsto_coeff_atTop _),
      PadicInt.mahlerSeries_apply (tendsto_coeff_atTop a),
      ← Summable.tsum_mul_left r (summable_mahler_smul a z)]
    refine tsum_congr fun n => ?_
    show mahler n z • (r * (a n : HaloInt p))
        = r * (mahler n z • (a n : HaloInt p))
    rw [HaloInt.smul_def, HaloInt.smul_def]
    ring

/-- The defining pointwise formula of the plain Mahler realisation. -/
theorem mahlerON_apply (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    mahlerON a z = ∑' n : ℕ, a n * HaloInt.const (Ring.choose z n) := by
  show PadicInt.mahlerSeries (fun n => (a n : HaloInt p)) z = _
  rw [PadicInt.mahlerSeries_apply (tendsto_coeff_atTop a)]
  refine tsum_congr fun n => ?_
  rw [mahler_apply, HaloInt.smul_def, mul_comm]

/-- Coefficient recovery for the plain realisation: `Δ̃^m(mahlerON a)(0) = aₘ`
(mathlib's `fwdDiff_mahlerSeries`). -/
theorem fwdDiff_mahlerON (a : c(ℕ, HaloInt p)) (m : ℕ) :
    Δ_[1]^[m] (⇑(mahlerON a)) 0 = a m :=
  PadicInt.fwdDiff_mahlerSeries (tendsto_coeff_atTop a) m

/-- The plain Mahler realisation is injective. -/
theorem mahlerON_injective :
    Function.Injective (mahlerON : c(ℕ, HaloInt p) →ₗ[HaloInt p] CFun p) := by
  intro a b h
  refine DFunLike.ext _ _ fun m => ?_
  rw [← fwdDiff_mahlerON a m, ← fwdDiff_mahlerON b m, h]

/-- The Mahler coefficient stream `m ↦ Δ̃^m F(0)` of a `Λ^{>1/p}`-valued continuous
function, as an element of the sequence model — c₀-decay is Bojanić–Mahler
(`PadicInt.fwdDiff_tendsto_zero`, applicable since `Λ^{>1/p}` is an ultrametric
`ℤ_p`-Banach algebra). -/
def mahlerCoeffs (F : CFun p) : c(ℕ, HaloInt p) :=
  ⟨⟨fun m : Ix ℕ => Δ_[1]^[m] (⇑F) 0, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    have h := PadicInt.fwdDiff_tendsto_zero (E := HaloInt p) F
    rwa [← Nat.cofinite_eq_atTop] at h⟩

/-- The defining formula of the coefficient stream. -/
@[simp] theorem mahlerCoeffs_apply (F : CFun p) (m : ℕ) :
    mahlerCoeffs F m = Δ_[1]^[m] (⇑F) 0 := rfl

/-- **Mahler's theorem** in the model: every `F : C(ℤ_p, Λ^{>1/p})` is the plain
Mahler series of its coefficient stream (`PadicInt.hasSum_mahler`). -/
theorem mahlerON_mahlerCoeffs (F : CFun p) : mahlerON (mahlerCoeffs F) = F := by
  show PadicInt.mahlerSeries (fun m : ℕ => Δ_[1]^[m] (⇑F) 0) = F
  exact (PadicInt.hasSum_mahler F).tsum_eq

/-- The coefficient stream of a realised sequence is the sequence. -/
theorem mahlerCoeffs_mahlerON (a : c(ℕ, HaloInt p)) : mahlerCoeffs (mahlerON a) = a :=
  DFunLike.ext _ _ fun m => fwdDiff_mahlerON a m

private theorem denUnit_zero (δ : LocalMat p) : δ.denUnit 0 = δ.d := by
  refine Units.ext ?_
  rw [denUnit_coe]
  ring

private theorem oneUnitPart_denUnit_factor (δ : LocalMat p) (z : ℤ_[p]) :
    oneUnitPart (δ.denUnit z) = oneUnitPart δ.d * (1 + δ.wCoeff * z) := by
  have hdw : (δ.d : ℤ_[p]) * δ.wCoeff = δ.c := by
    rw [LocalMat.wCoeff, show (δ.d : ℤ_[p]) * (δ.c * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
        = δ.c * ((δ.d : ℤ_[p]) * ((δ.d⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) from by ring,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [oneUnitPart_denUnit, denUnit_zero, oneUnitPart, Units.val_mul,
    show ((δ.d : ℤ_[p]ˣ) : ℤ_[p]) * (((teichmuller δ.d)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        * (1 + δ.wCoeff * z)
      = ((δ.d : ℤ_[p]) * (1 + δ.wCoeff * z))
        * (((teichmuller δ.d)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) from by ring]
  congr 1
  rw [mul_add, mul_one,
    show (δ.d : ℤ_[p]) * (δ.wCoeff * z) = ((δ.d : ℤ_[p]) * δ.wCoeff) * z from by ring,
    hdw]
  ring

/-- The exponent bridge: the normalised log of the denominator is the `gFun` of the
[LWX, Prop 3.14] proof. -/
private theorem logQuot_denUnit (hp2 : p ≠ 2) (δ : LocalMat p) (z : ℤ_[p]) :
    logQuot (δ.denUnit z) = δ.gFun z := by
  have hw : ‖(1 + δ.wCoeff * z) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [add_sub_cancel_left]
    calc ‖δ.wCoeff * z‖ ≤ ‖δ.wCoeff‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul (LocalMat.norm_wCoeff_le δ)
          (PadicInt.norm_le_one z) (norm_nonneg _) (by positivity)
      _ = (p : ℝ)⁻¹ := mul_one _
  refine Subtype.ext ?_
  show qlog (oneUnitPart (δ.denUnit z)) / (p : ℚ_[p]) = ((δ.gFun z : ℤ_[p]) : ℚ_[p])
  rw [LocalMat.coe_gFun, oneUnitPart_denUnit_factor,
    qlog_mul hp2 (norm_oneUnitPart_sub_one_le δ.d) hw]

/-- Coefficient evaluation as an additive homomorphism. -/
private def coeffHom (r : ℤ) : HaloInt p →+ ℤ_[p] where
  toFun f := f r
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem addMonoidHom_fwdDiff_iter {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (φ : M →+ N) (f : ℤ_[p] → M) (m : ℕ) (z : ℤ_[p]) :
    Δ_[1]^[m] (fun w => φ (f w)) z = φ (Δ_[1]^[m] f z) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]
  exact Finset.sum_congr rfl fun k _ => (map_zsmul φ _ _).symm

private theorem coeff_const_mul_oneAddTPow_mul_const (A B s : ℤ_[p]) (r : ℤ) :
    (HaloInt.const A * oneAddTPow p s * HaloInt.const B) r
      = if 0 ≤ r then A * (B * Ring.choose s r.toNat) else 0 := by
  rw [show HaloInt.const A * oneAddTPow p s * HaloInt.const B
      = HaloInt.const A * (HaloInt.const B * oneAddTPow p s) from by ring,
    HaloInt.coeff_const_mul, HaloInt.coeff_const_mul, coeff_oneAddTPow]
  split_ifs <;> simp

/-- The `T`-coefficients of a slashed basis function: `ω(d̄)·binom(g(z), r)`
against `binom(f(z), n)`.  (Public: `11_SeamH.lean` reproduces `entry_eq_fwdDiff` for the
disc model from it.) -/
theorem coeff_univChar_mul_const (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (δ : LocalMat p) (n : ℕ) (z : ℤ_[p]) (r : ℤ) :
    (univChar ω (δ.denUnit z) * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) r
      = if 0 ≤ r
        then (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p])
          * (Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat)
        else 0 := by
  rw [univChar, toZMod_denUnit, denUnit_zero, logQuot_denUnit hp2,
    coeff_const_mul_oneAddTPow_mul_const]

/-- **The identification behind [LWX, Prop 3.4]**: the entry stream `P_{m,n}(δ)` is
the `m`-th Mahler coefficient of the slashed basis function
`z ↦ [cz+d]·binom(möb_δ(z), n)`. -/
private theorem entry_eq_fwdDiff (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (δ : LocalMat p) (m n : ℕ) :
    entry ω δ m n
      = Δ_[1]^[m] (fun z => univChar ω (δ.denUnit z)
          * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 0 := by
  refine DFunLike.ext _ _ fun r => ?_
  have hcomm : Δ_[1]^[m] (fun z => (univChar ω (δ.denUnit z)
      * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r) 0
      = (Δ_[1]^[m] (fun z => univChar ω (δ.denUnit z)
          * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 0) r :=
    addMonoidHom_fwdDiff_iter (coeffHom r)
      (fun z => univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) m 0
  rw [coeff_entry, ← hcomm]
  rcases le_or_gt 0 r with h | h
  · rw [show (fun z => (univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r)
        = fun z => (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p])
            * (Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat) from
        funext fun z => by rw [coeff_univChar_mul_const hp2 ω δ n z r, if_pos h],
      entryCoeff, dif_pos h]
    exact (addMonoidHom_fwdDiff_iter
      (AddMonoidHom.mulLeft
        ((ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p])))
      (fun z => Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat)
      m 0).symm
  · rw [show (fun z => (univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r)
        = fun _ => (0 : ℤ_[p]) from
        funext fun z => by rw [coeff_univChar_mul_const hp2 ω δ n z r, if_neg (not_le.mpr h)],
      entryCoeff, dif_neg (not_le.mpr h)]
    simp [fwdDiff_iter_eq_sum_shift]

private theorem summable_plain (a : c(ℕ, HaloInt p)) (w : ℤ_[p]) :
    Summable fun n : ℕ => a n * HaloInt.const (Ring.choose w n) := by
  refine TateFredholm.summable_of_tendsto_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun n : ℕ => ‖(a n : HaloInt p)‖) (fun n => ?_) ?_
  · calc ‖a n * HaloInt.const (Ring.choose w n)‖
        ≤ ‖(a n : HaloInt p)‖ * ‖(HaloInt.const (Ring.choose w n) : HaloInt p)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(a n : HaloInt p)‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [HaloInt.norm_const]
          exact PadicInt.norm_le_one _
      _ = ‖(a n : HaloInt p)‖ := mul_one _
  · simpa using (tendsto_coeff_atTop a).norm

private theorem summable_slash_term (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (g : M1 p)
    (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    Summable fun n : ℕ => a n * (univChar ω ((M1.toLocalMat g).denUnit z)
      * HaloInt.const (Ring.choose ((M1.toLocalMat g).mobiusFun z) n)) := by
  refine TateFredholm.summable_of_tendsto_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun n : ℕ => ‖(a n : HaloInt p)‖) (fun n => ?_) ?_
  · calc ‖a n * (univChar ω ((M1.toLocalMat g).denUnit z)
        * HaloInt.const (Ring.choose ((M1.toLocalMat g).mobiusFun z) n))‖
        ≤ ‖(a n : HaloInt p)‖ * ‖univChar ω ((M1.toLocalMat g).denUnit z)
            * HaloInt.const (Ring.choose ((M1.toLocalMat g).mobiusFun z) n)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(a n : HaloInt p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (HaloInt.norm_le_one _) (norm_nonneg _)
      _ = ‖(a n : HaloInt p)‖ := mul_one _
  · simpa using (tendsto_coeff_atTop a).norm

private theorem cfunSlash_mahlerON_apply (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (g : M1 p) (a : c(ℕ, HaloInt p)) (z : ℤ_[p]) :
    cfunSlash hp2 ω (mahlerON a) g z
      = ∑' n : ℕ, a n * (univChar ω ((M1.toLocalMat g).denUnit z)
          * HaloInt.const (Ring.choose ((M1.toLocalMat g).mobiusFun z) n)) := by
  show univChar ω ((M1.toLocalMat g).denUnit z)
      * mahlerON a ((M1.toLocalMat g).mobiusFun z) = _
  rw [mahlerON_apply,
    ← Summable.tsum_mul_left (univChar ω ((M1.toLocalMat g).denUnit z))
      (summable_plain a ((M1.toLocalMat g).mobiusFun z))]
  refine tsum_congr fun n => ?_
  ring

/-- The Mahler coefficients of a slashed realisation: the entry-stream pairing
`Δ̃^m(mahlerON a ∣ g)(0) = ∑ₙ aₙ·P_{m,n}(δ_g)`. -/
private theorem fwdDiff_cfunSlash_mahlerON (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (g : M1 p) (a : c(ℕ, HaloInt p)) (m : ℕ) :
    Δ_[1]^[m] (⇑(cfunSlash hp2 ω (mahlerON a) g)) 0
      = ∑' n : ℕ, a n * entry ω (M1.toLocalMat g) m n := by
  have hswap : Δ_[1]^[m] (⇑(cfunSlash hp2 ω (mahlerON a) g)) 0
      = ∑' n : ℕ, Δ_[1]^[m] (fun z =>
          a n * (univChar ω ((M1.toLocalMat g).denUnit z)
            * HaloInt.const (Ring.choose ((M1.toLocalMat g).mobiusFun z) n))) 0 := by
    rw [fwdDiff_iter_eq_sum_shift]
    have hHS : ∀ k ∈ Finset.range (m + 1),
        HasSum (fun n => ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • (a n * (univChar ω ((M1.toLocalMat g).denUnit ((0 : ℤ_[p]) + k • 1))
              * HaloInt.const
                  (Ring.choose ((M1.toLocalMat g).mobiusFun ((0 : ℤ_[p]) + k • 1)) n))))
          (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ))
            • cfunSlash hp2 ω (mahlerON a) g ((0 : ℤ_[p]) + k • 1)) := by
      intro k _
      have h1 := (summable_slash_term ω g a ((0 : ℤ_[p]) + k • 1)).hasSum
      rw [← cfunSlash_mahlerON_apply hp2 ω g a ((0 : ℤ_[p]) + k • 1)] at h1
      exact h1.const_smul _
    rw [← (hasSum_finset_sum hHS).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [fwdDiff_iter_eq_sum_shift]
  rw [hswap]
  refine tsum_congr fun n => ?_
  rw [entry_eq_fwdDiff hp2 ω (M1.toLocalMat g) m n]
  exact addMonoidHom_fwdDiff_iter (AddMonoidHom.mulLeft (a n)) _ m 0

/-- **[LWX, Prop 3.4] as a theorem + [LWX, §5.4]'s stability**: the (2.3.2)-action
maps the plain Mahler model to itself, with matrix the entry streams of
`03_UpMatrix.lean`: `bₘ = ∑ₙ aₙ·P_{m,n}(δ)`.  Shared-witness existential: the
coefficient stream `b` (c₀ by Bojanić–Mahler decay). -/
theorem cfunSlash_mahlerON (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (g : M1 p) (a : c(ℕ, HaloInt p)) :
    ∃ b : c(ℕ, HaloInt p), cfunSlash hp2 ω (mahlerON a) g = mahlerON b ∧
      ∀ m : ℕ, b m = ∑' n : ℕ, a n * entry ω (M1.toLocalMat g) m n :=
  ⟨mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g),
    (mahlerON_mahlerCoeffs _).symm,
    fun m => by rw [mahlerCoeffs_apply, fwdDiff_cfunSlash_mahlerON hp2 ω g a m]⟩

set_option warn.classDefReducibility false in
/-- The transported action on the sequence model `c(ℕ, Λ^{>1/p})` — the home of the
determinant theory: `a ∣ₛ g` is the Mahler coefficient stream of the slashed
realisation. -/
def seqSlashAction (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    RightSlashAction (M1 p) (c(ℕ, HaloInt p)) where
  slash a g := mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g)
  zero_slash g := by
    rw [show mahlerON (0 : c(ℕ, HaloInt p)) = 0 from map_zero _,
      show cfunSlash hp2 ω 0 g = 0 from
        RightSlashAction.zero_slash (self := cfunSlashAction hp2 ω) g]
    refine DFunLike.ext _ _ fun m => ?_
    have h0 : ((0 : c(ℕ, HaloInt p)) m) = (0 : HaloInt p) := rfl
    rw [mahlerCoeffs_apply, h0, show ⇑(0 : CFun p) = fun _ => (0 : HaloInt p) from rfl]
    simp [fwdDiff_iter_eq_sum_shift]
  slash_one a := by
    rw [show cfunSlash hp2 ω (mahlerON a) 1 = mahlerON a from
      RightSlashAction.slash_one (self := cfunSlashAction hp2 ω) (mahlerON a)]
    exact mahlerCoeffs_mahlerON a
  slash_mul a g₁ g₂ := by
    have h1 : cfunSlash hp2 ω (mahlerON a) (g₁ * g₂)
        = cfunSlash hp2 ω (cfunSlash hp2 ω (mahlerON a) g₁) g₂ :=
      RightSlashAction.slash_mul (self := cfunSlashAction hp2 ω) (mahlerON a) g₁ g₂
    have h2 : cfunSlash hp2 ω (mahlerON a) g₁
        = mahlerON (mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g₁)) :=
      (mahlerON_mahlerCoeffs _).symm
    show mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) (g₁ * g₂)) = _
    conv_lhs => rw [h1, h2]
  add_slash a b g := by
    rw [show mahlerON (a + b) = mahlerON a + mahlerON b from map_add _ a b,
      show cfunSlash hp2 ω (mahlerON a + mahlerON b) g
          = cfunSlash hp2 ω (mahlerON a) g + cfunSlash hp2 ω (mahlerON b) g from
        RightSlashAction.add_slash (self := cfunSlashAction hp2 ω) _ _ g]
    refine DFunLike.ext _ _ fun m => ?_
    show Δ_[1]^[m] (⇑(cfunSlash hp2 ω (mahlerON a) g
        + cfunSlash hp2 ω (mahlerON b) g)) 0
      = mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g) m
        + mahlerCoeffs (cfunSlash hp2 ω (mahlerON b) g) m
    rw [ContinuousMap.coe_add, fwdDiff_iter_add]
    rfl

/-- The bridge: the transported slash realises the (2.3.2)-slash. -/
theorem mahlerON_seqSlash (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (a : c(ℕ, HaloInt p)) (g : M1 p) :
    mahlerON (RightSlashAction.slash (self := seqSlashAction hp2 ω) a g)
      = cfunSlash hp2 ω (mahlerON a) g :=
  mahlerON_mahlerCoeffs _

/-- The slash of the transported action commutes with the `Λ^{>1/p}`-scalars
(the sequence-model mirror of `cfunSMulSlash`, via `fwdDiff_iter_const_smul`). -/
theorem seqSMulSlash (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    @RightSlashAction.SMulSlashClass (HaloInt p) (M1 p) (c(ℕ, HaloInt p)) _ _ _
      (seqSlashAction hp2 ω) := by
  letI := seqSlashAction hp2 ω
  refine { smul_slash := ?_ }
  intro r a g
  show mahlerCoeffs (cfunSlash hp2 ω (mahlerON (r • a)) g)
      = r • mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g)
  rw [show mahlerON (r • a) = r • mahlerON a from map_smul _ r a,
    show cfunSlash hp2 ω (r • mahlerON a) g = r • cfunSlash hp2 ω (mahlerON a) g from
      RightSlashAction.SMulSlashClass.smul_slash (self := cfunSMulSlash hp2 ω)
        r (mahlerON a) g]
  refine DFunLike.ext _ _ fun m => ?_
  show Δ_[1]^[m] (⇑(r • cfunSlash hp2 ω (mahlerON a) g)) 0
      = (r • mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g)) m
  rw [ContinuousMap.coe_smul, fwdDiff_iter_const_smul]
  rfl

/-! ### The integral space `S^D_int` ([LWX, §2.7]) -/

variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])

/-- The level monoid: preimage of `M₁` under `θ` ([LWX, §2.4]'s `K^p Iw_q` at the
split place, abstracted as in `QMF.levelMonoidOf`). -/
def levelM1 : Submonoid G := Submonoid.comap θ (M1 p)

/-- The corestriction `θ⁻¹(M₁) →* M₁` of the component map (the
`levelMonoidOfToS` pattern of `Weight/Forms.lean`, inlined to keep this file off
the weight tower). -/
def levelM1ToM1 : levelM1 (p := p) θ →* M1 p where
  toFun g := ⟨θ g.1, g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

set_option warn.classDefReducibility false in
/-- The value-side action of the level monoid on the sequence model: the
transported (2.3.2)-action pulled back along the component map (the
`RightSlashAction.comap` pattern of `Weight/SlashAction.lean`, inlined). -/
def seqLevelSlashAction (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    RightSlashAction (levelM1 (p := p) θ) (c(ℕ, HaloInt p)) where
  slash a u := RightSlashAction.slash (self := seqSlashAction hp2 ω) a
    (levelM1ToM1 (p := p) θ u)
  zero_slash u := (seqSlashAction hp2 ω).zero_slash _
  slash_one a := by rw [map_one, (seqSlashAction hp2 ω).slash_one]
  slash_mul a u₁ u₂ := by rw [map_mul, (seqSlashAction hp2 ω).slash_mul]
  add_slash a b u := (seqSlashAction hp2 ω).add_slash a b _

/-- The level action commutes with the `Λ^{>1/p}`-scalars (inherited from
`seqSMulSlash` along the pullback). -/
theorem seqLevelSMulSlash (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    @RightSlashAction.SMulSlashClass (HaloInt p) (levelM1 (p := p) θ)
      (c(ℕ, HaloInt p)) _ _ _ (seqLevelSlashAction (p := p) θ hp2 ω) := by
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  refine { smul_slash := ?_ }
  intro r a u
  exact (seqSMulSlash hp2 ω).smul_slash r a (levelM1ToM1 (p := p) θ u)

set_option warn.classDefReducibility false in
/-- The slash action of the level monoid on `c(ℕ, Λ^{>1/p})`-valued automorphic
functions: Buzzard's `(φ ∣ₛ u)(g) = φ(g·u⁻¹) ∣ₛ u` — the ring-generic
`AutomorphicFunction` instance of `Slash/AutomorphicFunction.lean` over the
value-side level action `seqLevelSlashAction`. -/
def intAutSlashAction (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    RightSlashAction (levelM1 (p := p) θ)
      (AutomorphicFunction G Γ (c(ℕ, HaloInt p))) :=
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  inferInstance

/-- **`S^D_int`** ([LWX, §2.7]): the `U`-fixed points of the integral automorphic
functions — `levelSubmoduleSlash` of the ring-generic layer, so [LWX, (2.11.1)] is
`bijective_evalAtRepsSlash` applied, not re-proved. -/
def IntForms (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ levelM1 (p := p) θ) :
    Submodule (HaloInt p) (AutomorphicFunction G Γ (c(ℕ, HaloInt p))) := by
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  haveI := seqLevelSMulSlash (p := p) θ hp2 ω
  exact AutomorphicFunction.levelSubmoduleSlash (HaloInt p) U hU

/-! ### H5 — the Hecke seam -/

/-- [LWX, Prop 3.4] read in the sequence model: the transported slash of a single
`g ∈ M₁` has the entry streams as its matrix, `(a ∣ₛ g)ₘ = ∑ₙ aₙ·P_{m,n}(g)` — the
coefficient form the Hecke assembly consumes. -/
theorem seqSlash_coeff (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (g : M1 p)
    (a : c(ℕ, HaloInt p)) (m : ℕ) :
    (RightSlashAction.slash (self := seqSlashAction hp2 ω) a g) m
      = ∑' n : ℕ, a n * entry ω (M1.toLocalMat g) m n := by
  show mahlerCoeffs (cfunSlash hp2 ω (mahlerON a) g) m = _
  rw [mahlerCoeffs_apply, fwdDiff_cfunSlash_mahlerON hp2 ω g a m]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation at class-set representatives, ring-level mirror of
`QMF.Weight.evalAtReps` (Weight/Compact.lean:92): `φ ↦ ⊕ᵢ φ(cᵢ)` into the block
model `c(ι × ℕ, Λ^{>1/p})` via `cSpace.blockIncl`. -/
def intEvalAtReps (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ levelM1 (p := p) θ) (c : ι → G) :
    IntForms (Γ := Γ) θ hp2 ω U hU →ₗ[HaloInt p] c(ι × ℕ, HaloInt p) where
  toFun φ := ∑ i : ι, cSpace.blockIncl i
    ((φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i))
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' r φ := by simp [Finset.smul_sum]

/-- The `i`-th block of `intEvalAtReps c φ` is the value `φ(c i)`. -/
theorem blockProj_intEvalAtReps (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ) (c : ι → G)
    (φ : IntForms (Γ := Γ) θ hp2 ω U hU) (i : ι) :
    cSpace.blockProj i (intEvalAtReps θ hp2 ω U hU c φ)
      = (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i) := by
  simp only [intEvalAtReps, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Coordinates of the evaluation: `(evalᵢₘ φ) = φ(cᵢ)ₘ`. -/
theorem intEvalAtReps_apply (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ) (c : ι → G)
    (φ : IntForms (Γ := Γ) θ hp2 ω U hU) (i : ι) (m : ℕ) :
    intEvalAtReps θ hp2 ω U hU c φ (i, m)
      = (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i) m :=
  DFunLike.congr_fun (blockProj_intEvalAtReps θ hp2 ω U hU c φ i) m

/-- **The seam ([LWX, Prop 3.1] in full)**: any linear `Φ` on `S^D_int` satisfying
the Prop 3.1 display at the representatives — `(Φφ)(cᵢ) = ∑ⱼ φ(c_{tgt i j}) ∣ₛ gᵢⱼ`
with `p`-components realising the `UpDatum` `D` — intertwines `intEvalAtReps` with
the integral matrix operator `D.op ω`.  The display hypothesis is discharged at
instantiation by `AbstractHeckeOperatorSlash.heckeOperatorSlash_apply_rep`
(ring-generic, already proved), so `charPowerSeries` of the genuine `[UηU]` is
`charPowerSeries (D.op ω)` and Theorem 3.16 / Corollary 3.18 apply to it. -/
theorem intEvalAtReps_comm (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ levelM1 (p := p) θ) (c : ι → G) (D : UpDatum p ι)
    (g : ι → Fin p → M1 p) (hg : ∀ i j, M1.toLocalMat (g i j) = D.mat i j)
    (Φ : IntForms (Γ := Γ) θ hp2 ω U hU →ₗ[HaloInt p]
      IntForms (Γ := Γ) θ hp2 ω U hU)
    (hΦ : ∀ (φ : IntForms (Γ := Γ) θ hp2 ω U hU) (i : ι),
      ((Φ φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p)))) (c i)
        = ∑ j : Fin p, RightSlashAction.slash (self := seqSlashAction hp2 ω)
            ((φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (D.tgt i j))) (g i j))
    (φ : IntForms (Γ := Γ) θ hp2 ω U hU) :
    intEvalAtReps θ hp2 ω U hU c (Φ φ) = D.op ω (intEvalAtReps θ hp2 ω U hU c φ) := by
  refine DFunLike.ext _ _ fun a => ?_
  obtain ⟨i, m⟩ := a
  have hsum0 : Summable fun b : ι × ℕ =>
      D.matrix ω (i, m) b * intEvalAtReps θ hp2 ω U hU c φ b := by
    refine TateFredholm.summable_of_tendsto_cofinite ?_
    refine squeeze_zero_norm
      (a := fun b => ‖intEvalAtReps θ hp2 ω U hU c φ b‖) (fun b => ?_) ?_
    · calc ‖D.matrix ω (i, m) b * intEvalAtReps θ hp2 ω U hU c φ b‖
          ≤ ‖D.matrix ω (i, m) b‖ * ‖intEvalAtReps θ hp2 ω U hU c φ b‖ :=
            norm_mul_le _ _
        _ ≤ 1 * ‖intEvalAtReps θ hp2 ω U hU c φ b‖ :=
            mul_le_mul_of_nonneg_right (HaloInt.norm_le_one _) (norm_nonneg _)
        _ = ‖intEvalAtReps θ hp2 ω U hU c φ b‖ := one_mul _
    · simpa using (cSpace.tendsto_cofinite (intEvalAtReps θ hp2 ω U hU c φ)).norm
  have hsummand : ∀ (i' : ι) (j : Fin p), Summable fun n : ℕ =>
      entry ω (D.mat i j) m n
        * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n := by
    intro i' j
    refine TateFredholm.summable_of_tendsto_cofinite ?_
    refine squeeze_zero_norm
      (a := fun n => ‖(φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n‖)
      (fun n => ?_) ?_
    · calc ‖entry ω (D.mat i j) m n
          * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n‖
          ≤ ‖entry ω (D.mat i j) m n‖
            * ‖(φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n‖ :=
            norm_mul_le _ _
        _ ≤ 1 * ‖(φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n‖ :=
            mul_le_mul_of_nonneg_right (HaloInt.norm_le_one _) (norm_nonneg _)
        _ = ‖(φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n‖ := one_mul _
    · simpa using
        (cSpace.tendsto_cofinite
          ((φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i'))).norm
  calc intEvalAtReps θ hp2 ω U hU c (Φ φ) (i, m)
      = (Φ φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i) m :=
        intEvalAtReps_apply θ hp2 ω U hU c (Φ φ) i m
    _ = (∑ j : Fin p, RightSlashAction.slash (self := seqSlashAction hp2 ω)
          ((φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (D.tgt i j)))
          (g i j)) m := by rw [hΦ φ i]
    _ = ∑ j : Fin p, (RightSlashAction.slash (self := seqSlashAction hp2 ω)
          ((φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (D.tgt i j)))
          (g i j)) m :=
        map_sum (cSpace.evalCLM (R := HaloInt p) m) _ Finset.univ
    _ = ∑ j : Fin p, ∑' n : ℕ,
          entry ω (D.mat i j) m n
            * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (D.tgt i j)) n := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [seqSlash_coeff hp2 ω (g i j) _ m, hg i j]
        exact tsum_congr fun n => mul_comm _ _
    _ = ∑ i' : ι, ∑ j ∈ Finset.univ.filter (fun j : Fin p => D.tgt i j = i'),
          ∑' n : ℕ, entry ω (D.mat i j) m n
            * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (D.tgt i j)) n :=
        (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (D.tgt i j))
          _).symm
    _ = ∑ i' : ι, ∑ j ∈ Finset.univ.filter (fun j : Fin p => D.tgt i j = i'),
          ∑' n : ℕ, entry ω (D.mat i j) m n
            * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n := by
        refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.mp hj).2]
    _ = ∑ i' : ι, ∑' n : ℕ,
          ∑ j ∈ Finset.univ.filter (fun j : Fin p => D.tgt i j = i'),
            entry ω (D.mat i j) m n
              * (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i') n := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        exact ((hasSum_finset_sum fun j _ => (hsummand i' j).hasSum).tsum_eq).symm
    _ = ∑ i' : ι, ∑' n : ℕ, D.matrix ω (i, m) (i', n)
          * intEvalAtReps θ hp2 ω U hU c φ (i', n) := by
        refine Finset.sum_congr rfl fun i' _ => tsum_congr fun n => ?_
        rw [intEvalAtReps_apply θ hp2 ω U hU c φ i' n,
          show D.matrix ω (i, m) (i', n)
            = ∑ j ∈ Finset.univ.filter (fun j : Fin p => D.tgt i j = i'),
                entry ω (D.mat i j) m n from rfl,
          Finset.sum_mul]
    _ = ∑' b : ι × ℕ, D.matrix ω (i, m) b * intEvalAtReps θ hp2 ω U hU c φ b := by
        rw [hsum0.tsum_prod, tsum_fintype]
    _ = D.op ω (intEvalAtReps θ hp2 ω U hU c φ) (i, m) :=
        (UpDatum.op_apply hp2 D ω _ (i, m)).symm

end LWX
