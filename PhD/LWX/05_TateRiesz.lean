/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«01_HaloTate»
import PhD.LWX.«04_Halo»
import PhD.TateFredholm.«12_RieszColeman»
import PhD.TateFredholm.«11_SlopeFactor»

/-!
# The halo `U_p` over the Tate ring `A`: Riesz theory at a vertex

Over `A = Λ^{>1/p}[1/T]` the integral `U_p`-matrix `P` of `03_UpMatrix.lean` is conjugated, as
in the proof of [LWX, Theorem 3.16] ("We now conjugate the matrix `P` by the infinite diagonal
matrix whose diagonal entries are `1, …, T, …, T², …`; let `P'` denote the matrix we get this
way … the entries of `P'` in the `n`-th column all lie in `T^{⌊n/t⌋−⌊n/pt⌋}Λ^{>1/p}`"), and
then **transposed**: the columns of `P'` decay uniformly, so the transpose `(P')ᵀ` has
uniformly decaying rows and is a compactoid operator on `c(ι × ℕ, A)` in the sense of
`TateFredholm.IsCompactoid` (the halo board's H4 note records that the rescaled basis is
not `c₀`-stable for the action itself, which is why the transpose is the honest compact
operator here).  Principal minors are invariant under transposition and diagonal
conjugation, so its Fredholm determinant is `Char(P)` ([LWX] (3.16.1)) read in `A⟦X⟧`.

At an index `n` where `c_n = T^{λ(n)}·(unit)` — the situation of [LWX, Remark 3.25] ("for
`n = n^±_k`, `c_n(T)` is equal to `T^{λ_n}` times a unit in `Λ^{>1/p}`"), *hypothesised* here
since it is derived in [LWX] from the touching argument of Theorem 1.3 — `Char(P)` factors as
`P_n·G` with `deg P_n = n` (`PowerSeries.exists_isDominantFactorization`), and [JN] Theorem
2.2.2 (`TateFredholm.exists_rieszColemanProjection`) gives the Riesz decomposition of
`c(ι × ℕ, A)` for the transposed `U_p`.

## Main definitions

* `LWX.UpDatum.tateMatrix`, `LWX.UpDatum.tateOp`: the `T`-rescaled transpose of the integral
  `U_p` and its matrix.
* `LWX.UpDatum.IsHaloVertex`: the vertex hypothesis of [LWX, Remark 3.25].

## Main results

* `LWX.UpDatum.isCompactoid_tateOp`: the rescaled transpose is compactoid over `A`.
* `LWX.UpDatum.minor_tateOp`, `LWX.UpDatum.charPowerSeries_tateOp`: `Char(P') = Char(P)`.
* `LWX.lwxLambda_exponent_le`, `LWX.lwxLambda_exponent_lt`: convexity of the halo polygon `λ`.
* `LWX.UpDatum.isDominantIndex_charPowerSeries_tateOp`,
  `LWX.UpDatum.isMultiplicative_charCoeff_tateOp`: at a vertex, `n` is the dominant index at
  radius `p^{λ(n)−λ(n−1)}` and the dominant coefficient is a multiplicative unit.
* `LWX.UpDatum.exists_isDominantFactorization_tateOp`,
  `LWX.UpDatum.exists_rieszColemanProjection_tateOp`: the factorisation and the Riesz–Coleman
  decomposition at a vertex.
* `LWX.HaloInt.isUnit_of_isUnit_coeff_zero`, `LWX.UpDatum.isHaloVertex_of_isUnit_coeff`: the
  bridge from [LWX, Cor 3.18]'s unit-coefficient criterion to `IsHaloVertex`.
-/

open Filter Topology Polynomial TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Vertex

/-- The increments `d_k = ⌊k/t⌋ − ⌊k/(pt)⌋` of `λ` are nondecreasing (`monotone_sub_div`
composed with `k ↦ ⌊k/t⌋`) — the convexity of the halo polygon. -/
theorem monotone_lwxLambda_increment (p t : ℕ) :
    Monotone fun k : ℕ => k / t - k / (p * t) := by
  intro a b hab
  show a / t - a / (p * t) ≤ b / t - b / (p * t)
  have h1 : a / (p * t) = a / t / p := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h2 : b / (p * t) = b / t / p := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [h1, h2]
  exact monotone_sub_div p (Nat.div_le_div_right hab)

omit hp in
/-- Below a vertex: `λ(n) − λ(m) ≤ (n − m)·d_{n−1}` (the increments up to `n − 1` are at most
`d_{n−1}`). -/
theorem lwxLambda_sub_le (p t : ℕ) {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    lwxLambda p t n ≤ lwxLambda p t m + (n - m) * ((n - 1) / t - (n - 1) / (p * t)) := by
  have hsplit : lwxLambda p t m + ∑ k ∈ Finset.Ico m n, (k / t - k / (p * t)) =
      lwxLambda p t n := by
    rw [lwxLambda, lwxLambda, ← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le m) hm
  have hle := Finset.sum_le_card_nsmul (Finset.Ico m n) (fun k => k / t - k / (p * t))
    ((n - 1) / t - (n - 1) / (p * t)) fun k hk => by
      have hk' : k ≤ n - 1 := by
        have := (Finset.mem_Ico.1 hk).2
        omega
      exact monotone_lwxLambda_increment p t hk'
  rw [Nat.card_Ico, smul_eq_mul] at hle
  omega

omit hp in
/-- Above a vertex: `λ(m) − λ(n) ≥ (m − n)·d_n` (the increments from `n` on are at least
`d_n`). -/
theorem le_lwxLambda_sub (p t : ℕ) {n m : ℕ} (hnm : n < m) :
    lwxLambda p t n + (m - n) * (n / t - n / (p * t)) ≤ lwxLambda p t m := by
  have hsplit : lwxLambda p t n + ∑ k ∈ Finset.Ico n m, (k / t - k / (p * t)) =
      lwxLambda p t m := by
    rw [lwxLambda, lwxLambda, ← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le n) hnm.le
  have hle := Finset.card_nsmul_le_sum (Finset.Ico n m) (fun k => k / t - k / (p * t))
    (n / t - n / (p * t)) fun k hk => monotone_lwxLambda_increment p t (Finset.mem_Ico.1 hk).1
  rw [Nat.card_Ico, smul_eq_mul] at hle
  omega

omit hp in
/-- The exponent inequality behind dominance: with the left slope `s = λ(n) − λ(n−1)`,
`−λ(m) + s·m ≤ −λ(n) + s·n` for every `m`. -/
theorem lwxLambda_exponent_le (p t : ℕ) {n : ℕ} (hn0 : 0 < n) (m : ℕ) :
    -(lwxLambda p t m : ℤ) + ((lwxLambda p t n : ℤ) - lwxLambda p t (n - 1)) * m ≤
      -(lwxLambda p t n : ℤ) + ((lwxLambda p t n : ℤ) - lwxLambda p t (n - 1)) * n := by
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = (n - 1) / t - (n - 1) / (p * t) := ⟨_, rfl⟩
  have hsucc : lwxLambda p t n = lwxLambda p t (n - 1) + sN := by
    rw [hsN]
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact lwxLambda_succ p t (n - 1)
  have hs : (lwxLambda p t n : ℤ) - lwxLambda p t (n - 1) = sN := by
    rw [hsucc]
    push_cast
    ring
  rw [hs]
  rcases le_or_gt m n with hm | hm
  · have h := lwxLambda_sub_le p t hn0 hm
    rw [← hsN] at h
    zify [hm] at h
    nlinarith [h]
  · obtain ⟨cN, hcN⟩ : ∃ cN, cN = n / t - n / (p * t) := ⟨_, rfl⟩
    have h := le_lwxLambda_sub p t hm
    rw [← hcN] at h
    have hd : sN ≤ cN := by
      rw [hsN, hcN]
      exact monotone_lwxLambda_increment p t (by omega)
    zify [hm.le] at h
    have hd' : (sN : ℤ) ≤ cN := mod_cast hd
    nlinarith [h, hd']

omit hp in
/-- Strict dominance above a vertex: if the increment strictly grows at `n`, then
`−λ(m) + s·m < −λ(n) + s·n` for `m > n`. -/
theorem lwxLambda_exponent_lt (p t : ℕ) {n m : ℕ} (hn0 : 0 < n)
    (hvert : (n - 1) / t - (n - 1) / (p * t) < n / t - n / (p * t)) (hnm : n < m) :
    -(lwxLambda p t m : ℤ) + ((lwxLambda p t n : ℤ) - lwxLambda p t (n - 1)) * m <
      -(lwxLambda p t n : ℤ) + ((lwxLambda p t n : ℤ) - lwxLambda p t (n - 1)) * n := by
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = (n - 1) / t - (n - 1) / (p * t) := ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ cN, cN = n / t - n / (p * t) := ⟨_, rfl⟩
  have hsucc : lwxLambda p t n = lwxLambda p t (n - 1) + sN := by
    rw [hsN]
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact lwxLambda_succ p t (n - 1)
  have hs : (lwxLambda p t n : ℤ) - lwxLambda p t (n - 1) = sN := by
    rw [hsucc]
    push_cast
    ring
  have h := le_lwxLambda_sub p t hnm
  rw [← hcN] at h
  have hlt : sN < cN := by rw [hsN, hcN]; exact hvert
  zify [hnm.le] at h
  have hlt' : (sN : ℤ) + 1 ≤ cN := mod_cast hlt
  have hmn : (1 : ℤ) ≤ (m : ℤ) - n := by
    have : (n : ℤ) < m := mod_cast hnm
    omega
  rw [hs]
  nlinarith [h, hlt', hmn]

end Vertex

namespace UpDatum

section TateOp

variable (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- The matrix of the `T`-rescaled transpose: `T^{m − n}` times the transposed integral
entry ([LWX, proof of Thm 3.16]: `P' = D⁻¹ P D` with `D = diag(T^{n})`, then transposed). -/
def tateMatrix (a b : ι × ℕ) : HaloTate p :=
  ((HaloTate.T ^ ((a.2 : ℤ) - b.2) : (HaloTate p)ˣ) : HaloTate p) *
    HaloTate.ofInt (D.matrix ω b a)

omit [Fintype ι] in
/-- **Row decay of the rescaled transpose** ([LWX, proof of Thm 3.16]: "the entries of `P'` in
the `n`-th column all lie in `T^{⌊n/t⌋−⌊n/pt⌋}Λ^{>1/p}`"): the row `a` is bounded by
`p^{−(m − ⌊m/p⌋)}`, uniformly in the column. -/
theorem norm_tateMatrix_le (hp2 : p ≠ 2) (a b : ι × ℕ) :
    ‖tateMatrix D ω a b‖ ≤ (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hT : ‖((HaloTate.T ^ ((a.2 : ℤ) - b.2) : (HaloTate p)ˣ) : HaloTate p)‖ =
      (p : ℝ) ^ (-((a.2 : ℤ) - b.2)) := HaloTate.norm_T_zpow _
  calc ‖tateMatrix D ω a b‖
      ≤ ‖((HaloTate.T ^ ((a.2 : ℤ) - b.2) : (HaloTate p)ˣ) : HaloTate p)‖ *
        ‖HaloTate.ofInt (D.matrix ω b a)‖ := norm_mul_le _ _
    _ ≤ (p : ℝ) ^ (-((a.2 : ℤ) - b.2)) * (p : ℝ) ^ (-((b.2 - a.2 / p : ℕ) : ℤ)) := by
        rw [hT, HaloTate.norm_ofInt]
        exact mul_le_mul_of_nonneg_left (D.norm_matrix_le hp2 ω b a) (by positivity)
    _ = (p : ℝ) ^ (-((a.2 : ℤ) - b.2) + -((b.2 - a.2 / p : ℕ) : ℤ)) :=
        (zpow_add₀ (by positivity) _ _).symm
    _ ≤ (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) := by
        refine zpow_le_zpow_right₀ hp1.le ?_
        have hdiv : a.2 / p ≤ a.2 := Nat.div_le_self _ _
        rcases le_or_gt b.2 (a.2 / p) with hb | hb
        · rw [Nat.sub_eq_zero_of_le hb]
          push_cast
          omega
        · have : ((b.2 - a.2 / p : ℕ) : ℤ) = (b.2 : ℤ) - a.2 / p := by
            push_cast [Nat.cast_sub hb.le]
            ring
          rw [this]
          push_cast [Nat.cast_sub hdiv]
          ring_nf
          omega

omit [Fintype ι] in
private theorem norm_tateMatrix_le_one (hp2 : p ≠ 2) (a b : ι × ℕ) :
    ‖tateMatrix D ω a b‖ ≤ 1 := by
  refine (norm_tateMatrix_le D ω hp2 a b).trans ?_
  refine zpow_le_one_of_nonpos₀ ?_ (neg_nonpos.2 (Int.natCast_nonneg _))
  exact_mod_cast hp.out.one_le

private theorem tendsto_tateRow_mul (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloTate p)) (a : ι × ℕ) :
    Tendsto (fun b => tateMatrix D ω a b * φ b) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (a := fun b => ‖φ b‖) (fun b => ?_) ?_
  · calc ‖tateMatrix D ω a b * φ b‖ ≤ ‖tateMatrix D ω a b‖ * ‖φ b‖ := norm_mul_le _ _
      _ ≤ 1 * ‖φ b‖ := mul_le_mul_of_nonneg_right (norm_tateMatrix_le_one D ω hp2 a b)
          (norm_nonneg _)
      _ = ‖φ b‖ := one_mul _
  · simpa using (cSpace.tendsto_cofinite φ).norm

private theorem norm_tsum_tateRow_le (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloTate p)) (a : ι × ℕ) :
    ‖∑' b, tateMatrix D ω a b * φ b‖ ≤ (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) * ‖φ‖ := by
  refine (norm_tsum_le_iSup (tendsto_tateRow_mul D ω hp2 φ a)).trans
    (Real.iSup_le (fun b => ?_) (by positivity))
  calc ‖tateMatrix D ω a b * φ b‖ ≤ ‖tateMatrix D ω a b‖ * ‖φ b‖ := norm_mul_le _ _
    _ ≤ (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) * ‖φ‖ :=
        mul_le_mul (norm_tateMatrix_le D ω hp2 a b) (cSpace.norm_apply_le φ b) (norm_nonneg _)
          (by positivity)

private theorem tendsto_tsum_tateRow (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloTate p)) :
    Tendsto (fun a => ∑' b, tateMatrix D ω a b * φ b) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (a := fun a : ι × ℕ =>
    (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) * ‖φ‖) (norm_tsum_tateRow_le D ω hp2 φ) ?_
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have h0 : Tendsto (fun a : ι × ℕ => (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ))) cofinite (𝓝 0) := by
    have hcomp : Tendsto (fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
      simpa [zpow_neg, zpow_natCast, ← inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (inv_lt_one_of_one_lt₀ hp1)
    exact hcomp.comp tendsto_weight_cofinite_atTop
  simpa using h0.mul_const ‖φ‖

private def tateOpLinear (hp2 : p ≠ 2) :
    c(ι × ℕ, HaloTate p) →ₗ[HaloTate p] c(ι × ℕ, HaloTate p) where
  toFun φ := ⟨⟨fun a : Ix (ι × ℕ) => ∑' b, tateMatrix D ω a b * φ b,
    continuous_of_discreteTopology⟩, by
      rw [Filter.cocompact_eq_cofinite]
      exact tendsto_tsum_tateRow D ω hp2 φ⟩
  map_add' φ ψ := by
    refine DFunLike.ext _ _ fun a => ?_
    show (∑' b, tateMatrix D ω a b * (φ + ψ) b)
        = (∑' b, tateMatrix D ω a b * φ b) + ∑' b, tateMatrix D ω a b * ψ b
    rw [← ((TateFredholm.summable_of_tendsto_cofinite
        (tendsto_tateRow_mul D ω hp2 φ a)).hasSum.add
      (TateFredholm.summable_of_tendsto_cofinite
        (tendsto_tateRow_mul D ω hp2 ψ a)).hasSum).tsum_eq]
    exact tsum_congr fun b => mul_add (tateMatrix D ω a b) (φ b) (ψ b)
  map_smul' r φ := by
    refine DFunLike.ext _ _ fun a => ?_
    show (∑' b, tateMatrix D ω a b * (r • φ) b) = r * ∑' b, tateMatrix D ω a b * φ b
    rw [← Summable.tsum_mul_left r
      (TateFredholm.summable_of_tendsto_cofinite (tendsto_tateRow_mul D ω hp2 φ a))]
    exact tsum_congr fun b => mul_left_comm (tateMatrix D ω a b) r (φ b)

/-- **The `T`-rescaled transpose of the integral `U_p` over `A`**: the operator on
`c(ι × ℕ, A)` with matrix entry `T^{m−n}·M_{(j,n),(i,m)}` at row `(i, m)`, column `(j, n)`
([LWX, proof of Thm 3.16]: `P' = D⁻¹ P D`, then transposed).  Its rows decay uniformly, so it
is compactoid; at `p = 2` (where the halo bound is unavailable) it is junk `0`, as for
`UpDatum.op`. -/
def tateOp : c(ι × ℕ, HaloTate p) →L[HaloTate p] c(ι × ℕ, HaloTate p) :=
  if hp2 : p ≠ 2 then
    LinearMap.mkContinuous (tateOpLinear D ω hp2) 1 fun φ => by
      rw [one_mul, cSpace.norm_eq_iSup]
      refine Real.iSup_le (fun a => ?_) (norm_nonneg _)
      refine (norm_tsum_tateRow_le D ω hp2 φ a).trans ?_
      refine mul_le_of_le_one_left (norm_nonneg _)
        (zpow_le_one_of_nonpos₀ ?_ (neg_nonpos.2 (Int.natCast_nonneg _)))
      exact_mod_cast hp.out.one_le
  else 0

/-- The rows of the rescaled transpose, at odd `p`. -/
theorem tateOp_apply (hp2 : p ≠ 2) (φ : c(ι × ℕ, HaloTate p)) (a : ι × ℕ) :
    D.tateOp ω φ a = ∑' b, tateMatrix D ω a b * φ b := by
  rw [tateOp, dif_pos hp2]
  rfl

/-- The matrix of `tateOp`: `T^{m − n}` times the transposed integral entry. -/
theorem matrixCoeff_tateOp (hp2 : p ≠ 2) (a b : ι × ℕ) :
    matrixCoeff (D.tateOp ω) a b =
      ((HaloTate.T ^ ((a.2 : ℤ) - b.2) : (HaloTate p)ˣ) : HaloTate p) *
        HaloTate.ofInt (D.matrix ω b a) := by
  show D.tateOp ω (cSpace.single b 1) a = _
  rw [tateOp_apply D ω hp2,
    tsum_eq_single b fun b' hb' => by rw [cSpace.single_apply_of_ne hb', mul_zero],
    cSpace.single_apply_self, mul_one]
  rfl

/-- **Row decay** ([LWX, proof of Thm 3.16]), on the operator: the row `(i, m)` of the
transpose is bounded by `p^{−(m − ⌊m/p⌋)}`. -/
theorem norm_matrixCoeff_tateOp_le (hp2 : p ≠ 2) (a b : ι × ℕ) :
    ‖matrixCoeff (D.tateOp ω) a b‖ ≤ (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ)) := by
  rw [matrixCoeff_tateOp D ω hp2 a b]
  exact norm_tateMatrix_le D ω hp2 a b

/-- The transposed rescaled `U_p` is compactoid over `A` (its row norms decay). -/
theorem isCompactoid_tateOp (hp2 : p ≠ 2) : IsCompactoid (D.tateOp ω) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  refine squeeze_zero (fun a => rowNorm_nonneg _ a) (fun a => ?_)
    (g := fun a : ι × ℕ => (p : ℝ) ^ (-((a.2 - a.2 / p : ℕ) : ℤ))) ?_
  · exact Real.iSup_le (fun b => norm_matrixCoeff_tateOp_le D ω hp2 a b) (by positivity)
  · have hcomp : Tendsto (fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
      simpa [zpow_neg, zpow_natCast, ← inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
    exact hcomp.comp tendsto_weight_cofinite_atTop

end TateOp

section Char

variable (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- Principal minors are unchanged by transposition and diagonal conjugation
(`Matrix.det_transpose`; the factors `T^{n_a}`, `T^{−m_a}` over `a ∈ S` cancel). -/
theorem minor_tateOp (hp2 : p ≠ 2) (S : Finset (ι × ℕ)) :
    minor (D.tateOp ω) S = HaloTate.ofInt (minor (D.op ω) S) := by
  classical
  have hfact : (Matrix.of fun a b : S => matrixCoeff (D.tateOp ω) a b) =
      Matrix.diagonal
          (fun a : S => ((HaloTate.T ^ ((a : ι × ℕ).2 : ℤ) : (HaloTate p)ˣ) : HaloTate p)) *
        (Matrix.of fun a b : S => HaloTate.ofInt (D.matrix ω b a)) *
        Matrix.diagonal
          (fun b : S => ((HaloTate.T ^ (-((b : ι × ℕ).2 : ℤ)) : (HaloTate p)ˣ) : HaloTate p)) := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
      Matrix.of_apply, matrixCoeff_tateOp D ω hp2,
      show ((HaloTate.T ^ (((a : ι × ℕ).2 : ℤ) - (b : ι × ℕ).2) : (HaloTate p)ˣ) : HaloTate p) =
        ((HaloTate.T ^ ((a : ι × ℕ).2 : ℤ) : (HaloTate p)ˣ) : HaloTate p) *
          ((HaloTate.T ^ (-((b : ι × ℕ).2 : ℤ)) : (HaloTate p)ˣ) : HaloTate p) from by
        rw [← Units.val_mul, ← zpow_add, sub_eq_add_neg]]
    ring
  have hprod : (∏ a : S, ((HaloTate.T ^ ((a : ι × ℕ).2 : ℤ) : (HaloTate p)ˣ) : HaloTate p)) *
      ∏ a : S, ((HaloTate.T ^ (-((a : ι × ℕ).2 : ℤ)) : (HaloTate p)ˣ) : HaloTate p) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  have hNdet : (Matrix.of fun a b : S => HaloTate.ofInt (D.matrix ω b a)).det =
      HaloTate.ofInt (minor (D.op ω) S) := by
    rw [show (Matrix.of fun a b : S => HaloTate.ofInt (D.matrix ω b a)) =
        Matrix.transpose (Matrix.of fun a b : S => HaloTate.ofInt (D.matrix ω a b)) from rfl,
      Matrix.det_transpose, minor,
      show (Matrix.of fun a b : S => HaloTate.ofInt (D.matrix ω a b)) =
        (Matrix.of fun a b : S => matrixCoeff (D.op ω) a b).map HaloTate.ofIntRingHom from
        Matrix.ext fun a b => by
          rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, HaloTate.ofIntRingHom_apply,
            D.matrixCoeff_op hp2 ω],
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, HaloTate.ofIntRingHom_apply]
  rw [minor, hfact, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    hNdet]
  calc (∏ a : S, ((HaloTate.T ^ ((a : ι × ℕ).2 : ℤ) : (HaloTate p)ˣ) : HaloTate p)) *
        HaloTate.ofInt (minor (D.op ω) S) *
        ∏ a : S, ((HaloTate.T ^ (-((a : ι × ℕ).2 : ℤ)) : (HaloTate p)ˣ) : HaloTate p)
      = ((∏ a : S, ((HaloTate.T ^ ((a : ι × ℕ).2 : ℤ) : (HaloTate p)ˣ) : HaloTate p)) *
        ∏ a : S, ((HaloTate.T ^ (-((a : ι × ℕ).2 : ℤ)) : (HaloTate p)ˣ) : HaloTate p)) *
        HaloTate.ofInt (minor (D.op ω) S) := by ring
    _ = HaloTate.ofInt (minor (D.op ω) S) := by rw [hprod, one_mul]

omit [DecidableEq ι] in
private theorem continuous_ofInt :
    Continuous (HaloTate.ofIntRingHom : HaloInt p →+* HaloTate p) :=
  (AddMonoidHomClass.isometry_of_norm (HaloTate.ofIntRingHom : HaloInt p →+* HaloTate p)
    (fun x => HaloTate.norm_ofInt x)).continuous

/-- **`Char(P') = Char(P)`** ([LWX, proof of Thm 3.16]: "So `Char(P) = Char(P')`"): the
Fredholm determinant of the transposed rescaled `U_p` over `A` is the halo characteristic
series read in `A⟦X⟧` (summability from `summable_minor_upOp`, `ofInt` continuous). -/
theorem charPowerSeries_tateOp (hp2 : p ≠ 2) :
    charPowerSeries (D.tateOp ω) =
      PowerSeries.map HaloTate.ofIntRingHom (charPowerSeries (D.op ω)) := by
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, PowerSeries.coeff_map, charPowerSeries_coeff, charCoeff, charCoeff,
    map_mul, map_pow, map_neg, map_one]
  congr 1
  have hsum := ((summable_minor_upOp hp2 D ω n).hasSum.map
    (HaloTate.ofIntRingHom : HaloInt p →+* HaloTate p) continuous_ofInt).tsum_eq
  rw [← hsum]
  exact tsum_congr fun S => minor_tateOp D ω hp2 (S : Finset (ι × ℕ))

/-- The coefficients of the Fredholm determinant over `A` are the halo ones. -/
theorem charCoeff_tateOp (hp2 : p ≠ 2) (n : ℕ) :
    charCoeff (D.tateOp ω) n = HaloTate.ofInt (charCoeff (D.op ω) n) := by
  have h := congrArg (PowerSeries.coeff n) (charPowerSeries_tateOp D ω hp2)
  rwa [charPowerSeries_coeff, PowerSeries.coeff_map, charPowerSeries_coeff] at h

end Char

/-- **The vertex hypothesis** ([LWX, Remark 3.25]: "`c_n(T)` is equal to `T^{λ_n}` times a unit
in `Λ^{>1/p}`", at an index where the halo polygon `λ` has a genuine vertex,
`λ(n) − λ(n−1) < λ(n+1) − λ(n)`).  In [LWX] this is *derived* for `n = n^±_k` from the touching
argument of Theorem 1.3 (classicality + Atkin–Lehner), which is out of scope here. -/
def IsHaloVertex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) : Prop :=
  (∃ e : (HaloInt p)ˣ, ‖(e : HaloInt p)‖ = 1 ∧
      charCoeff (D.op ω) n = HaloInt.T ^ lwxLambda p (Fintype.card ι) n * (e : HaloInt p)) ∧
    (n - 1) / Fintype.card ι - (n - 1) / (p * Fintype.card ι) <
      n / Fintype.card ι - n / (p * Fintype.card ι)

section VertexOp

variable (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- At a vertex the halo coefficient is `T^{λ(n)}` times a unit of norm `1`, read over `A`. -/
theorem exists_charCoeff_tateOp_eq (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    ∃ e : (HaloInt p)ˣ, ‖(e : HaloInt p)‖ = 1 ∧
      charCoeff (D.tateOp ω) n =
        ((HaloTate.T : (HaloTate p)ˣ) : HaloTate p) ^ lwxLambda p (Fintype.card ι) n *
          HaloTate.ofInt (e : HaloInt p) := by
  obtain ⟨⟨e, he, hce⟩, -⟩ := hn
  refine ⟨e, he, ?_⟩
  rw [charCoeff_tateOp D ω hp2, hce, ← HaloTate.ofIntRingHom_apply, map_mul, map_pow,
    HaloTate.ofIntRingHom_apply, HaloTate.ofIntRingHom_apply, HaloTate.coe_T]

private theorem norm_charCoeff_tateOp_eq (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    ‖charCoeff (D.tateOp ω) n‖ = (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) n : ℤ)) := by
  obtain ⟨e, he, hc⟩ := exists_charCoeff_tateOp_eq D ω hp2 hn
  rw [hc, ← Units.val_pow_eq_pow_val, ← zpow_natCast, HaloTate.norm_T_zpow_mul,
    HaloTate.norm_ofInt, he, mul_one]

private theorem norm_charCoeff_tateOp_le (hp2 : p ≠ 2) (m : ℕ) :
    ‖charCoeff (D.tateOp ω) m‖ ≤ (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) m : ℤ)) := by
  rw [charCoeff_tateOp D ω hp2, HaloTate.norm_ofInt]
  exact norm_charCoeff_upOp_le hp2 D ω m

/-- At a vertex, `n` is the dominant index of `Char(P)` over `A` at the radius `ρ = p^{s}`,
`s = λ(n) − λ(n−1)` the left slope: the halo bound `‖c_m‖ ≤ p^{−λ(m)}` ([LWX, Thm 3.16]) and
convexity of `λ` (`lwxLambda_succ`, `monotone_sub_div`) give `‖c_m‖ρ^m ≤ ‖c_n‖ρ^n`, strictly for
`m > n`. -/
theorem isDominantIndex_charPowerSeries_tateOp (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    PowerSeries.IsDominantIndex
      ((p : ℝ) ^ ((lwxLambda p (Fintype.card ι) n : ℤ) - lwxLambda p (Fintype.card ι) (n - 1)))
      (charPowerSeries (D.tateOp ω)) n := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h2 := hn.2
      rw [Nat.zero_sub] at h2
      exact absurd h2 (lt_irrefl _)
    · exact h
  obtain ⟨sZ, hsZ⟩ : ∃ sZ : ℤ, sZ = (lwxLambda p (Fintype.card ι) n : ℤ) -
    lwxLambda p (Fintype.card ι) (n - 1) := ⟨_, rfl⟩
  have hpow : ∀ m : ℕ, ((p : ℝ) ^ sZ) ^ m = (p : ℝ) ^ (sZ * m) := fun m => by
    rw [← zpow_natCast ((p : ℝ) ^ sZ) m, ← zpow_mul]
  have hle : ∀ m : ℕ, ‖PowerSeries.coeff m (charPowerSeries (D.tateOp ω))‖ *
      ((p : ℝ) ^ sZ) ^ m ≤ (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) m : ℤ) + sZ * m) := by
    intro m
    rw [charPowerSeries_coeff, hpow, zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
    exact mul_le_mul_of_nonneg_right (norm_charCoeff_tateOp_le D ω hp2 m) (by positivity)
  have heq : ‖PowerSeries.coeff n (charPowerSeries (D.tateOp ω))‖ * ((p : ℝ) ^ sZ) ^ n =
      (p : ℝ) ^ (-(lwxLambda p (Fintype.card ι) n : ℤ) + sZ * n) := by
    rw [charPowerSeries_coeff, norm_charCoeff_tateOp_eq D ω hp2 hn, hpow,
      zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
  rw [← hsZ]
  refine ⟨fun m => ?_, fun m hm => ?_⟩
  · refine (hle m).trans (heq ▸ ?_)
    exact zpow_le_zpow_right₀ hp1.le (hsZ ▸ lwxLambda_exponent_le p (Fintype.card ι) hn0 m)
  · refine (hle m).trans_lt (heq ▸ ?_)
    exact zpow_lt_zpow_right₀ hp1
      (hsZ ▸ lwxLambda_exponent_lt p (Fintype.card ι) hn0 hn.2 hm)

/-- At a vertex the dominant coefficient `T^{λ(n)}·e` is a multiplicative unit of `A`. -/
theorem isMultiplicative_charCoeff_tateOp (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    IsUnit (charCoeff (D.tateOp ω) n) ∧
      TateFredholm.IsMultiplicative (charCoeff (D.tateOp ω) n) := by
  obtain ⟨e, he, hc⟩ := exists_charCoeff_tateOp_eq D ω hp2 hn
  rw [hc]
  refine ⟨(Units.isUnit ((HaloTate.T : (HaloTate p)ˣ) ^ lwxLambda p (Fintype.card ι) n)).mul
    (e.isUnit.map HaloTate.ofIntRingHom), ?_⟩
  exact (HaloTate.isMultiplicative_T.pow _).mul (HaloTate.isMultiplicative_ofInt_of_isUnit e he)

end VertexOp

section Riesz

variable (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **[LWX, Remark 3.25], one vertex** ("a standard factorization argument shows … that we can
factor `Char(P)`"): at a vertex `n`, `Char(P) = P_n·G` over `A` with `P_n` a dominant
polynomial of degree `n` and `G` of dominant index `0`. -/
theorem exists_isDominantFactorization_tateOp (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    ∃ (P : (HaloTate p)[X]) (G : PowerSeries (HaloTate p)),
      PowerSeries.IsDominantFactorization
        ((p : ℝ) ^ ((lwxLambda p (Fintype.card ι) n : ℤ) - lwxLambda p (Fintype.card ι) (n - 1)))
        n (charPowerSeries (D.tateOp ω)) P G := by
  have hp0 : (0 : ℝ) < p := mod_cast hp.out.pos
  obtain ⟨hunit, hmul⟩ := isMultiplicative_charCoeff_tateOp D ω hp2 hn
  rw [← charPowerSeries_coeff] at hunit hmul
  refine PowerSeries.exists_isDominantFactorization (by positivity)
    (fun c hc => charPowerSeries_isEntire _ (isCompactoid_tateOp D ω hp2) c hc) ?_
    (isDominantIndex_charPowerSeries_tateOp D ω hp2 hn) hunit hmul
  rw [charPowerSeries_coeff, charCoeff_zero]

/-- **[JN] Theorem 2.2.2 for the halo `U_p` at a vertex**: the Riesz–Coleman projector of the
transposed rescaled `U_p` over `A` for the factorisation `Char(P) = P_n·G`, so that
`Ker P_n*(U)` is finitely generated projective of rank `n` with `U`-stable closed complement on
which `P_n*(U)` is invertible. -/
theorem exists_rieszColemanProjection_tateOp (hp2 : p ≠ 2) {n : ℕ} (hn : IsHaloVertex D ω n) :
    ∃ (P : (HaloTate p)[X]) (G : PowerSeries (HaloTate p)) (v : (HaloTate p)ˣ)
      (q w : c(ι × ℕ, HaloTate p) →L[HaloTate p] c(ι × ℕ, HaloTate p)),
      P.natDegree = n ∧ IsRieszColemanProjection (D.tateOp ω) q w P G v := by
  have hp0 : (0 : ℝ) < p := mod_cast hp.out.pos
  obtain ⟨P, G, hPG⟩ := exists_isDominantFactorization_tateOp D ω hp2 hn
  obtain ⟨v, hv⟩ := hPG.dominant.2
  have hcop := hPG.isEntireCoprime (by positivity)
  obtain ⟨q, w, hidem, hcomm, hcomm_w, hcomm_pw, hnil, hinv⟩ :=
    exists_rieszColemanProjection (u := D.tateOp ω) (isCompactoid_tateOp D ω hp2)
      hPG.coeff_zero hv hPG.entire hPG.coeff_zero_G hPG.eq hcop
  exact ⟨P, G, v, q, w, hPG.natDegree,
    ⟨isCompactoid_tateOp D ω hp2, hPG.coeff_zero, hv, hPG.entire, hPG.coeff_zero_G, hPG.eq, hcop,
      hidem, hcomm, hcomm_w, hcomm_pw, hnil, hinv⟩⟩

end Riesz

end UpDatum

section HaloUnits

variable {x : HaloInt p}

omit [Fintype ι] [DecidableEq ι] in
-- `‖x_m‖ ≤ √(p^{m−1})` for a halo element with vanishing constant coefficient: the two halo
-- bounds `‖x_m‖ ≤ 1` (m ≥ 1) and `‖x_m‖ ≤ p^m` (m ≤ −1) both give it.
private theorem norm_coeff_le_sqrt (hx : x 0 = 0) (m : ℤ) :
    ‖x m‖ ≤ Real.sqrt ((p : ℝ) ^ (m - 1)) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hb := x.bound m
    rw [min_eq_right hm.le] at hb
    refine (Real.le_sqrt (norm_nonneg _) (zpow_nonneg hp0.le _)).2 ?_
    calc ‖x m‖ ^ 2 ≤ ((p : ℝ) ^ m) ^ 2 := by
          rw [sq, sq]
          exact mul_le_mul hb hb (norm_nonneg _) (zpow_nonneg hp0.le _)
      _ = (p : ℝ) ^ (2 * m) := by
          rw [← zpow_natCast ((p : ℝ) ^ m) 2, ← zpow_mul, mul_comm]
          norm_cast
      _ ≤ (p : ℝ) ^ (m - 1) := zpow_le_zpow_right₀ hp1.le (by omega)
  · rw [hx, norm_zero]
    exact Real.sqrt_nonneg _
  · have hb := x.bound m
    rw [min_eq_left hm.le, zpow_zero] at hb
    refine hb.trans ?_
    rw [← Real.sqrt_one]
    refine Real.sqrt_le_sqrt ?_
    exact one_le_zpow₀ hp1.le (by omega)

omit [Fintype ι] [DecidableEq ι] in
-- The `k`-th power of a halo element with vanishing constant coefficient decays as
-- `‖(x^k)_j‖ ≤ √(p^{j−k})`: in a monomial `T^{j_1}⋯T^{j_k}` contributing to the index `j`,
-- the negative indices contribute `p`-adic valuation and the total is at least `(k − j)/2`.
private theorem norm_coeff_pow_le_sqrt (hx : x 0 = 0) (k : ℕ) (j : ℤ) :
    ‖(x ^ k) j‖ ≤ Real.sqrt ((p : ℝ) ^ (j - k)) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  induction k generalizing j with
  | zero =>
    rw [pow_zero, HaloInt.coeff_one]
    rcases eq_or_ne j 0 with rfl | hj
    · rw [if_pos rfl, norm_one, Nat.cast_zero, sub_zero, zpow_zero, Real.sqrt_one]
    · rw [if_neg hj, norm_zero]
      exact Real.sqrt_nonneg _
  | succ k ih =>
    rw [pow_succ, HaloInt.coeff_mul]
    refine (norm_tsum_le_iSup (HaloInt.tendsto_mul_coeff_cofinite _ _ j)).trans
      (Real.iSup_le (fun i => ?_) (Real.sqrt_nonneg _))
    calc ‖(x ^ k) i * x (j - i)‖ ≤ ‖(x ^ k) i‖ * ‖x (j - i)‖ := norm_mul_le _ _
      _ ≤ Real.sqrt ((p : ℝ) ^ (i - k)) * Real.sqrt ((p : ℝ) ^ (j - i - 1)) :=
          mul_le_mul (ih i) (norm_coeff_le_sqrt hx _) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((p : ℝ) ^ (j - (k + 1 : ℕ))) := by
          rw [← Real.sqrt_mul (zpow_nonneg hp0.le _), ← zpow_add₀ hp0.ne']
          congr 2
          push_cast
          ring

omit [Fintype ι] [DecidableEq ι] in
private theorem tendsto_norm_coeff_pow (hx : x 0 = 0) (j : ℤ) :
    Tendsto (fun k : ℕ => ‖(x ^ k) j‖) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => norm_coeff_pow_le_sqrt hx k j) ?_
  have h0 : Tendsto (fun k : ℕ => (p : ℝ) ^ (j - k)) atTop (𝓝 0) := by
    have hc : Tendsto (fun k : ℕ => (p : ℝ) ^ j * ((p : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hp1)).const_mul ((p : ℝ) ^ j)
    refine hc.congr fun k => ?_
    rw [← zpow_natCast ((p : ℝ)⁻¹) k, ← zpow_neg_one, ← zpow_mul, ← zpow_add₀ hp0.ne']
    congr 1
    ring
  have := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at this
  exact this

omit [Fintype ι] [DecidableEq ι] in
private theorem summable_coeff_pow (hx : x 0 = 0) (j : ℤ) :
    Summable fun k : ℕ => (x ^ k) j := by
  refine TateFredholm.summable_of_tendsto_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_coeff_pow hx j)

/-- The geometric series `∑ₖ xᵏ` of a halo element with vanishing constant coefficient,
summed coefficientwise `p`-adically ([LWX, Lemma 3.15]). -/
private def geomInv (hx : x 0 = 0) : HaloInt p :=
  ⟨fun j => ∑' k : ℕ, (x ^ k) j, fun j => by
    refine (norm_tsum_le_iSup ?_).trans (Real.iSup_le (fun k => (x ^ k).bound j) ?_)
    · rw [Nat.cofinite_eq_atTop]
      exact tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_coeff_pow hx j)
    · have hp0 : (0 : ℝ) < p := mod_cast hp.out.pos
      positivity⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem coeff_sum_range (K : ℕ) (m : ℤ) :
    (∑ k ∈ Finset.range K, x ^ k) m = ∑ k ∈ Finset.range K, (x ^ k) m := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, HaloInt.coeff_add, ih, Finset.sum_range_succ]

omit [Fintype ι] [DecidableEq ι] in
-- The tail of the geometric series is uniformly small: `‖(y − S_K)_m‖ ≤ √(p^{m−K−1})`.
private theorem norm_geomInv_sub_sum_le (hx : x 0 = 0) (K : ℕ) (m : ℤ) :
    ‖geomInv hx m - (∑ k ∈ Finset.range (K + 1), x ^ k) m‖ ≤
      Real.sqrt ((p : ℝ) ^ (m - (K + 1))) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have htail := (summable_coeff_pow hx m).sum_add_tsum_nat_add (K + 1)
  have hval : geomInv hx m = ∑' k : ℕ, (x ^ k) m := rfl
  rw [coeff_sum_range, hval, ← htail, add_sub_cancel_left]
  refine (norm_tsum_le_iSup ?_).trans (Real.iSup_le (fun k => ?_) (Real.sqrt_nonneg _))
  · rw [Nat.cofinite_eq_atTop]
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    exact (tendsto_norm_coeff_pow hx m).comp (Filter.tendsto_add_atTop_nat (K + 1))
  · refine (norm_coeff_pow_le_sqrt hx (k + (K + 1)) m).trans (Real.sqrt_le_sqrt ?_)
    refine zpow_le_zpow_right₀ hp1.le ?_
    push_cast
    omega

omit [Fintype ι] [DecidableEq ι] in
-- `√(p^{j−K}) → 0`.
private theorem tendsto_sqrt_zpow_sub (j : ℤ) :
    Tendsto (fun K : ℕ => Real.sqrt ((p : ℝ) ^ (j - (K : ℤ)))) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hc : Tendsto (fun K : ℕ => (p : ℝ) ^ (j - (K : ℤ))) atTop (𝓝 0) := by
    have hmul := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hp1)).const_mul ((p : ℝ) ^ j)
    rw [mul_zero] at hmul
    refine hmul.congr fun K => ?_
    rw [← zpow_natCast ((p : ℝ)⁻¹) K, ← zpow_neg_one, ← zpow_mul, ← zpow_add₀ hp0.ne']
    ring_nf
  have h := (Real.continuous_sqrt.tendsto 0).comp hc
  rw [Real.sqrt_zero] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
-- The convolution of `1 − x` with the tail of the geometric series is uniformly small.
private theorem norm_mul_geomInv_sub_sum_le (hx : x 0 = 0) (K : ℕ) (j : ℤ) :
    ‖((1 - x) * (geomInv hx - ∑ k ∈ Finset.range (K + 1), x ^ k)) j‖ ≤
      Real.sqrt ((p : ℝ) ^ (j - (K + 1))) := by
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  rw [HaloInt.coeff_mul]
  refine (norm_tsum_le_iSup (HaloInt.tendsto_mul_coeff_cofinite _ _ j)).trans
    (Real.iSup_le (fun i => ?_) (Real.sqrt_nonneg _))
  have hi := (1 - x : HaloInt p).bound i
  calc ‖(1 - x : HaloInt p) i * (geomInv hx - ∑ k ∈ Finset.range (K + 1), x ^ k) (j - i)‖
      ≤ ‖(1 - x : HaloInt p) i‖ *
        ‖(geomInv hx - ∑ k ∈ Finset.range (K + 1), x ^ k) (j - i)‖ := norm_mul_le _ _
    _ ≤ (p : ℝ) ^ min 0 i * Real.sqrt ((p : ℝ) ^ (j - i - (K + 1))) := by
        refine mul_le_mul hi ?_ (norm_nonneg _) (zpow_nonneg hp0.le _)
        rw [HaloInt.coeff_sub]
        exact norm_geomInv_sub_sum_le hx K (j - i)
    _ ≤ Real.sqrt ((p : ℝ) ^ (j - (K + 1))) := by
        rw [show ((p : ℝ) ^ min 0 i) = Real.sqrt ((p : ℝ) ^ (2 * min 0 i)) from by
          rw [show (2 : ℤ) * min 0 i = min 0 i + min 0 i from by ring, zpow_add₀ hp0.ne',
            Real.sqrt_mul_self (zpow_nonneg hp0.le _)],
          ← Real.sqrt_mul (zpow_nonneg hp0.le _), ← zpow_add₀ hp0.ne']
        refine Real.sqrt_le_sqrt (zpow_le_zpow_right₀ hp1.le ?_)
        have h0i : min 0 i ≤ 0 := min_le_left _ _
        have hmi : min 0 i ≤ i := min_le_right _ _
        omega

omit [Fintype ι] [DecidableEq ι] in
-- `(1 − x)·∑ₖ xᵏ = 1`, proved coefficientwise: the partial sums satisfy
-- `(1 − x)·S_K = 1 − x^{K+1}` and the tail of the series is uniformly small.
private theorem one_sub_mul_geomInv (hx : x 0 = 0) : (1 - x) * geomInv hx = 1 := by
  refine HaloInt.ext fun j => ?_
  have hzero : ‖((1 - x) * geomInv hx) j - (1 : HaloInt p) j‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto (b := (Filter.atTop : Filter ℕ))
      (f := fun _ : ℕ => ‖((1 - x) * geomInv hx) j - (1 : HaloInt p) j‖)
      (g := fun K : ℕ => Real.sqrt ((p : ℝ) ^ (j - ((K : ℤ) + 1))) + ‖(x ^ (K + 1)) j‖)
      tendsto_const_nhds ?_ (Filter.Eventually.of_forall fun K => ?_)
    · have h1 : Tendsto (fun K : ℕ => Real.sqrt ((p : ℝ) ^ (j - ((K : ℤ) + 1)))) atTop (𝓝 0) := by
        refine ((tendsto_sqrt_zpow_sub (p := p) j).comp
          (Filter.tendsto_add_atTop_nat 1)).congr fun K => ?_
        show Real.sqrt ((p : ℝ) ^ (j - ((K + 1 : ℕ) : ℤ))) =
          Real.sqrt ((p : ℝ) ^ (j - ((K : ℤ) + 1)))
        push_cast
        ring_nf
      have h3 : Tendsto (fun K : ℕ => ‖(x ^ (K + 1)) j‖) atTop (𝓝 0) :=
        (tendsto_norm_coeff_pow hx j).comp (Filter.tendsto_add_atTop_nat 1)
      simpa using h1.add h3
    · have hsplit : ((1 - x) * geomInv hx) j - (1 : HaloInt p) j =
          ((1 - x) * (geomInv hx - ∑ k ∈ Finset.range (K + 1), x ^ k)) j +
            (-((x ^ (K + 1)) j)) := by
        have hgeom : (1 - x) * (∑ k ∈ Finset.range (K + 1), x ^ k) = 1 - x ^ (K + 1) :=
          mul_neg_geom_sum x (K + 1)
        have hmul : ((1 - x) * (geomInv hx - ∑ k ∈ Finset.range (K + 1), x ^ k)) j =
            ((1 - x) * geomInv hx) j - ((1 : HaloInt p) - x ^ (K + 1)) j := by
          rw [← hgeom, ← HaloInt.coeff_sub, mul_sub]
        rw [hmul, HaloInt.coeff_sub]
        ring
      rw [hsplit]
      refine (_root_.norm_add_le _ _).trans
        (add_le_add (norm_mul_geomInv_sub_sum_le hx K j) ?_)
      rw [norm_neg]
  have h := norm_le_zero_iff.1 hzero
  rw [sub_eq_zero] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **Units of the integral halo ring**, geometric-series form: `1 − x` is a unit whenever the
constant coefficient of `x` vanishes ([LWX, Lemma 3.15]).  The inverse `∑ₖ xᵏ` converges
coefficientwise `p`-adically because a monomial of `xᵏ` landing in degree `j` uses at least
`(k − j)/2` factors of negative degree, each carrying a factor `p`. -/
theorem HaloInt.isUnit_one_sub_of_coeff_zero (hx : x 0 = 0) : IsUnit (1 - x) :=
  isUnit_iff_exists.2 ⟨geomInv hx, one_sub_mul_geomInv hx,
    by rw [mul_comm]; exact one_sub_mul_geomInv hx⟩

end HaloUnits

/-- **Units of the integral halo ring**: an element of `Λ^{>1/p}` whose constant coefficient
is a `p`-adic unit is a unit ([LWX, Lemma 3.15]: "`𝔪_Λ Λ^{>1/p}` is the same as the principal
ideal `(T)`").  Rescale by the constant coefficient and apply
`HaloInt.isUnit_one_sub_of_coeff_zero`. -/
theorem HaloInt.isUnit_of_isUnit_coeff_zero (g : HaloInt p) (hg : IsUnit (g 0)) : IsUnit g := by
  obtain ⟨u, hu⟩ := hg
  have hx0 : (1 - HaloInt.constRingHom ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * g) 0 = 0 := by
    rw [HaloInt.coeff_sub, HaloInt.coeff_one, if_pos rfl, HaloInt.constRingHom_apply,
      HaloInt.coeff_const_mul, ← hu, Units.inv_mul, sub_self]
  have hgx : g = HaloInt.constRingHom ((u : ℤ_[p])) *
      (1 - (1 - HaloInt.constRingHom ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * g)) := by
    rw [sub_sub_cancel, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [hgx]
  exact (u.isUnit.map HaloInt.constRingHom).mul (HaloInt.isUnit_one_sub_of_coeff_zero hx0)

/-- **The bridge from [LWX, Cor 3.18]'s unit-coefficient form of the vertex hypothesis** ("with
equality holding if and only if `b_{n,λ(n)} ∈ ℤ_p^×`"; [LWX, (3.23.2)]) **to `IsHaloVertex`**:
at a genuine vertex of `λ`, if the `T^{λ(n)}`-coefficient of `c_n` is a `p`-adic unit then
`c_n = T^{λ(n)}·(unit of Λ^{>1/p})` — the form in which [LWX, Remark 3.25] uses it.  This is
the interface the deferred Atkin–Lehner/classicality board must produce (see `plan.md`,
"Dependence on Atkin–Lehner"). -/
theorem UpDatum.isHaloVertex_of_isUnit_coeff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {n : ℕ}
    (hvert : (n - 1) / Fintype.card ι - (n - 1) / (p * Fintype.card ι) <
      n / Fintype.card ι - n / (p * Fintype.card ι))
    (hb : IsUnit (charCoeff (D.op ω) n (lwxLambda p (Fintype.card ι) n : ℤ))) :
    UpDatum.IsHaloVertex D ω n := by
  obtain ⟨g, hg⟩ := exists_charCoeff_upOp_eq_T_pow_mul hp2 D ω n
  have hg0 : g 0 = charCoeff (D.op ω) n (lwxLambda p (Fintype.card ι) n : ℤ) := by
    rw [hg, HaloInt.coeff_T_pow_mul, sub_self]
  obtain ⟨e, he⟩ := HaloInt.isUnit_of_isUnit_coeff_zero g (hg0 ▸ hb)
  have hnorm : ‖(e : HaloInt p)‖ = 1 := by
    refine le_antisymm (HaloInt.norm_le_one _) ?_
    have hmul := norm_mul_le ((e : HaloInt p)) (((e⁻¹ : (HaloInt p)ˣ) : HaloInt p))
    rw [show ((e : HaloInt p)) * (((e⁻¹ : (HaloInt p)ˣ) : HaloInt p)) = 1 from
      e.mul_inv, norm_one] at hmul
    have hinv := HaloInt.norm_le_one (((e⁻¹ : (HaloInt p)ˣ) : HaloInt p))
    nlinarith [norm_nonneg ((e : HaloInt p)), norm_nonneg (((e⁻¹ : (HaloInt p)ˣ) : HaloInt p))]
  exact ⟨⟨e, hnorm, by rw [hg, he]⟩, hvert⟩

end LWX

end
