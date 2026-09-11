/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.HaloWeight
import PhD.LWX.Colmez
import PhD.LWX.Certificates
import PhD.TateFredholm.Conjugation
import PhD.QMF.Weight.Fredholm

/-!
# [LWX, Proposition 2.17]: the integral `Char(P)` specialises to `Char(U_p; S^{D,†,1})`

[LWX, Prop 2.17]: "Using the isomorphism (2.11.1), the space `S^D_int` admits an orthonormal
basis (over `Λ`) given by `1₀, …, 1_{t−1}, z₀, …, z_{t−1}, (z₀ choose 2), …` … Let `P` denote
the corresponding infinite matrix for the `U_p`-action … Suppose that the limit `Char(P) :=
det(I∞ − XP)` exists (which we shall prove in Theorem 3.16).  Then it agrees with the
characteristic power series of the `U_p`-action on each `S^{D,†,m}_{[−]_m}`."  Proof: "the
functions `⌊n/(q⁻¹pᵐ)⌋!·(zᵢ choose n)` form an orthonormal basis of `S^{D,†,m}_{[−]_m}`.  If `P′`
denotes the infinite matrix of `U_p`-action on this basis, then `P` and `P′` are conjugated by an
infinite diagonal matrix … So taking the limit of the characteristic polynomial of the first
`r × r`-minors … gives `Char(U_p; S^{D,†,m}_{[−]_m}) = det(I∞ − XP′) = det(I∞ − XP)`."

This file proves the `m = 1` case on the sub-annulus `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹` (where the
halo weight is `1`-analytic, `PhD/LWX/HaloWeight.lean`), identifying
`specCharSeries D ω ψ T₀` (`Char(P)` evaluated at `T₀`, `PhD/LWX/Halo.lean`) with the
general-weight layer's `QMF.Weight.heckeCharPowerSeries` at the halo weight — the Fredholm
determinant of `U_p` on Buzzard's `S^{D,†,1}` in the monomial basis of the Tate algebra:

1. the specialised operator `specOp D` on `c(ι × ℕ, K)` (matrix `P(T₀)` in the Mahler basis)
   has `charCoeff = specialize (charCoeff (D.op ω))` — the specialization is a continuous ring
   homomorphism and the minors are determinants (`charCoeff_specOp`);
2. **the seam identity**: monomial-to-Mahler coordinates intertwine the QMF action of a
   certificate matrix with `P(T₀)` — both are `f ↦ χ(cz+d)·f(möb z)` read at `ℕ`-points
   (`monomialToMahler_comp_kappaSlash`), hence blockwise for `[UηU]`
   (`monomialToMahlerBlock_comp_heckeBlockOp`);
3. `monomialToMahler = diag(m!) ∘ colmezEquiv.symm` (`PhD/LWX/Colmez.lean`), so the Colmez-basis
   matrix `P′ = colmezEquiv⁻¹·[UηU]·colmezEquiv` satisfies `diag(m!)·P′ = P(T₀)·diag(m!)`, and
   `charPowerSeries_eq_of_diag_intertwine` gives `det(I − XP′) = det(I − XP(T₀))`;
4. `charPowerSeries_conj` (basis independence, [Buzzard, Cor 2.6]) gives
   `det(I − XP′) = det(I − X[UηU])`.

## Main declarations

* `LWX.specOp`, `LWX.charPowerSeries_specOp` — `P(T₀)` and `det(I − XP(T₀)) = Char(P)(T₀)`.
* `LWX.thetaK`, `LWX.levelMonoidOf_thetaK` — the `K`-side component map and level.
* `LWX.monomialToMahler_comp_kappaSlash` — the seam identity for one certificate matrix.
* **`LWX.specCharSeries_ofCerts_eq_heckeCharPowerSeries`** — [LWX, Prop 2.17] at `m = 1`.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash

open scoped Nat TateFredholm Pointwise fwdDiff

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section SpecOp

variable (hp2 : p ≠ 2) (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
  (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

omit hp2 hψ h0 h1 in
/-- The specialised entry stream of a local matrix, as an operator on `c(ℕ, K)`: the matrix
`P_{m,n}(δ)(T₀)` in the Mahler basis (entries integral, columns decaying — `norm_entry_le_M1`
and `norm_specialize_le`).  The hypotheses are explicit (they are consumed only by the proof
fields). -/
def specEntryOp (hp2 : p ≠ 2) (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (δ : LocalMat p) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m n => HaloInt.specialize (intHom ψ) T₀ (entry ω δ m n))
    ⟨1, fun m n => by
      have h := HaloInt.norm_specialize_le (intHom ψ) (norm_intHom ψ hψ) h0 h1 (k := 0)
        (f := entry ω δ m n) (by
          rw [Nat.cast_zero, neg_zero, zpow_zero]
          exact HaloInt.norm_le_one _)
      rwa [pow_zero] at h⟩
    (fun n => by
      rw [Nat.cofinite_eq_atTop]
      refine squeeze_zero_norm (fun m => HaloInt.norm_specialize_le (intHom ψ) (norm_intHom ψ hψ)
        h0 h1 (k := m - n) (norm_entry_le_M1 hp2 ω δ m n)) ?_
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).comp
        (tendsto_sub_atTop_nat n))

omit [CharZero K] in
/-- The matrix of `specEntryOp`. -/
theorem matrixCoeff_specEntryOp (δ : LocalMat p) (m n : ℕ) :
    matrixCoeff (specEntryOp hp2 ψ hψ h0 h1 ω δ) m n
      = HaloInt.specialize (intHom ψ) T₀ (entry ω δ m n) :=
  matrixCoeff_ofCoeffs _ _ _ m n

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The specialised integral `U_p`** `P(T₀)` on the block model `c(ι × ℕ, K)`: the block
`(i, j)` is the sum of the specialised entry streams of the summands with target `j`
(`UpDatum.matrix` specialised). -/
def specOp (D : UpDatum p ι) : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) :=
  blockOp fun i j =>
    ∑ t ∈ Finset.univ.filter (fun t : Fin p => D.tgt i t = j),
      specEntryOp hp2 ψ hψ h0 h1 ω (D.mat i t)

omit [CharZero K] in
/-- The matrix of `specOp` is the specialised matrix of the datum. -/
theorem matrixCoeff_specOp (D : UpDatum p ι) (a b : ι × ℕ) :
    matrixCoeff (specOp hp2 ψ hψ h0 h1 ω D) a b
      = HaloInt.specialize (intHom ψ) T₀ (D.matrix ω a b) := by
  obtain ⟨i, m⟩ := a
  obtain ⟨j, n⟩ := b
  rw [specOp, matrixCoeff_blockOp, matrixCoeff_sum]
  simp only [UpDatum.matrix]
  rw [← HaloInt.specializeHom_apply (intHom ψ) (norm_intHom ψ hψ) h0 h1, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [HaloInt.specializeHom_apply, matrixCoeff_specEntryOp]

omit [CharZero K] in
/-- The minors of `P(T₀)` are the specialised minors of `P` (`RingHom.map_det`). -/
theorem minor_specOp (D : UpDatum p ι) (S : Finset (ι × ℕ)) :
    minor (specOp hp2 ψ hψ h0 h1 ω D) S
      = HaloInt.specialize (intHom ψ) T₀ (minor (D.op ω) S) := by
  unfold minor
  rw [← HaloInt.specializeHom_apply (intHom ψ) (norm_intHom ψ hψ) h0 h1, RingHom.map_det]
  congr 1
  ext j i
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
    HaloInt.specializeHom_apply, matrixCoeff_specOp, UpDatum.matrixCoeff_op hp2]

omit [CharZero K] in
/-- **`c_n(P(T₀)) = c_n(P)(T₀)`**: the coefficients of `det(I − XP(T₀))` are the specialised
coefficients of `Char(P)` — the specialization is continuous (`HasSum.specialize`) and the
integral minors are summable ([LWX, Thm 3.16], `summable_minor_upOp`). -/
theorem charCoeff_specOp (D : UpDatum p ι) (n : ℕ) :
    charCoeff (specOp hp2 ψ hψ h0 h1 ω D) n
      = HaloInt.specialize (intHom ψ) T₀ (charCoeff (D.op ω) n) := by
  unfold charCoeff
  rw [← HaloInt.specializeHom_apply (intHom ψ) (norm_intHom ψ hψ) h0 h1, map_mul, map_pow,
    map_neg, map_one, HaloInt.specializeHom_apply,
    ← (HaloInt.HasSum.specialize (intHom ψ) (norm_intHom ψ hψ) h0 h1
      (summable_minor_upOp hp2 D ω n).hasSum).tsum_eq]
  congr 1
  exact tsum_congr fun S => minor_specOp hp2 ψ hψ h0 h1 ω D S

omit [CharZero K] in
/-- **`det(I − XP(T₀)) = Char(P)(T₀)`**: the Fredholm determinant of the specialised operator is
the specialised characteristic series of [LWX, Cor 3.18]. -/
theorem charPowerSeries_specOp (D : UpDatum p ι) :
    charPowerSeries (specOp hp2 ψ hψ h0 h1 ω D) = specCharSeries D ω (intHom ψ) T₀ :=
  PowerSeries.ext fun n => by
    rw [charPowerSeries_coeff, specCharSeries, PowerSeries.coeff_mk, charCoeff_specOp]

end SpecOp

section Level

variable (ψ : ℚ_[p] →+* K) {G : Type*} [Group G] (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])

/-- The `K`-side component map `θ_K = ψ ∘ θ`. -/
def thetaK : G →* Matrix (Fin 2) (Fin 2) K :=
  (RingHom.mapMatrix ψ).toMonoidHom.comp θ

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem thetaK_apply (g : G) : thetaK ψ θ g = (RingHom.mapMatrix ψ) (θ g) := rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The wild-level monoid of the `K`-side map at `M1K` is the level monoid of the integral
model (`ψ` is injective). -/
theorem levelMonoidOf_thetaK : levelMonoidOf (thetaK ψ θ) (M1K ψ) = levelM1 (p := p) θ := by
  ext g
  rw [levelMonoidOf, Submonoid.mem_comap, thetaK_apply, M1K, Submonoid.mem_map, levelM1,
    Submonoid.mem_comap]
  constructor
  · rintro ⟨δ, hδ, hδg⟩
    have hδ' : δ = θ g := by
      ext i j
      exact ψ.injective (congrFun (congrFun hδg i) j)
    rwa [hδ'] at hδ
  · intro hg
    exact ⟨θ g, hg, rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The level group of the integral model lies in the `K`-side level monoid. -/
theorem subset_levelMonoidOf_thetaK (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ) :
    (U : Set G) ⊆ levelMonoidOf (thetaK ψ θ) (M1K ψ) := by
  rw [levelMonoidOf_thetaK]
  exact hU

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Members of the integral level monoid lie in the `K`-side level monoid. -/
theorem mem_levelMonoidOf_thetaK {g : G} (hg : g ∈ levelM1 (p := p) θ) :
    g ∈ levelMonoidOf (thetaK ψ θ) (M1K ψ) := by
  rw [levelMonoidOf_thetaK]
  exact hg

/-- The `K`-side image of an element of `M₁`. -/
def M1K.ofM1 (δ : M1 p) : M1K ψ := ⟨(RingHom.mapMatrix ψ) δ.1, ⟨δ.1, δ.2, rfl⟩⟩

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem M1K.coe_ofM1 (δ : M1 p) : (M1K.ofM1 ψ δ : Matrix (Fin 2) (Fin 2) K)
    = (RingHom.mapMatrix ψ) δ.1 := rfl

end Level

section SeamIdentity

variable (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- The Mahler coordinates of the monomial `z ↦ zⁿ` as a sequence in `c(ℕ, Λ^{>1/p})`
(finitely supported, integral). -/
def mahlerOfPow (n : ℕ) : c(ℕ, HaloInt p) :=
  cSpace.ofTendsto (fun k => HaloInt.const (mahlerCoeffPow k n : ℤ_[p])) (by
    refine tendsto_const_nhds.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_cofinite]
    refine (Finset.range (n + 1)).finite_toSet.subset fun k hk => ?_
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hk ?_
    rw [mahlerCoeffPow_eq_zero_of_lt (by omega), Int.cast_zero, ← HaloInt.constRingHom_apply,
      map_zero])

/-- The plain Mahler realisation of `mahlerOfPow n` is the monomial `z ↦ zⁿ`
(`pow_eq_sum_choose_mul_mahlerCoeffPow` through `mahlerON_apply`). -/
theorem mahlerON_mahlerOfPow (n : ℕ) (z : ℤ_[p]) :
    mahlerON (mahlerOfPow (p := p) n) z = HaloInt.const (z ^ n) := by
  rw [mahlerON_apply, tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      change HaloInt.const (mahlerCoeffPow k n : ℤ_[p]) * _ = 0
      rw [mahlerCoeffPow_eq_zero_of_lt (by omega), Int.cast_zero,
        ← HaloInt.constRingHom_apply, map_zero, zero_mul]),
    pow_eq_sum_choose_mul_mahlerCoeffPow, ← HaloInt.constRingHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change HaloInt.const (mahlerCoeffPow k n : ℤ_[p]) * HaloInt.const (Ring.choose z k) = _
  rw [← HaloInt.const_mul, HaloInt.constRingHom_apply,
    mul_comm ((mahlerCoeffPow k n : ℤ) : ℤ_[p]) (Ring.choose z k)]

/-- Forward differences at `0` of a function on `ℤ_p` only see its values at `ℕ`-points. -/
theorem fwdDiff_iter_comp_natCast {M : Type*} [AddCommGroup M] (f : ℤ_[p] → M) (m : ℕ) :
    Δ_[1]^[m] (fun j : ℕ => f (j : ℤ_[p])) 0 = Δ_[1]^[m] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp

/-- **The Mahler coordinates of `[cz+d]·möb(z)ⁿ`** (integral): `Δ^m(z ↦ [cz+d]·möb(z)ⁿ)(0)
= ∑_{k ≤ n} Δ^k(zⁿ)(0)·P_{m,k}(δ)` — [LWX, Prop 3.4] (`seqSlash_coeff`) applied to the finite
Mahler expansion of the monomial. -/
theorem fwdDiff_iter_cfunSlash_pow (hp2 : p ≠ 2) (δ : M1 p) (n m : ℕ) :
    Δ_[1]^[m] (fun z : ℤ_[p] => univChar ω ((M1.toLocalMat δ).denUnit z)
        * HaloInt.const ((M1.toLocalMat δ).mobiusFun z ^ n)) 0
      = ∑ k ∈ Finset.range (n + 1),
          (mahlerCoeffPow k n : HaloInt p) * entry ω (M1.toLocalMat δ) m k := by
  have hfun : (fun z : ℤ_[p] => univChar ω ((M1.toLocalMat δ).denUnit z)
        * HaloInt.const ((M1.toLocalMat δ).mobiusFun z ^ n))
      = ⇑(cfunSlash hp2 ω (mahlerON (mahlerOfPow n)) δ) := by
    funext z
    change _ = univChar ω ((M1.toLocalMat δ).denUnit z)
      * mahlerON (mahlerOfPow n) ((M1.toLocalMat δ).mobiusFun z)
    rw [mahlerON_mahlerOfPow]
  rw [hfun, ← mahlerCoeffs_apply]
  change (RightSlashAction.slash (self := seqSlashAction hp2 ω) (mahlerOfPow n) δ) m = _
  rw [seqSlash_coeff, tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    change HaloInt.const (mahlerCoeffPow k n : ℤ_[p]) * _ = 0
    rw [mahlerCoeffPow_eq_zero_of_lt (by omega), Int.cast_zero, ← HaloInt.constRingHom_apply,
      map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (mahlerCoeffPow k n : HaloInt p) = HaloInt.constRingHom (mahlerCoeffPow k n : ℤ_[p])
    from (map_intCast HaloInt.constRingHom _).symm]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ψ` of the denominator `cz + d` is the `K`-side denominator at `ψ z`. -/
theorem intHom_denUnit (δ : M1 p) (z : ℤ_[p]) :
    intHom ψ ((M1.toLocalMat δ).denUnit z : ℤ_[p])
      = (RingHom.mapMatrix ψ) δ.1 1 0 * intHom ψ z + (RingHom.mapMatrix ψ) δ.1 1 1 := by
  change intHom ψ (((M1.toLocalMat δ).isUnit_c_mul_add z).unit : ℤ_[p]) = _
  rw [IsUnit.unit_spec, map_add, map_mul]
  simp only [intHom_apply, M1.coe_toLocalMat_c, M1.coe_toLocalMat_d]
  rfl

omit [IsUltrametricDist K] [CharZero K] in
/-- `ψ` of the Möbius value is the evaluated `K`-side Möbius series at `ψ z`
(`evalAt_mobius`). -/
theorem intHom_mobiusFun (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (δ : M1 p) (z : ℤ_[p]) :
    intHom ψ ((M1.toLocalMat δ).mobiusFun z)
      = evalAt (mobius ((RingHom.mapMatrix ψ) δ.1)) (intHom ψ z) := by
  have hd : (RingHom.mapMatrix ψ) δ.1 1 1 ≠ 0 := by
    change ψ (δ.1 1 1) ≠ 0
    rw [← norm_ne_zero_iff, hψ, δ.2.2.2.1]
    exact one_ne_zero
  have hlt : ‖(RingHom.mapMatrix ψ) δ.1 1 0‖ < ‖(RingHom.mapMatrix ψ) δ.1 1 1‖ := by
    change ‖ψ (δ.1 1 0)‖ < ‖ψ (δ.1 1 1)‖
    rw [hψ, hψ, δ.2.2.2.1]
    exact δ.2.2.1.trans_lt (inv_lt_one_p (p := p))
  have hz : ‖intHom ψ z‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]
    exact PadicInt.norm_le_one z
  have hinv : Ring.inverse ((M1.toLocalMat δ).c * z + ((M1.toLocalMat δ).d : ℤ_[p]))
      = ((((M1.toLocalMat δ).denUnit z)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [← Ring.inverse_unit ((M1.toLocalMat δ).denUnit z)]
    rfl
  rw [evalAt_mobius hd hlt hz, div_eq_mul_inv, LocalMat.mobiusFun, hinv, map_mul, map_add,
    map_mul, map_units_inv, intHom_denUnit ψ δ z]
  simp only [intHom_apply, M1.coe_toLocalMat_a, M1.coe_toLocalMat_b]
  rfl

/-- **The value at `ℕ`-points of the QMF slash of a monomial** — the power series with
coefficients `kappaSlash g (single n 1)` is `autFactor g · mobius g ^ n`. -/
theorem mk_kappaSlash_single (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (g : M1K ψ) (n : ℕ) :
    PowerSeries.mk (fun j => (haloWeight ψ T₀ ω hp2 hψ h0 h1).kappaSlash g (cSpace.single n 1) j)
      = (haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1 * mobius g.1 ^ n := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_mk, AnalyticWeight.kappaSlash_def, WeightSeries.kappaSlash_apply,
    tsum_eq_single n (fun i hi => by rw [cSpace.single_apply_of_ne hi, mul_zero]),
    cSpace.single_apply_self, mul_one]

/-- **Pointwise agreement at `ℕ`-points**: the specialised integral slash of `zⁿ` and the
`K`-side slash of `zⁿ` take the same value `χ(cn+d)·möb(n)ⁿ` at every `n ∈ ℕ`
(`haloCharFun_psi`, `evalAt_autFactor_haloWeight`, `intHom_denUnit`, `intHom_mobiusFun`). -/
theorem specialize_cfunSlash_pow_natCast (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (δ : M1 p) (n k : ℕ) :
    HaloInt.specialize (intHom ψ) T₀ (univChar ω ((M1.toLocalMat δ).denUnit k)
        * HaloInt.const ((M1.toLocalMat δ).mobiusFun k ^ n))
      = evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor
          ((RingHom.mapMatrix ψ) δ.1) * mobius ((RingHom.mapMatrix ψ) δ.1) ^ n) (k : K) := by
  have h1' := norm_lt_one_of_sq_lt h1
  have hg : (RingHom.mapMatrix ψ) δ.1 ∈ M1K ψ := ⟨δ.1, δ.2, rfl⟩
  have hk : ‖(k : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K k
  have hev := evalAt_autFactor_haloWeight ψ T₀ ω hp2 hψ h0 h1 (M1K.ofM1 ψ δ) hk
  rw [M1K.coe_ofM1] at hev
  rw [HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1', HaloInt.specialize_const,
    ← haloCharFun_psi ψ T₀ ω hp2 hψ h0 h1, intHom_denUnit, map_natCast, map_pow,
    intHom_mobiusFun ψ hψ, map_natCast,
    evalAt_mul ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable_autFactor hg)
      (PowerSeries.absSummable_pow
        ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable_mobius hg) n) hk,
    evalAt_pow ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable_mobius hg) hk, hev]

/-- **The seam identity for one certificate matrix**: monomial-to-Mahler coordinates
intertwine the halo-weight action of `ψ(δ)` with the specialised entry stream `P(δ)(T₀)`:
`Φ ∘ (·‖_κ ψ(δ)) = P(δ)(T₀) ∘ Φ`.  Both sides, on `e_n`, are the Mahler coordinates of
`z ↦ χ(cz+d)·möb(z)ⁿ` (`fwdDiff_iter_evalAt_natCast` on the left,
`fwdDiff_iter_cfunSlash_pow` specialised on the right). -/
theorem monomialToMahler_comp_kappaSlash (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (δ : M1 p) :
    (monomialToMahler K).comp ((haloWeight ψ T₀ ω hp2 hψ h0 h1).kappaSlash (M1K.ofM1 ψ δ))
      = (specEntryOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω (M1.toLocalMat δ)).comp
          (monomialToMahler K) := by
  have h1' := norm_lt_one_of_sq_lt h1
  have hg : (RingHom.mapMatrix ψ) δ.1 ∈ M1K ψ := ⟨δ.1, δ.2, rfl⟩
  refine ext_matrixCoeff fun m n => ?_
  rw [matrixCoeff_comp, matrixCoeff_comp]
  have hF : PowerSeries.AbsSummable ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor
      ((RingHom.mapMatrix ψ) δ.1) * mobius ((RingHom.mapMatrix ψ) δ.1) ^ n) :=
    PowerSeries.absSummable_mul
      ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable_autFactor hg)
      (PowerSeries.absSummable_pow
        ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable_mobius hg) n)
  have hmk := mk_kappaSlash_single ψ T₀ ω hp2 hψ h0 h1 (M1K.ofM1 ψ δ) n
  rw [M1K.coe_ofM1] at hmk
  have hcoef : ∀ k, matrixCoeff ((haloWeight ψ T₀ ω hp2 hψ h0 h1).kappaSlash (M1K.ofM1 ψ δ)) k n
      = PowerSeries.coeff k ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor
          ((RingHom.mapMatrix ψ) δ.1) * mobius ((RingHom.mapMatrix ψ) δ.1) ^ n) := fun k => by
    rw [← hmk, PowerSeries.coeff_mk]
    rfl
  simp_rw [hcoef, matrixCoeff_monomialToMahler]
  rw [← fwdDiff_iter_evalAt_natCast K (QMF.AbsSummable.tendstoCoeff hF) m]
  have hpt : (fun j : ℕ => evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor
        ((RingHom.mapMatrix ψ) δ.1) * mobius ((RingHom.mapMatrix ψ) δ.1) ^ n) (j : K))
      = fun j : ℕ => (HaloInt.specializeHom (intHom ψ) (norm_intHom ψ hψ) h0 h1').toAddMonoidHom
          (univChar ω ((M1.toLocalMat δ).denUnit (j : ℤ_[p]))
            * HaloInt.const ((M1.toLocalMat δ).mobiusFun (j : ℤ_[p]) ^ n)) :=
    funext fun j => (specialize_cfunSlash_pow_natCast ψ T₀ ω hp2 hψ h0 h1 δ n j).symm
  rw [hpt, map_fwdDiff_iter, fwdDiff_iter_comp_natCast (fun z : ℤ_[p] =>
      univChar ω ((M1.toLocalMat δ).denUnit z) * HaloInt.const ((M1.toLocalMat δ).mobiusFun z ^ n)),
    fwdDiff_iter_cfunSlash_pow ω hp2 δ n m, map_sum,
    tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      rw [mahlerCoeffPow_eq_zero_of_lt (by omega), Int.cast_zero, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  change HaloInt.specializeHom (intHom ψ) (norm_intHom ψ hψ) h0 h1'
    ((mahlerCoeffPow k n : HaloInt p) * entry ω (M1.toLocalMat δ) m k) = _
  rw [map_mul, map_intCast, matrixCoeff_specEntryOp]
  rfl

end SeamIdentity

section Assembly

variable (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
variable {G : Type*} [Group G] (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p]) (U : Subgroup G)
  (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

/-- The blockwise monomial-to-Mahler map on the block model. -/
def monomialToMahlerBlock : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) := blockDiag (monomialToMahler K)

/-- The blockwise `diag(m!)`. -/
def diagFactorialBlock : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) := blockDiag (diagFactorial K)

/-- The blockwise Colmez basis change. -/
def colmezEquivBlock : c(ι × ℕ, K) ≃L[K] c(ι × ℕ, K) := diagBlockEquiv (colmezEquiv K)

omit [CharZero K] in
/-- `monomialToMahlerBlock = diagFactorialBlock ∘ colmezEquivBlock.symm` (blockwise
`monomialToMahler_eq`). -/
theorem monomialToMahlerBlock_eq :
    (monomialToMahlerBlock (K := K) (ι := ι))
      = (diagFactorialBlock (K := K) (ι := ι)).comp
          ((colmezEquivBlock (K := K) (ι := ι)).symm : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) := by
  unfold monomialToMahlerBlock diagFactorialBlock colmezEquivBlock
  rw [coe_diagBlockEquiv_symm, blockDiag_comp, ← monomialToMahler_eq]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [Fintype ι] [DecidableEq ι] in
/-- The certificate matrices, read on the `K`-side, are `ψ` of the integral certificates. -/
theorem thetaK_cert (i : ι) (t : Fin p) :
    thetaK ψ θ ((u i t : G) * vRep t) = (RingHom.mapMatrix ψ) (certM1 θ U hU vRep hvΔ u i t).1 :=
  rfl

/-- **The seam identity blockwise**: the monomial-to-Mahler map intertwines the QMF block
operator of `[UηU]` at the halo weight (untwisted, `χ = 1`) with the specialised integral
`U_p` of the certificate datum (`monomialToMahler_comp_kappaSlash` summed over the
certificates with target `j`, `blockDiag_comp_blockOp`, `blockOp_comp_blockDiag`). -/
theorem monomialToMahlerBlock_comp_heckeBlockOp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (monomialToMahlerBlock (K := K) (ι := ι)).comp
        (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
          (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
          (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u)
      = (specOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω
          (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (monomialToMahlerBlock (K := K) (ι := ι)) := by
  unfold monomialToMahlerBlock heckeBlockOp specOp
  rw [blockDiag_comp_blockOp, blockOp_comp_blockDiag]
  congr 1
  funext i j
  unfold heckeBlock
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, UpDatum.ofCerts_mat,
    UpDatum.ofCerts_tgt]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h := DFunLike.congr_fun (monomialToMahler_comp_kappaSlash ψ T₀ ω hp2 hψ h0 h1
    (certM1 θ U hU vRep hvΔ u i t)) x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
  exact h

/-- **`U_p` is compactoid at the halo weight** — every certificate matrix has the `U_p`-shape
`‖a‖ ≤ p⁻¹ ≤ ρ` (`isCompactoid_kappaSlash`, `isCompactoid_blockOp`); [Buzzard, Lemma 12.2]. -/
theorem isCompactoid_heckeBlockOp_haloWeight (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    IsCompactoid (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
      (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
      (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u) := by
  refine isCompactoid_blockOp fun i j => ?_
  unfold heckeBlock
  refine IsCompactoid.finset_sum _ fun t _ => IsCompactoid.smul _ ?_
  refine (haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.isCompactoid_kappaSlash _ le_rfl
    (haloRho_lt_one T₀ h1) ?_
  change ‖ψ (θ ((u i t : G) * vRep t) 0 0)‖ ≤ haloRho (p := p) T₀
  rw [hψ]
  refine le_trans ?_ (inv_le_haloRho T₀ h0)
  have h := hshape i t
  unfold LocalMat.IsUpShape at h
  rw [PadicInt.norm_def, M1.coe_toLocalMat_a] at h
  exact h

omit [CharZero K] in
/-- The matrix of the blockwise `diag(m!)`. -/
theorem matrixCoeff_diagFactorialBlock (a b : ι × ℕ) :
    matrixCoeff (diagFactorialBlock (K := K) (ι := ι)) a b
      = if a = b then ((a.2 ! : ℕ) : K) else 0 := by
  obtain ⟨i, m⟩ := a
  obtain ⟨j, n⟩ := b
  rw [diagFactorialBlock, matrixCoeff_blockDiag, matrixCoeff_diagFactorial]
  by_cases hij : i = j
  · subst hij
    by_cases hmn : m = n
    · subst hmn
      simp
    · simp [hmn]
  · simp [hij]

omit [CharZero K] in
/-- Left composition with `diag(m!)` scales the rows. -/
theorem matrixCoeff_diagFactorialBlock_comp (u : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (a b : ι × ℕ) :
    matrixCoeff ((diagFactorialBlock (K := K) (ι := ι)).comp u) a b
      = ((a.2 ! : ℕ) : K) * matrixCoeff u a b := by
  rw [matrixCoeff_comp, tsum_eq_single a (fun c hc => by
    rw [matrixCoeff_diagFactorialBlock, if_neg (Ne.symm hc), mul_zero]),
    matrixCoeff_diagFactorialBlock, if_pos rfl, mul_comm]

omit [CharZero K] in
/-- Right composition with `diag(m!)` scales the columns. -/
theorem matrixCoeff_comp_diagFactorialBlock (u : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (a b : ι × ℕ) :
    matrixCoeff (u.comp (diagFactorialBlock (K := K) (ι := ι))) a b
      = matrixCoeff u a b * ((b.2 ! : ℕ) : K) := by
  rw [matrixCoeff_comp, tsum_eq_single b (fun c hc => by
    rw [matrixCoeff_diagFactorialBlock, if_neg hc, zero_mul]),
    matrixCoeff_diagFactorialBlock, if_pos rfl, mul_comm]

/-- **The Colmez-basis matrix `P′` of `U_p`** (conjugate of the QMF block operator by the
Colmez basis change) is diagonally intertwined with `P(T₀)`:
`diag(m!)·P′ = P(T₀)·diag(m!)` (from `monomialToMahlerBlock_comp_heckeBlockOp` and
`monomialToMahlerBlock_eq`). -/
theorem diagFactorialBlock_comp_colmezConj (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (diagFactorialBlock (K := K) (ι := ι)).comp
        ((((colmezEquivBlock (K := K) (ι := ι)).symm : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)).comp
          (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
            (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
            (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u)).comp
          (colmezEquivBlock (K := K) (ι := ι) : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)))
      = (specOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω
          (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (diagFactorialBlock (K := K) (ι := ι)) := by
  have h := monomialToMahlerBlock_comp_heckeBlockOp ψ T₀ ω θ U hU vRep hvΔ idx u hp2 hψ h0 h1
    hshape
  rw [monomialToMahlerBlock_eq] at h
  have hΨ : ((colmezEquivBlock (K := K) (ι := ι)).symm : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)).comp
      (colmezEquivBlock (K := K) (ι := ι) : c(ι × ℕ, K) →L[K] c(ι × ℕ, K))
        = ContinuousLinearMap.id K c(ι × ℕ, K) :=
    ContinuousLinearMap.ext fun x => (colmezEquivBlock (K := K) (ι := ι)).symm_apply_apply x
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, h,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hΨ,
    ContinuousLinearMap.comp_id]

/-- **[LWX, Proposition 2.17] at `m = 1`**, on the sub-annulus `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹`:
the specialised integral characteristic series `Char(P)(T₀)` of the certificate datum is the
Fredholm determinant `det(1 − X·[UηU])` of `U_p` on the overconvergent forms of the halo weight
(`QMF.Weight.heckeCharPowerSeries` at `haloWeight`, level `U`, untwisted).

Proof: `det(1 − X[UηU]) = det(1 − XP′)` (`charPowerSeries_conj` along `colmezEquivBlock`,
compactoid by `isCompactoid_heckeBlockOp_haloWeight`) `= det(1 − XP(T₀))`
(`charPowerSeries_eq_of_diag_intertwine` with `diagFactorialBlock_comp_colmezConj`)
`= Char(P)(T₀)` (`charPowerSeries_specOp`). -/
theorem specCharSeries_ofCerts_eq_heckeCharPowerSeries (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (intHom ψ) T₀
      = heckeCharPowerSeries (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
          (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
          (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u := by
  have hconj := charPowerSeries_conj (colmezEquivBlock (K := K) (ι := ι)).symm
    (heckeBlockOp (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
      (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
      (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u)
    (isCompactoid_heckeBlockOp_haloWeight ψ T₀ ω θ U hU vRep hvΔ idx u hp2 hψ h0 h1 hshape)
  rw [ContinuousLinearEquiv.symm_symm] at hconj
  have hE := diagFactorialBlock_comp_colmezConj ψ T₀ ω θ U hU vRep hvΔ idx u hp2 hψ h0 h1 hshape
  have hdiag := charPowerSeries_eq_of_diag_intertwine (d := fun a : ι × ℕ => ((a.2 ! : ℕ) : K))
    (fun a => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
    (fun a b => by
      have h := congrArg (fun T => matrixCoeff T a b) hE
      rwa [matrixCoeff_diagFactorialBlock_comp, matrixCoeff_comp_diagFactorialBlock] at h)
  rw [← charPowerSeries_specOp hp2 ψ hψ h0 (norm_lt_one_of_sq_lt h1) ω, ← hdiag, hconj]
  rfl

end Assembly

end LWX

end
