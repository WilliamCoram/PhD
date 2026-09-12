/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.U3.«3_ClassSet»
import PhD.Main.JacobsSlash.U3.«3_EtaDecomposition»
import PhD.Main.JacobsSlash.U3.«4_KappaColumn»

/-!
# Lemmas 2.4/2.5 in certificate form: the nine factorisations (thesis orientation)

[Jacobs, Lemmas 2.4/2.5 + §B.1], in the thesis's own right-handed convention: for each
`(i,t)` the identity

  `classRep i · (etaRep t)⁻¹ = d(i,t) · classRep σ(i,t) · u(i,t)`,  `u(i,t) ∈ U₁(9)`,

in `D_f^×` — exactly the `hfact` shape `heckeOperatorSlash_apply_rep` consumes.  The
`u`-factor is *defined* by the equation (`uCand`), so `factorisation` is true by
construction and the whole certificate content is `uCand_mem : uCand i t ∈ U1_9`.

## Provenance

The tables were computed by `PhD/Main/JacobsSlash/U3/certificate_search.py` (2026-08-06,
exact `ℚ(ν)` arithmetic, unique hit per pair; see its header for the full record):

* `σ(i,·)` = `(2,1,1), (0,2,2), (1,0,0)` — the thesis's table.
* `d(i,t) = ±h/3` with `h ∈ {a, b, c}`, `a = 1+i−j`, `b = (−1+i+3j+k)/2`,
  `c = −(1+3i+j+k)/2` (`nrd h = 3`, so `nrd d = 1/3` — the thesis's own global
  factors; the left library's `d`'s are `3×` these).  The inverse is `d⁻¹ = ±star h`,
  Hurwitz-integral on the nose.
* **The identification is TWIST-FREE**: the `θ₃`-parameters of `(u(i,t)·etaRep t)₃`
  equal the transcribed `ε`-matrices exactly (all nine summands) — the left library's
  classWeight coboundary `κ(s)s⁻²` vanishes identically in the thesis orientation, so
  `sum_weightGenFun_eq_h` below carries NO scalar and [Jac p. 28]
  "the matrix of `U₃` has the form `A = (ε_{i,j})`" holds on the nose.
-/

open TateFredholm JacobsSlash Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/- The three certificate quaternions (same literals as the left library; the fork's
global factors are these over `3`). -/

/-- `a = 1 + i − j` (`nrd = 3`). -/
def dA : D := ⟨1, 1, -1, 0⟩

@[simp] theorem dA_re : dA.re = 1 := rfl
@[simp] theorem dA_imI : dA.imI = 1 := rfl
@[simp] theorem dA_imJ : dA.imJ = -1 := rfl
@[simp] theorem dA_imK : dA.imK = 0 := rfl

/-- `b = (−1 + i + 3j + k)/2` (`nrd = 3`). -/
def dB : D := ⟨-(1/2), 1/2, 3/2, 1/2⟩

@[simp] theorem dB_re : dB.re = -(1/2) := rfl
@[simp] theorem dB_imI : dB.imI = 1/2 := rfl
@[simp] theorem dB_imJ : dB.imJ = 3/2 := rfl
@[simp] theorem dB_imK : dB.imK = 1/2 := rfl

/-- `c = −(1 + 3i + j + k)/2` (`nrd = 3`). -/
def dC : D := ⟨-(1/2), -(3/2), -(1/2), -(1/2)⟩

@[simp] theorem dC_re : dC.re = -(1/2) := rfl
@[simp] theorem dC_imI : dC.imI = -(3/2) := rfl
@[simp] theorem dC_imJ : dC.imJ = -(1/2) := rfl
@[simp] theorem dC_imK : dC.imK = -(1/2) := rfl

/-- The fork's global factor `a/3 = (1 + i − j)/3` (`nrd = 1/3`). -/
def dA3 : D := ⟨1/3, 1/3, -(1/3), 0⟩

@[simp] theorem dA3_re : dA3.re = 1/3 := rfl
@[simp] theorem dA3_imI : dA3.imI = 1/3 := rfl
@[simp] theorem dA3_imJ : dA3.imJ = -(1/3) := rfl
@[simp] theorem dA3_imK : dA3.imK = 0 := rfl

/-- `b/3` (`nrd = 1/3`). -/
def dB3 : D := ⟨-(1/6), 1/6, 1/2, 1/6⟩

@[simp] theorem dB3_re : dB3.re = -(1/6) := rfl
@[simp] theorem dB3_imI : dB3.imI = 1/6 := rfl
@[simp] theorem dB3_imJ : dB3.imJ = 1/2 := rfl
@[simp] theorem dB3_imK : dB3.imK = 1/6 := rfl

/-- `c/3` (`nrd = 1/3`). -/
def dC3 : D := ⟨-(1/6), -(1/2), -(1/6), -(1/6)⟩

@[simp] theorem dC3_re : dC3.re = -(1/6) := rfl
@[simp] theorem dC3_imI : dC3.imI = -(1/2) := rfl
@[simp] theorem dC3_imJ : dC3.imJ = -(1/6) := rfl
@[simp] theorem dC3_imK : dC3.imK = -(1/6) := rfl

/- `(h/3)·(star h) = nrd(h)/3 = 1`: the fork's inverses are the conjugates. -/

theorem dA3_mul_star : dA3 * star dA = 1 := by ext <;> norm_num

theorem star_mul_dA3 : star dA * dA3 = 1 := by ext <;> norm_num

theorem dB3_mul_star : dB3 * star dB = 1 := by ext <;> norm_num

theorem star_mul_dB3 : star dB * dB3 = 1 := by ext <;> norm_num

theorem dC3_mul_star : dC3 * star dC = 1 := by ext <;> norm_num

theorem star_mul_dC3 : star dC * dC3 = 1 := by ext <;> norm_num

/-- The fork's certificate units: `d = h/3` with inverse `star h`. -/
def uA3 : Dˣ := ⟨dA3, star dA, dA3_mul_star, star_mul_dA3⟩

/-- See `uA3`. -/
def uB3 : Dˣ := ⟨dB3, star dB, dB3_mul_star, star_mul_dB3⟩

/-- See `uA3`. -/
def uC3 : Dˣ := ⟨dC3, star dC, dC3_mul_star, star_mul_dC3⟩

@[simp] theorem uA3_val : (uA3 : D) = dA3 := rfl
@[simp] theorem uB3_val : (uB3 : D) = dB3 := rfl
@[simp] theorem uC3_val : (uC3 : D) = dC3 := rfl
@[simp] theorem uA3_inv_val : ((uA3⁻¹ : Dˣ) : D) = star dA := rfl
@[simp] theorem uB3_inv_val : ((uB3⁻¹ : Dˣ) : D) = star dB := rfl
@[simp] theorem uC3_inv_val : ((uC3⁻¹ : Dˣ) : D) = star dC := rfl

/-- The class-index table `σ(i,t)` of the nine factorisations ([Jacobs pp. 26–27]),
computed by the certificate search (module header): the thesis's table on the nose. -/
def sigmaTable : Fin 3 → Fin 3 → Fin 3 := ![![2, 1, 1], ![0, 2, 2], ![1, 0, 0]]

/-- The diagonal never occurs: `σ(i,t) ≠ i` — the source of `ε_{i,i} = 0` and hence
`trace U₃ = 0` [Jacobs, p. 28]. -/
theorem sigmaTable_ne (i t : Fin 3) : sigmaTable i t ≠ i := by decide +revert

/-- The global factor `d(i,t)` of each certificate (oracle rows:
`d(0,·) = (−a, b, c)/3`, `d(1,·) = (a, b, c)/3`, `d(2,·) = (a, −b, −c)/3`). -/
def dTable : Fin 3 → Fin 3 → Dˣ := ![![-uA3, uC3, uB3], ![uA3, uC3, uB3], ![uA3, -uC3, -uB3]]

/-- The certificate factors `d(i,t)`, viewed in `D_f^×`, are global units. -/
theorem dTable_mem (i t : Fin 3) : unitsIncl ℚ D (dTable i t) ∈ globalUnits ℚ D :=
  ⟨dTable i t, rfl⟩

/-- The candidate level factor, *defined* by the factorisation equation: `factorisation`
below is then true by construction and the whole certificate content is `uCand_mem`. -/
noncomputable def uCand (i t : Fin 3) : Dfx ℚ D :=
  (unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t))⁻¹
    * (classRep i * (etaRep t)⁻¹)

/- Hurwitz bookkeeping for the fork's `d = ±h/3` family: the VALUES are `(3⁻¹)•h` with
`h` Hurwitz-integral, and the INVERSES `±star h` are Hurwitz-integral on the nose —
the two away-from-`3` branches swap relative to the left library. -/

theorem dA_mem : dA ∈ hurwitzOrder :=
  ⟨2, 2, -2, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dB_mem : dB ∈ hurwitzOrder :=
  ⟨-1, 1, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dC_mem : dC ∈ hurwitzOrder :=
  ⟨-1, -3, -1, -1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dA_star_mem : star dA ∈ hurwitzOrder :=
  ⟨2, -2, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dB_star_mem : star dB ∈ hurwitzOrder :=
  ⟨-1, -1, -3, -1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dC_star_mem : star dC ∈ hurwitzOrder :=
  ⟨-1, 3, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dA_star_re : (star dA).re = 1 := by norm_num
@[simp] theorem dA_star_imI : (star dA).imI = -1 := by norm_num
theorem dA_star_imJ : (star dA).imJ = 1 := by norm_num
theorem dA_star_imK : (star dA).imK = 0 := by norm_num
theorem dB_star_re : (star dB).re = -(1/2) := by norm_num
theorem dB_star_imI : (star dB).imI = -(1/2) := by norm_num
@[simp] theorem dB_star_imJ : (star dB).imJ = -(3/2) := by norm_num
theorem dB_star_imK : (star dB).imK = -(1/2) := by norm_num
theorem dC_star_re : (star dC).re = -(1/2) := by norm_num
theorem dC_star_imI : (star dC).imI = 3/2 := by norm_num
theorem dC_star_imJ : (star dC).imJ = 1/2 := by norm_num
theorem dC_star_imK : (star dC).imK = 1/2 := by norm_num

/-- The Hurwitz numerators of the fork's global factors. -/
def hTable : Fin 3 → Fin 3 → D := ![![-dA, dC, dB], ![dA, dC, dB], ![dA, -dC, -dB]]

private theorem hTable_mem (i t : Fin 3) : hTable i t ∈ hurwitzOrder := by
  fin_cases i <;> fin_cases t
  exacts [hurwitzOrder.neg_mem dA_mem, dC_mem, dB_mem, dA_mem, dC_mem, dB_mem, dA_mem,
    hurwitzOrder.neg_mem dC_mem, hurwitzOrder.neg_mem dB_mem]

private theorem third_smul_dA : (3⁻¹ : ℚ) • dA = dA3 := by ext <;> norm_num

private theorem third_smul_dB : (3⁻¹ : ℚ) • dB = dB3 := by ext <;> norm_num

private theorem third_smul_dC : (3⁻¹ : ℚ) • dC = dC3 := by ext <;> norm_num

-- The fork's table values are `(3⁻¹) • hTable`.
private theorem dTable_val_smul (i t : Fin 3) :
    ((dTable i t : Dˣ) : D) = (3⁻¹ : ℚ) • hTable i t := by
  have hneg : ∀ {x y : D}, (3⁻¹ : ℚ) • x = y → (3⁻¹ : ℚ) • (-x) = -y :=
    fun h ↦ by rw [smul_neg, h]
  fin_cases i <;> fin_cases t
  exacts [(hneg third_smul_dA).symm, third_smul_dC.symm, third_smul_dB.symm,
    third_smul_dA.symm, third_smul_dC.symm, third_smul_dB.symm, third_smul_dA.symm,
    (hneg third_smul_dC).symm, (hneg third_smul_dB).symm]

-- The fork's table inverses are `±star h` — Hurwitz-integral on the nose.
private theorem dTable_inv_mem (i t : Fin 3) :
    (((dTable i t)⁻¹ : Dˣ) : D) ∈ hurwitzOrder := by
  fin_cases i <;> fin_cases t
  exacts [hurwitzOrder.neg_mem dA_star_mem, dC_star_mem, dB_star_mem, dA_star_mem,
    dC_star_mem, dB_star_mem, dA_star_mem, hurwitzOrder.neg_mem dC_star_mem,
    hurwitzOrder.neg_mem dB_star_mem]

/- Norm bookkeeping over `ℤ[ν₃]`: every matrix entry below is `(X + Y·ν₃)/M`.  The two
workhorses bound and compute such norms from the congruence `ν₃ ≡ 22 mod 27`. -/

private theorem norm_ν₃_sub_22 : ‖ν₃ - 22‖ ≤ ‖(3 : K₃)‖ ^ 3 := by
  refine JacobsSlash.norm_le_of_sub (y := (2673 : K₃)) ?_ ?_
  · rw [show ν₃ - 22 - 2673 = ν₃ - 2695 by ring]
    exact ν₃_near.trans
      (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le (by norm_num))
  · rw [show (2673 : K₃) = (3 : K₃) ^ 3 * 99 by norm_num, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) 3)
      (IsUltrametricDist.norm_natCast_le_one (R := K₃) 99)

private theorem norm_intCast_eq_one_of_not_dvd {m : ℤ} (hm : ¬ (3 : ℤ) ∣ m) :
    ‖(m : K₃)‖ = 1 := by
  rw [← norm_natAbs]
  refine JacobsSlash.norm_natCast_eq_one_of_coprime norm_three_lt_one (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h ↦
      hm (Int.natAbs_dvd_natAbs.mp (by simpa using h))))

private theorem norm_lin_le (X Y m : ℤ) (k : ℕ) (hk : k ≤ 3) (hm : X + 22 * Y = 3 ^ k * m) :
    ‖(X : K₃) + (Y : K₃) * ν₃‖ ≤ ‖(3 : K₃)‖ ^ k := by
  refine JacobsSlash.norm_le_of_sub (y := (X : K₃) + 22 * (Y : K₃)) ?_ ?_
  · rw [show (X : K₃) + (Y : K₃) * ν₃ - ((X : K₃) + 22 * (Y : K₃))
        = (Y : K₃) * (ν₃ - 22) by ring, norm_mul]
    exact ((mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one (R := K₃) Y)).trans norm_ν₃_sub_22).trans
      (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le hk)
  · rw [show (X : K₃) + 22 * (Y : K₃) = (3 : K₃) ^ k * (m : K₃) by exact_mod_cast hm,
      norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) k)
      (IsUltrametricDist.norm_intCast_le_one (R := K₃) m)

private theorem norm_lin_eq (X Y m : ℤ) (k : ℕ) (hk : k ≤ 2) (hm : X + 22 * Y = 3 ^ k * m)
    (hm3 : ¬ (3 : ℤ) ∣ m) : ‖(X : K₃) + (Y : K₃) * ν₃‖ = ‖(3 : K₃)‖ ^ k := by
  have hmain : ‖(X : K₃) + 22 * (Y : K₃)‖ = ‖(3 : K₃)‖ ^ k := by
    rw [show (X : K₃) + 22 * (Y : K₃) = (3 : K₃) ^ k * (m : K₃) by exact_mod_cast hm,
      norm_mul, norm_pow, norm_intCast_eq_one_of_not_dvd hm3, mul_one]
  rw [show (X : K₃) + (Y : K₃) * ν₃
      = ((X : K₃) + 22 * (Y : K₃)) + (Y : K₃) * (ν₃ - 22) by ring, ← hmain]
  refine JacobsSlash.norm_eq_of_sub_lt ?_
  rw [add_sub_cancel_left, norm_mul, hmain]
  exact ((mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_intCast_le_one (R := K₃) Y)).trans norm_ν₃_sub_22).trans_lt
    (pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.mpr (by norm_num)) norm_three_lt_one
      (by omega))

/-- The `v₃`-component matrix of a global unit: `theta_tmul_one` read through
`toMatrix`. -/
theorem toMatrix_unitsIncl (x : Dˣ) :
    toMatrix ℚ D v₃ (unitsIncl ℚ D x)
      = !![algebraMap ℚ K₃ (x : D).re + algebraMap ℚ K₃ (x : D).imI * ν₃
            + algebraMap ℚ K₃ (x : D).imK,
          algebraMap ℚ K₃ (x : D).imI - algebraMap ℚ K₃ (x : D).imJ
            - algebraMap ℚ K₃ (x : D).imK * ν₃;
          algebraMap ℚ K₃ (x : D).imI + algebraMap ℚ K₃ (x : D).imJ
            - algebraMap ℚ K₃ (x : D).imK * ν₃,
          algebraMap ℚ K₃ (x : D).re - algebraMap ℚ K₃ (x : D).imI * ν₃
            - algebraMap ℚ K₃ (x : D).imK] := by
  rw [toMatrix_apply, toLocal_unitsIncl]
  exact theta_tmul_one ν₃ sq_ν₃ (x : D)

-- Away-from-`3` components of the four factors.
private theorem toLocal_classRep_ne (j : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((classRep j : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = 1 := by
  simp [classRep, hw]

private theorem toLocal_classRep_inv_ne (j : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((classRep j)⁻¹ : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 := by
  simp [classRep, hw]

private theorem toLocal_etaRep_ne (t : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((etaRep t : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = 1 := by
  simp [etaRep, levelUnip, eta3, hw]

private theorem toLocal_etaRep_inv_ne (t : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((etaRep t)⁻¹ : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 := by
  simp [etaRep, levelUnip, eta3, hw]

-- Away from `3`, the candidate's component is `d(i,t)⁻¹ = ±star h` (everything else is
-- single-place at `3`) — Hurwitz-integral on the nose.
private theorem toLocal_uCand_ne (i t : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((uCand i t : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = (((dTable i t)⁻¹ : Dˣ) : D) ⊗ₜ[ℚ] 1 := by
  simp only [uCand, mul_inv_rev, ← map_inv (unitsIncl ℚ D), Units.val_mul, map_mul,
    toLocal_classRep_inv_ne _ hw, toLocal_unitsIncl, toLocal_classRep_ne _ hw,
    toLocal_etaRep_inv_ne _ hw, one_mul, mul_one]

-- Away from `3`, the candidate's inverse has component `d(i,t) = (3⁻¹)•h`.
private theorem toLocal_uCand_inv_ne (i t : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((uCand i t)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = ((dTable i t : Dˣ) : D) ⊗ₜ[ℚ] 1 := by
  simp only [uCand, mul_inv_rev, inv_inv, Units.val_mul, map_mul,
    toLocal_etaRep_ne _ hw, toLocal_classRep_inv_ne _ hw, toLocal_unitsIncl,
    toLocal_classRep_ne _ hw, one_mul, mul_one]

-- `((3⁻¹ • e) ⊗ 1` is `w`-integral for Hurwitz `e`, `w ≠ v₃`.
private theorem smul_third_tmul_mem {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) {e : D} (he : e ∈ hurwitzOrder) :
    ((3⁻¹ : ℚ) • e) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ localOrder w := by
  rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  exact tmul_mem_localOrder he ⟨_, inv_three_mem_adicCompletionIntegers hw⟩

-- The away-from-`3` halves of `uCand`'s `U₀(1)`-membership (branches SWAPPED relative
-- to the left library: forward = star-h integral directly; inverse = the (3⁻¹)•h case).
private theorem uCand_away (i t : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((uCand i t : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w ∧
      toLocal ℚ D w (((uCand i t)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w := by
  constructor
  · rw [toLocal_uCand_ne i t hw]
    exact tmul_mem_localOrder (dTable_inv_mem i t) 1
  · rw [toLocal_uCand_inv_ne i t hw, dTable_val_smul]
    exact smul_third_tmul_mem hw (hTable_mem i t)

/- The nine level matrices `E(i,t) = toMatrix (uCand i t)`: transcribed from the
certificate search (`PhD/Main/JacobsSlash/U3/certificate_search.py`, section `LEAN
LITERALS`), in the canonical shape `(X + Y·ν₃)/M` that the norm workhorses consume. -/

private theorem toMatrix_uCand₀₀ :
    toMatrix ℚ D v₃ (uCand 0 0)
      = !![((((-1) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((21 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          0, ((((-1) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 0
      = (unitsIncl ℚ D (-uA3) * classRep 2)⁻¹ * (classRep 0 * (etaRep 0)⁻¹) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uA3_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dA_star_re, dA_star_imI, dA_star_imJ, dA_star_imK,
        map_neg, map_zero, map_one, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, ht, mul_zero, zero_mul, add_zero, zero_add, neg_zero]
      push_cast
      ring

private theorem toMatrix_uCand₀₁ :
    toMatrix ℚ D v₃ (uCand 0 1)
      = !![((((-3) : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃);
          (((11 : ℤ) : K₃) + ((13 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 1
      = (unitsIncl ℚ D (uC3) * classRep 1)⁻¹ * (classRep 0 * (etaRep 1)⁻¹) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC3_inv_val, dC_star_re, dC_star_imI, dC_star_imJ, dC_star_imK, map_neg, map_one, map_div₀, map_ofNat,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₀₂ :
    toMatrix ℚ D v₃ (uCand 0 2)
      = !![((((-38) : ℤ) : K₃) + (((-19) : ℤ) : K₃) * ν₃) / ((30 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃);
          ((((-4) : ℤ) : K₃) + (((-17) : ℤ) : K₃) * ν₃) / ((12 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 2
      = (unitsIncl ℚ D (uB3) * classRep 1)⁻¹ * (classRep 0 * (etaRep 2)⁻¹) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB3_inv_val, dB_star_re, dB_star_imI, dB_star_imJ, dB_star_imK, map_neg, map_one, map_div₀, map_ofNat,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₁₀ :
    toMatrix ℚ D v₃ (uCand 1 0)
      = !![(((5 : ℤ) : K₃) + ((-5 : ℤ) : K₃) * ν₃) / ((3 : ℕ) : K₃),
          (((-4 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((0 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 1 0
      = (unitsIncl ℚ D (uA3) * classRep 0)⁻¹ * (classRep 1 * (etaRep 0)⁻¹) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA3_inv_val, dA_star_re, dA_star_imI, dA_star_imJ, dA_star_imK,
        map_neg, map_zero, map_one, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, Nat.cast_one, ht, mul_zero, zero_mul, add_zero, zero_add, neg_zero]
      push_cast
      ring

private theorem toMatrix_uCand₁₁ :
    toMatrix ℚ D v₃ (uCand 1 1)
      = !![(((-12 : ℤ) : K₃) + ((11 : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((-1 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          (((56 : ℤ) : K₃) + ((49 : ℤ) : K₃) * ν₃) / ((24 : ℕ) : K₃),
          (((-2 : ℤ) : K₃) + ((-3 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 1 1
      = (unitsIncl ℚ D (uC3) * classRep 2)⁻¹ * (classRep 1 * (etaRep 1)⁻¹) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC3_inv_val, dC_star_re, dC_star_imI, dC_star_imJ, dC_star_imK,
        map_neg, map_one, map_div₀, map_ofNat, Int.cast_ofNat,
        Nat.cast_ofNat, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₁₂ :
    toMatrix ℚ D v₃ (uCand 1 2)
      = !![(((-82 : ℤ) : K₃) + ((-41 : ℤ) : K₃) * ν₃) / ((42 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          (((-20 : ℤ) : K₃) + ((-31 : ℤ) : K₃) * ν₃) / ((24 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 1 2
      = (unitsIncl ℚ D (uB3) * classRep 2)⁻¹ * (classRep 1 * (etaRep 2)⁻¹) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB3_inv_val, dB_star_re, dB_star_imI, dB_star_imJ, dB_star_imK,
        map_neg, map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₂₀ :
    toMatrix ℚ D v₃ (uCand 2 0)
      = !![(((7 : ℤ) : K₃) + ((-7 : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃),
          (((-8 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃);
          (((0 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 0
      = (unitsIncl ℚ D (uA3) * classRep 1)⁻¹ * (classRep 2 * (etaRep 0)⁻¹) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA3_inv_val, dA_star_re, dA_star_imI, dA_star_imJ, dA_star_imK,
        map_neg, map_zero, map_one, Int.cast_ofNat,
        Nat.cast_ofNat, Nat.cast_one, ht, mul_zero, zero_mul, add_zero, zero_add, neg_zero]
      push_cast
      ring

private theorem toMatrix_uCand₂₁ :
    toMatrix ℚ D v₃ (uCand 2 1)
      = !![(((24 : ℤ) : K₃) + ((-19 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          (((-4 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((-100 : ℤ) : K₃) + ((-101 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((4 : ℤ) : K₃) + ((6 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 1
      = (unitsIncl ℚ D (-uC3) * classRep 0)⁻¹ * (classRep 2 * (etaRep 1)⁻¹) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uC3_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dC_star_re, dC_star_imI, dC_star_imJ, dC_star_imK,
        map_neg, map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, Nat.cast_one, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₂₂ :
    toMatrix ℚ D v₃ (uCand 2 2)
      = !![(((158 : ℤ) : K₃) + ((79 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((-4 : ℤ) : K₃) + ((-2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((28 : ℤ) : K₃) + ((65 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((-2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 2
      = (unitsIncl ℚ D (-uB3) * classRep 0)⁻¹ * (classRep 2 * (etaRep 2)⁻¹) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uB3_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dB_star_re, dB_star_imI, dB_star_imJ, dB_star_imK,
        map_neg, map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, Nat.cast_one, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

-- `Valued.v x ≤ γ₉` from the norm bound `‖x‖ ≤ ‖3‖²`.
private theorem valued_le_γ₉_of_norm {x : K₃} (h : ‖x‖ ≤ ‖(3 : K₃)‖ ^ 2) :
    Valued.v x ≤ γ₉ := by
  rw [← valued_nine_eq, ← Valued.toNormedField.norm_le_iff]
  rwa [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, ← sq]

-- The full-entry workhorse: `‖(X + Y·ν₃)/M‖ ≤ ‖3‖^T`.
private theorem norm_frac_le (X Y : ℤ) (M T e : ℕ) (m : ℤ) (M' : ℕ) (hTe : T + e ≤ 3)
    (hnum : X + 22 * Y = 3 ^ (T + e) * m) (hM : M = 3 ^ e * M') (hM' : Nat.Coprime M' 3) :
    ‖((X : K₃) + (Y : K₃) * ν₃) / (M : K₃)‖ ≤ ‖(3 : K₃)‖ ^ T := by
  rw [norm_div, JacobsSlash.norm_ofNat_eq_pow norm_three_lt_one hM' hM rfl,
    div_le_iff₀ (pow_pos (norm_pos_iff.mpr (by norm_num : (3 : K₃) ≠ 0)) e), ← pow_add]
  exact norm_lin_le X Y m (T + e) hTe hnum

-- The full-entry workhorse, unit form.
private theorem norm_frac_eq_one (X Y : ℤ) (M e : ℕ) (m : ℤ) (M' : ℕ) (he : e ≤ 2)
    (hnum : X + 22 * Y = 3 ^ e * m) (hm3 : ¬ (3 : ℤ) ∣ m) (hM : M = 3 ^ e * M')
    (hM' : Nat.Coprime M' 3) : ‖((X : K₃) + (Y : K₃) * ν₃) / (M : K₃)‖ = 1 := by
  rw [norm_div, JacobsSlash.norm_ofNat_eq_pow norm_three_lt_one hM' hM rfl,
    norm_lin_eq X Y m e he hnum hm3,
    div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (by norm_num : (3 : K₃) ≠ 0)))]

private theorem det_uCand₀₀ : (toMatrix ℚ D v₃ (uCand 0 0)).det = (1 : K₃) / (28 : K₃) := by
  rw [toMatrix_uCand₀₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1 / 84 : K₃) * sq_ν₃

private theorem int_uCand₀₀ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 0 0)) r c) ≤ 1 := by
  rw [toMatrix_uCand₀₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-1) 1 21 0 1 7 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 0 7 0 0 2 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-1) (-1) 4 0 0 (-23) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₀₀ : toMatrix ℚ D v₃ (uCand 0 0) ∈ Sigma1 := by
  rw [toMatrix_uCand₀₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₀₀] using int_uCand₀₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-1) (-1) 4 0 (-23) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₀, det_uCand₀₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-1) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) : K₃) - 1
        = ((((-5) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-5) (-1) 4 2 0 (-3) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₀ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 0 0)).det) = 1 := by
  rw [det_uCand₀₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₀₁ : (toMatrix ℚ D v₃ (uCand 0 1)).det = (1 : K₃) / (10 : K₃) := by
  rw [toMatrix_uCand₀₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1/12 : K₃) * sq_ν₃

private theorem int_uCand₀₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 0 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₀₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-3) (2) 5 0 0 (41) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (-1) 10 0 0 (-20) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (11) (13) 6 0 1 (99) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-3) 4 0 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₀₁ : toMatrix ℚ D v₃ (uCand 0 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₀₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₀₁] using int_uCand₀₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (11) (13) 6 2 1 (11) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-2) (-3) 4 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₁, det_uCand₀₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((-2 : ℤ) : K₃) + ((-3 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) : K₃) - 1
        = (((-6 : ℤ) : K₃) + ((-3 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-6) (-3) 4 2 0 (-8) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₁ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 0 1)).det) = 1 := by
  rw [det_uCand₀₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₀₂ : (toMatrix ℚ D v₃ (uCand 0 2)).det = (1 : K₃) / (10 : K₃) := by
  rw [toMatrix_uCand₀₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1/60 : K₃) * sq_ν₃

private theorem int_uCand₀₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 0 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₀₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-38) (-19) 30 0 1 (-152) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (1) 10 0 0 (24) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (-17) 12 0 1 (-126) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (0) (1) 4 0 0 (22) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₀₂ : toMatrix ℚ D v₃ (uCand 0 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₀₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₀₂] using int_uCand₀₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-4) (-17) 12 2 1 (-14) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (0) (1) 4 0 (22) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₂, det_uCand₀₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) : K₃) - 1
        = (((-4 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-4) (1) 4 2 0 (2) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₂ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 0 2)).det) = 1 := by
  rw [det_uCand₀₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₀ : (toMatrix ℚ D v₃ (uCand 1 0)).det = (10 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₁₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-10/3 : K₃) * sq_ν₃

private theorem int_uCand₁₀ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 0)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (5) (-5) 3 0 1 (-35) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (0) 1 0 0 (-4) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (2) 1 0 0 (46) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₀ : toMatrix ℚ D v₃ (uCand 1 0) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₀] using int_uCand₁₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (2) (2) 1 0 (46) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₀, det_uCand₁₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) : K₃) - 1
        = (((1 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (1) (2) 1 2 0 (5) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₀ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 1 0)).det) = 1 := by
  rw [det_uCand₁₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₁ : (toMatrix ℚ D v₃ (uCand 1 1)).det = (5 : K₃) / (14 : K₃) := by
  rw [toMatrix_uCand₁₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-25/84 : K₃) * sq_ν₃

private theorem int_uCand₁₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-12) (11) 14 0 0 (230) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (-1) 7 0 0 (-20) 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (56) (49) 24 0 1 (378) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-3) 4 0 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₁ : toMatrix ℚ D v₃ (uCand 1 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₁] using int_uCand₁₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (56) (49) 24 2 1 (42) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-2) (-3) 4 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₁, det_uCand₁₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((-2 : ℤ) : K₃) + ((-3 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) : K₃) - 1
        = (((-6 : ℤ) : K₃) + ((-3 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-6) (-3) 4 2 0 (-8) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₁ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 1 1)).det) = 1 := by
  rw [det_uCand₁₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₂ : (toMatrix ℚ D v₃ (uCand 1 2)).det = (5 : K₃) / (14 : K₃) := by
  rw [toMatrix_uCand₁₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-5/84 : K₃) * sq_ν₃

private theorem int_uCand₁₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-82) (-41) 42 0 1 (-328) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (1) 7 0 0 (24) 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-20) (-31) 24 0 1 (-234) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (0) (1) 4 0 0 (22) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₂ : toMatrix ℚ D v₃ (uCand 1 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₂] using int_uCand₁₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-20) (-31) 24 2 1 (-26) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (0) (1) 4 0 (22) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₂, det_uCand₁₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) : K₃) - 1
        = (((-4 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-4) (1) 4 2 0 (2) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₂ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 1 2)).det) = 1 := by
  rw [det_uCand₁₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₀ : (toMatrix ℚ D v₃ (uCand 2 0)).det = (14 : K₃) / (5 : K₃) := by
  rw [toMatrix_uCand₂₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-14/15 : K₃) * sq_ν₃

private theorem int_uCand₂₀ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 0)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (7) (-7) 15 0 1 (-49) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-8) (0) 5 0 0 (-8) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (2) (2) 1 0 0 (46) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₀ : toMatrix ℚ D v₃ (uCand 2 0) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₀] using int_uCand₂₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (2) (2) 1 0 (46) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₀, det_uCand₂₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) : K₃) - 1
        = (((1 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (1) (2) 1 2 0 (5) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₀ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 2 0)).det) = 1 := by
  rw [det_uCand₂₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₁ : (toMatrix ℚ D v₃ (uCand 2 1)).det = (28 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₂₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-70/3 : K₃) * sq_ν₃

private theorem int_uCand₂₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (24) (-19) 2 0 0 (-394) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (2) 1 0 0 (40) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-100) (-101) 6 0 1 (-774) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (4) (6) 1 0 0 (136) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₁ : toMatrix ℚ D v₃ (uCand 2 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₁] using int_uCand₂₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-100) (-101) 6 2 1 (-86) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (4) (6) 1 0 (136) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₁, det_uCand₂₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((4 : ℤ) : K₃) + ((6 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) : K₃) - 1
        = (((3 : ℤ) : K₃) + ((6 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (3) (6) 1 2 0 (15) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₁ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 2 1)).det) = 1 := by
  rw [det_uCand₂₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₂ : (toMatrix ℚ D v₃ (uCand 2 2)).det = (28 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₂₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-14/3 : K₃) * sq_ν₃

private theorem int_uCand₂₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (158) (79) 6 0 1 (632) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (-2) 1 0 0 (-48) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (28) (65) 6 0 1 (486) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (0) (-2) 1 0 0 (-44) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₂ : toMatrix ℚ D v₃ (uCand 2 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₂] using int_uCand₂₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (28) (65) 6 2 1 (54) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (0) (-2) 1 0 (-44) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₂, det_uCand₂₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + ((-2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) : K₃) - 1
        = (((-1 : ℤ) : K₃) + ((-2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
      push_cast
      ring]
    exact norm_frac_le (-1) (-2) 1 2 0 (-5) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₂ :
    Valued.v ((toMatrix ℚ D v₃ (uCand 2 2)).det) = 1 := by
  rw [det_uCand₂₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), JacobsSlash.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

-- A two-sided inverse of an integral matrix with unit determinant is entrywise
-- integral.
private theorem valued_inv_entries_le {M N : Matrix (Fin 2) (Fin 2) K₃}
    (hM : ∀ r c, Valued.v (M r c) ≤ 1) (hdet : Valued.v M.det = 1)
    (h1 : M * N = 1) : ∀ r c, Valued.v (N r c) ≤ 1 := by
  intro r c
  rw [← Matrix.inv_eq_right_inv h1, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    map_mul, Ring.inverse_eq_inv', map_inv₀, hdet, inv_one, one_mul,
    Matrix.adjugate_fin_two]
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Valuation.map_neg]
  exacts [hM 1 1, hM 0 1, hM 1 0, hM 0 0]

/-- **The certificate content**: every candidate lies in `U₁(9)`.  Away from `3` the
component is `±star h` (Hurwitz) resp. `±h/3` (integral there); at `3` the nine
`Σ₁(9)`-certificates above apply, and the inverse's conditions follow by
`sigma1_of_mul_eq_one`. -/
theorem uCand_mem : ∀ i t : Fin 3, uCand i t ∈ U1_9 := by
  intro i t
  have hmul1 : toMatrix ℚ D v₃ (uCand i t) * toMatrix ℚ D v₃ (uCand i t)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hmul2 : toMatrix ℚ D v₃ (uCand i t)⁻¹ * toMatrix ℚ D v₃ (uCand i t) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hsig : toMatrix ℚ D v₃ (uCand i t) ∈ Sigma1 := by
    fin_cases i <;> fin_cases t
    exacts [sigma1_uCand₀₀, sigma1_uCand₀₁, sigma1_uCand₀₂, sigma1_uCand₁₀,
      sigma1_uCand₁₁, sigma1_uCand₁₂, sigma1_uCand₂₀, sigma1_uCand₂₁, sigma1_uCand₂₂]
  have hdet1 : Valued.v ((toMatrix ℚ D v₃ (uCand i t)).det) = 1 := by
    fin_cases i <;> fin_cases t
    exacts [valued_det_uCand₀₀, valued_det_uCand₀₁, valued_det_uCand₀₂, valued_det_uCand₁₀,
      valued_det_uCand₁₁, valued_det_uCand₁₂, valued_det_uCand₂₀, valued_det_uCand₂₁,
      valued_det_uCand₂₂]
  have hint' : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand i t)⁻¹) r c) ≤ 1 :=
    valued_inv_entries_le (fun r c => hsig.1.1 r c) hdet1 hmul1
  refine mem_U1_9_of_toMatrix (fun w hw => uCand_away i t hw) ?_
    (mem_integralMatrices_iff.mpr fun r c => hint' r c) hsig
    (sigma1_of_mul_eq_one hsig hint' hmul1 hmul2)
  exact mem_integralMatrices_iff.mpr fun r c => hsig.1.1 r c

/-- **The nine certificates** [Jacobs, Lemmas 2.4/2.5, pp. 26–27, §B.1], in the
thesis's own shape: `cᵢ · vₜ⁻¹ = d(i,t) · c_{σ(i,t)} · u(i,t)` in `D_f^×` — true by
construction of `uCand`. -/
theorem factorisation (i t : Fin 3) :
    classRep i * (etaRep t)⁻¹
      = unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t) * uCand i t := by
  rw [uCand]
  group

/-- The level factors as `U₁(9)`-elements: the table `u(i,t) = ⟨uCand i t, uCand_mem⟩`. -/
noncomputable def uTable : Fin 3 → Fin 3 → U1_9 := fun i t => ⟨uCand i t, uCand_mem i t⟩

/-- The class determinants `det cᵢ = dᵢ·eᵢ ∈ {1, 10, 28}`. -/
def classDet (i : Fin 3) : ℤ := (classDiag i).1 * (classDiag i).2

theorem cd0 : ((classDet (0 : Fin 3) : ℤ) : K₃) = 1 :=
  mod_cast show classDet (0 : Fin 3) = 1 by decide

theorem cd1 : ((classDet (1 : Fin 3) : ℤ) : K₃) = 10 :=
  mod_cast show classDet (1 : Fin 3) = 10 by decide

theorem cd2 : ((classDet (2 : Fin 3) : ℤ) : K₃) = 28 :=
  mod_cast show classDet (2 : Fin 3) = 28 by decide

/-- The transcribed `ε`-matrix acting at `(i, t)` — arranged so that
`epsTable i t` is the `ε`-member the certificate `(i,t)` realises (in the thesis
orientation the `t`-columns meet the members IN ORDER: `t = 1 ↦ M1`, `t = 2 ↦ M2`). -/
noncomputable def epsTable : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) K₃ :=
  ![![JacobsSlash.eps02M ν₃, JacobsSlash.eps01M1 ν₃, JacobsSlash.eps01M2 ν₃],
    ![JacobsSlash.eps10M ν₃, JacobsSlash.eps12M1 ν₃, JacobsSlash.eps12M2 ν₃],
    ![JacobsSlash.eps21M ν₃, JacobsSlash.eps20M1 ν₃, JacobsSlash.eps20M2 ν₃]]

private theorem acting₀₀ :
    toMatrix ℚ D v₃ (uCand 0 0 * etaRep 0) = JacobsSlash.eps02M ν₃ := by
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [map_mul, toMatrix_uCand₀₀, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps02M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₀₁ :
    toMatrix ℚ D v₃ (uCand 0 1 * etaRep 1) = JacobsSlash.eps01M1 ν₃ := by
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [map_mul, toMatrix_uCand₀₁, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps01M1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₀₂ :
    toMatrix ℚ D v₃ (uCand 0 2 * etaRep 2) = JacobsSlash.eps01M2 ν₃ := by
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [map_mul, toMatrix_uCand₀₂, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps01M2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₁₀ :
    toMatrix ℚ D v₃ (uCand 1 0 * etaRep 0) = JacobsSlash.eps10M ν₃ := by
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [map_mul, toMatrix_uCand₁₀, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps10M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₁₁ :
    toMatrix ℚ D v₃ (uCand 1 1 * etaRep 1) = JacobsSlash.eps12M1 ν₃ := by
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [map_mul, toMatrix_uCand₁₁, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps12M1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₁₂ :
    toMatrix ℚ D v₃ (uCand 1 2 * etaRep 2) = JacobsSlash.eps12M2 ν₃ := by
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [map_mul, toMatrix_uCand₁₂, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps12M2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₂₀ :
    toMatrix ℚ D v₃ (uCand 2 0 * etaRep 0) = JacobsSlash.eps21M ν₃ := by
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [map_mul, toMatrix_uCand₂₀, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps21M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₂₁ :
    toMatrix ℚ D v₃ (uCand 2 1 * etaRep 1) = JacobsSlash.eps20M1 ν₃ := by
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [map_mul, toMatrix_uCand₂₁, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps20M1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

private theorem acting₂₂ :
    toMatrix ℚ D v₃ (uCand 2 2 * etaRep 2) = JacobsSlash.eps20M2 ν₃ := by
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [map_mul, toMatrix_uCand₂₂, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [JacobsSlash.eps20M2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.isValue, ht]
      push_cast
      field_simp
      ring

/-- **The `ε`-matrix identification, matrix level — TWIST-FREE**: the parameters of the
acting element `u(i,t)·vₜ` of certificate `(i,t)` are the transcribed `ε`-matrix ON THE
NOSE — no adjugate, no determinant-ratio scalar (machine-verified by
`certificate_search.py`; the left library's classWeight coboundary vanishes identically
in the thesis orientation). -/
theorem toMatrix_eq_epsTable (i t : Fin 3) :
    toMatrix ℚ D v₃ ((uTable i t : Dfx ℚ D) * etaRep t) = epsTable i t := by
  fin_cases i <;> fin_cases t <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, epsTable, uTable,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  exacts [acting₀₀, acting₀₁, acting₀₂, acting₁₀, acting₁₁, acting₁₂, acting₂₀,
    acting₂₁, acting₂₂]

@[simp] theorem uTable_coe (i t : Fin 3) : ((uTable i t : U1_9) : Dfx ℚ D) = uCand i t :=
  rfl

/-- **The `ε`-identification, series level — NO SCALAR** (the form `6_Matrix` consumes):
for each `(i, j)` with `j ≠ i`, the sum of `weightGenFun tw` over the acting matrices of
`{t' | σ(i,t') = j}` is the transcribed block generating function `h_{i,j}` of
`PhD.Main.JacobsSlash.«2_U3Data»` ON THE NOSE.  In the thesis orientation the left library's
handedness scalar `κ(s)s⁻²` is identically `1`, so no weight hypothesis is needed and
[Jac p. 28] "the matrix of `U₃` will have the form `A = (ε_{i,j})`" holds exactly. -/
theorem sum_weightGenFun_eq_h (tw : K₃) (i j : Fin 3) (hij : j ≠ i) :
    ∑ t' ∈ {t' | sigmaTable i t' = j},
        JacobsSlash.weightGenFun tw
          (toMatrix ℚ D v₃ ((uTable i t' : Dfx ℚ D) * etaRep t'))
      = ![![0, JacobsSlash.h01 tw ν₃, JacobsSlash.h02 tw ν₃],
          ![JacobsSlash.h10 tw ν₃, 0, JacobsSlash.h12 tw ν₃],
          ![JacobsSlash.h20 tw ν₃, JacobsSlash.h21 tw ν₃, 0]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, uTable_coe,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    try exact absurd rfl hij
  · rw [show ({t' | sigmaTable 0 t' = 1} : Finset (Fin 3)) = {1, 2} by decide,
      Finset.sum_pair (by decide), acting₀₁, acting₀₂, JacobsSlash.h01]
  · rw [show ({t' | sigmaTable 0 t' = 2} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, acting₀₀, JacobsSlash.h02]
    rfl
  · rw [show ({t' | sigmaTable 1 t' = 0} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, acting₁₀, JacobsSlash.h10]
  · rw [show ({t' | sigmaTable 1 t' = 2} : Finset (Fin 3)) = {1, 2} by decide,
      Finset.sum_pair (by decide), acting₁₁, acting₁₂, JacobsSlash.h12]
    rfl
  · rw [show ({t' | sigmaTable 2 t' = 0} : Finset (Fin 3)) = {1, 2} by decide,
      Finset.sum_pair (by decide), acting₂₁, acting₂₂, JacobsSlash.h20]
    rfl
  · rw [show ({t' | sigmaTable 2 t' = 1} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, acting₂₀, JacobsSlash.h21]
    rfl

end JacobsSlash
