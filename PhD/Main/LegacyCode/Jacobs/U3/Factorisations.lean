/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.ClassSet
import PhD.Jacobs.U3.EtaDecomposition
import PhD.Jacobs.U3.KappaAction

/-!
# Lemmas 2.4/2.5 in certificate form: the nine factorisations

[Jacobs, pp. 25–27 and §B.1 pp. 44–48].  The thesis's Lemmas 2.4 ("There exists `d ∈ D`
such that `d⁻¹cᵢv_t⁻¹ ∈ U₀(1)`") and 2.5 ("Given `ũ ∈ U₀(1)` there exist `ε ∈ 𝓞_D^×`,
`i ∈ I` and `u ∈ U` such that `ũ = εcᵢu`") are the *search algorithm* that produced the
nine explicit factorisations tabulated on pp. 26–27 (PARI implementation §B.1):

> "c₀v₀⁻¹ = (−1/3 − 1/3 i + 1/3 j) (7 0; 0 4) (1/21 ν₃ − 1/21, 2/7; 0, −1/4 ν₃ − 1/4)"

(and eight more).  **Planning decision** (recorded in `decomposition.md` R4): we
formalise the *certificates* — the nine verified identities with their membership
side-conditions — not the search.  Each certificate consists of

* a global quaternion `d(i,t)` (a Hurwitz-order unit after clearing the norm-`3ᵏ`
  factor), the class index `σ(i,t)`, and a level element `u(i,t) ∈ U₁(9)`;
* the identity `classRep i · etaRep t = d(i,t) · classRep (σ(i,t)) · u(i,t)` in `D_f^×`,
  checked at `3` through `θ₃` (arithmetic over `ℚ(ν₃)` with `ν₃² = −2`) and away from
  `3` by integrality of `d(i,t)`;
* membership `u(i,t) ∈ U₁(9)`, from the entry-integrality and mod-`9` congruences
  (which need `ν₃ mod 27`-precision, supplied by `ν₃_near`).

The tables are *recomputed* during proof (the extraction of the thesis PDF loses signs;
and the p. 28 `ε₁,₂` misprint — `.mathlib-quality/jacobs/decomposition.md`, adversarial
finding 1 — was caught exactly this way).  The `t`-indexing below refers to our
left-coset representatives `etaRep`, which differ from the thesis's `v_t` by the
adjugate transport; the concrete value tables are fixed at ticket time.

## Why certificates suffice (design note)

The thesis's Lemmas 2.4/2.5 are *existence* statements; a certificate is a *witness*, and
a witness discharges an existence obligation.  Since the endpoint
(`Jacobs.U3.heckeU3_apply_classRep`) is a per-`(i,t)` computation — it needs, for each of
the nine pairs, *some* factorisation with `d ∈ Γ` and `u ∈ U₁(9)` — the search algorithm
is never consumed downstream.  Note also that `d` ranges over all of `Dˣ` (`Γ` is the
image of `Dˣ`, and `D` is a division algebra), so Lemma 2.5's `ε ∈ 𝓞_D^×` is an artifact
of the *search*, not of the result.

Two things certificates do **not** give, both split off as their own tickets: uniqueness
of `σ(i,t)` (that is Theorem 2.1's disjointness — needed only for the completeness half,
`eval_classRep_injective`, and gated on `HClassNumberOne`), and exhaustiveness of the
`etaRep t` (that is Lemma 2.3, `EtaDecomposition.lean`).

**Self-forcing design (binding for the tickets).**  A certificate asserting an identity
between three *guessed* objects is fragile — the thesis has at least one known misprint.
So only `dTable` and `sigmaTable` are guessed (seven rationals and an index per pair); the
level factor is *defined* by `u := (d · c_σ)⁻¹ · cᵢ · wₜ`, which makes `factorisation`
true by construction and collapses the entire mathematical content into the single side
condition `u ∈ U₁(9)` — a valuation check on four entries, needing `ν₃ mod 27` (supplied
by `Setting.ν₃_near`).  Contingency if a guessed `d` is wrong: `d` is determined only up
to `𝓞_D^×` (24 elements) and the class index (3), so the fallback is a 72-case finite
search, not a re-derivation of Lemmas 2.4/2.5.

## Handedness

Jacobs factorises `cᵢ v_t⁻¹` (right-action convention); we factorise `classRep i · etaRep t`
(left).  The tables are therefore the *adjugate transports* of the thesis's, and must be
recomputed rather than copied — see `PhD/Main/QMF/00_Sigma0.lean`'s header for why the library is
left-handed and why the adjugate is the standard dictionary.

## The computed tables (2026-08-05): see `certificate_search.py`

The certificates were found by `certificate_search.py` (this directory, pure-stdlib
Python, < 1 s): the determinant bookkeeping forces `nrd d = 3`, so per pair the search
is exhaustive over the 96 norm-`3` Hurwitz quaternions × 3 class indices, with the
`u ∈ U₁(9)` membership checked through `θ₃` in exact `ℚ(ν)` arithmetic at
`ν ≡ 2695 mod 3¹⁰`.  Exactly one `(σ, d)` passed per pair — the uniqueness Lemma 2.2
(`Γᵢ = 1`) and Theorem 2.1's disjointness predict.  The values (script docstring has
the full nine-line table):

* `sigmaTable` = `(2,1,1), (0,2,2), (1,0,0)` (rows `i`, cols `t`) — the thesis's table
  on the nose, `σ(i,t) ≠ i` throughout;
* `dTable`: with `a = 1 + i − j`, `b = (−1 + i + 3j + k)/2`, `c = −(1 + 3i + j + k)/2`
  (all `nrd = 3`), the rows are `d(0,·) = (−a, b, c)`, `d(1,·) = (a, b, c)`,
  `d(2,·) = (a, −b, −c)`.

Cross-checks: `d(0,0) = 3·d_thesis` and `u(0,0)` is literally the printed third factor
of the thesis's p. 26 example; and the `ε`-identification closes **exactly**, in the form
`ε_{i,j}(t') = θ₃ (c_j⁻¹ · star (d(i,t')) · cᵢ)` for all nine summands — confirming the
E1-corrected `eps12M2` (the misprinted `−15/14` entry occurs nowhere).

**Handedness normalisation (B15 statement amendment, applied 2026-08-05).**  The
left-handed parameter matrices differ from the transcribed `ε`'s by a scalar:
`adjParams (θ₃ (etaRep t' · u(i,t')⁻¹)) = (classDet σ(i,t') / classDet i) • ε_{i,j}(t')`,
a `1`-unit since `classDet ∈ {1, 10, 28}` are all `≡ 1 mod 9`.  Per B15's binding
determinant-twist audit this is a *recorded statement amendment*: the identification is
stated in two layers — the matrix-level identity `adjParams_toMatrix_eq_smul_epsTable`
(the exact certificate content, against the assignment table `epsTable`), and the
series-level corollary `sum_weightGenFun_eq_h`, which now carries the factor
`κ(s)·s⁻²` with `s = classDet j / classDet i` and follows from the matrix layer by
`Jacobs.weightGenFun_smul` and summing the fibre `{t' | σ(i,t') = j}`.

**Why the twist is harmless (resolution, recorded 2026-08-05).**  The scalar carried by
block `(i, j)` is a *coboundary*: it factors as `φⱼ/φᵢ` with `φₖ = κ(dₖ)·dₖ⁻²`,
`dₖ = classDet k` (`Jacobs.U3.twist_factor`, three `unitPow_mul` applications).  The
certificate-assembled block matrix is therefore *conjugate* to the transcribed one by
the blockwise-scalar diagonal `diag (φₖ)` — not merely a rescaling of it — and
conjugation preserves the characteristic power series on the nose
(`TateFredholm.charPowerSeries_blockOp_twist`; instantiated at `U₃` as
`Jacobs.U3.charPowerSeries_blockOp_eq_U3MatrixOp` in `U3/Matrix.lean`).  So AG-W's
slope analysis of `Jacobs.U3MatrixOp` — Fredholm determinant, eigenvalues, Newton
polygon — applies verbatim to the operator the certificates actually produce; a
non-coboundary scalar (one with a nontrivial closed cycle product) is the only kind
that could have moved a slope.  Independently, each scalar is a `1`-unit, so no matrix
entry changes norm and the norm-driven slope machinery (`PhD.Jacobs.SlopeTheorem`) is
blind to the twist regardless.

## Main definitions

* `Jacobs.U3.sigmaTable`, `Jacobs.U3.dTable`, `Jacobs.U3.uTable`: the nine certificates —
  the class index `σ(i,t)`, the global quaternion `d(i,t)`, and the level element
  `u(i,t) ∈ U₁(9)` (the last *defined* by the factorisation equation, not guessed).
* `Jacobs.U3.classDet`: the determinant `dᵢeᵢ ∈ {1, 10, 28}` of `θ₃(classRep i)`, whose
  ratios are the handedness scalars above.
* `Jacobs.U3.epsTable`: the transcribed `ε`-matrix acting at `(i, t')`, in the
  `t'`-assignment the certificate search produced.

## Main results

* `Jacobs.U3.factorisation`: **the nine certificates**,
  `classRep i · etaRep t = d(i,t) · classRep (σ(i,t)) · u(i,t)` in `D_f^×`.
* `Jacobs.U3.sigmaTable_ne`: `σ(i,t) ≠ i` — the source of `ε_{i,i} = 0`, hence
  `trace U₃ = 0`.
* `Jacobs.U3.toMatrix_etaRep_mul_inv_uTable_mem_sigma1`: the acting matrices lie in
  `Σ₁(9)`, so they act through the weight-`κ` theory.
* `Jacobs.U3.adjParams_toMatrix_eq_smul_epsTable`, `Jacobs.U3.sum_weightGenFun_eq_h`:
  the `ε`-identification at matrix and series level — the two layers of the recorded
  B15 amendment.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

/- See `Setting.lean`: the adic `Algebra ℚ K₃` path is the one the `QMF` framework uses;
pinning it keeps `theta`'s domain syntactically equal to the tensors appearing here. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace Jacobs.U3

/- The `dTable` below is built from three quaternions up to sign (module header):
`a = 1 + i − j`, `b = (−1 + i + 3j + k)/2`, `c = −(1 + 3i + j + k)/2`, all of reduced
norm `3` and Hurwitz-integral.  Their inverses are `star/3`, recorded as literals
(`dAi`, `dBi`, `dCi`) so that every downstream matrix entry is explicit. -/

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

/-- `a⁻¹ = (1 − i + j)/3`. -/
def dAi : D := ⟨1/3, -(1/3), 1/3, 0⟩

@[simp] theorem dAi_re : dAi.re = 1/3 := rfl
@[simp] theorem dAi_imI : dAi.imI = -(1/3) := rfl
@[simp] theorem dAi_imJ : dAi.imJ = 1/3 := rfl
@[simp] theorem dAi_imK : dAi.imK = 0 := rfl

/-- `b⁻¹ = (−1 − i − 3j − k)/6`. -/
def dBi : D := ⟨-(1/6), -(1/6), -(1/2), -(1/6)⟩

@[simp] theorem dBi_re : dBi.re = -(1/6) := rfl
@[simp] theorem dBi_imI : dBi.imI = -(1/6) := rfl
@[simp] theorem dBi_imJ : dBi.imJ = -(1/2) := rfl
@[simp] theorem dBi_imK : dBi.imK = -(1/6) := rfl

/-- `c⁻¹ = (−1 + 3i + j + k)/6`. -/
def dCi : D := ⟨-(1/6), 1/2, 1/6, 1/6⟩

@[simp] theorem dCi_re : dCi.re = -(1/6) := rfl
@[simp] theorem dCi_imI : dCi.imI = 1/2 := rfl
@[simp] theorem dCi_imJ : dCi.imJ = 1/6 := rfl
@[simp] theorem dCi_imK : dCi.imK = 1/6 := rfl

theorem dA_mul_dAi : dA * dAi = 1 := by ext <;> norm_num

theorem dB_mul_dBi : dB * dBi = 1 := by ext <;> norm_num

theorem dC_mul_dCi : dC * dCi = 1 := by ext <;> norm_num

theorem dAi_mul_dA : dAi * dA = 1 := by ext <;> norm_num

theorem dBi_mul_dB : dBi * dB = 1 := by ext <;> norm_num

theorem dCi_mul_dC : dCi * dC = 1 := by ext <;> norm_num

/-- The certificate quaternions as units of the division ring `D`. -/
def uA : Dˣ := ⟨dA, dAi, dA_mul_dAi, dAi_mul_dA⟩

/-- See `uA`. -/
def uB : Dˣ := ⟨dB, dBi, dB_mul_dBi, dBi_mul_dB⟩

/-- See `uA`. -/
def uC : Dˣ := ⟨dC, dCi, dC_mul_dCi, dCi_mul_dC⟩

@[simp] theorem uA_val : (uA : D) = dA := rfl
@[simp] theorem uB_val : (uB : D) = dB := rfl
@[simp] theorem uC_val : (uC : D) = dC := rfl
@[simp] theorem uA_inv_val : ((uA⁻¹ : Dˣ) : D) = dAi := rfl
@[simp] theorem uB_inv_val : ((uB⁻¹ : Dˣ) : D) = dBi := rfl
@[simp] theorem uC_inv_val : ((uC⁻¹ : Dˣ) : D) = dCi := rfl

theorem dA_mem : dA ∈ hurwitzOrder :=
  ⟨2, 2, -2, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dB_mem : dB ∈ hurwitzOrder :=
  ⟨-1, 1, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

theorem dC_mem : dC ∈ hurwitzOrder :=
  ⟨-1, -3, -1, -1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- The inverses are `star/3`: `3 • dAi = star dA`, and likewise for `b`, `c` — the form
the away-from-`3` integrality argument consumes. -/
theorem three_smul_dAi : (3 : ℚ) • dAi = star dA := by ext <;> simp

theorem three_smul_dBi : (3 : ℚ) • dBi = star dB := by ext <;> norm_num

theorem three_smul_dCi : (3 : ℚ) • dCi = star dC := by ext <;> norm_num

/-- The class-index table `σ(i,t)` of the nine factorisations ([Jacobs pp. 26–27]),
computed by the certificate search (module header): `σ(0,·) = (2,1,1)`,
`σ(1,·) = (0,2,2)`, `σ(2,·) = (1,0,0)` — the thesis's right-handed table on the nose. -/
def sigmaTable : Fin 3 → Fin 3 → Fin 3 := ![![2, 1, 1], ![0, 2, 2], ![1, 0, 0]]

/-- The diagonal never occurs: `σ(i,t) ≠ i` — the source of `ε_{i,i} = 0` and hence
`trace U₃ = 0` [Jacobs, p. 28: "noticing that ε_{i,i} = 0 … the trace of U₃ is zero"]. -/
theorem sigmaTable_ne (i t : Fin 3) : sigmaTable i t ≠ i := by decide +revert

/-- The global factor `d(i,t)` of each certificate, as a unit of `D`: the rows are
`(−a, b, c)`, `(a, b, c)`, `(a, −b, −c)` in the three certificate quaternions
(computed by the search, module header). -/
def dTable : Fin 3 → Fin 3 → Dˣ := ![![-uA, uB, uC], ![uA, uB, uC], ![uA, -uB, -uC]]

/-- The certificate factors `d(i,t)`, viewed in `D_f^×`, are global units. -/
theorem dTable_mem (i t : Fin 3) : unitsIncl ℚ D (dTable i t) ∈ globalUnits ℚ D :=
  ⟨dTable i t, rfl⟩

-- The values of `dTable` are Hurwitz-integral.
private theorem dTable_val_mem (i t : Fin 3) : ((dTable i t : Dˣ) : D) ∈ hurwitzOrder := by
  fin_cases i <;> fin_cases t
  exacts [hurwitzOrder.neg_mem dA_mem, dB_mem, dC_mem, dA_mem, dB_mem, dC_mem, dA_mem,
    hurwitzOrder.neg_mem dB_mem, hurwitzOrder.neg_mem dC_mem]

-- The inverse of each table entry is `star/3` — the shape the away-from-`3`
-- integrality argument consumes.
private theorem dTable_inv_val (i t : Fin 3) :
    (((dTable i t)⁻¹ : Dˣ) : D) = (3⁻¹ : ℚ) • star ((dTable i t : Dˣ) : D) := by
  have hA : dAi = (3⁻¹ : ℚ) • star dA := by norm_num [← three_smul_dAi, smul_smul]
  have hB : dBi = (3⁻¹ : ℚ) • star dB := by norm_num [← three_smul_dBi, smul_smul]
  have hC : dCi = (3⁻¹ : ℚ) • star dC := by norm_num [← three_smul_dCi, smul_smul]
  have hneg : ∀ {x y : D}, x = (3⁻¹ : ℚ) • star y → -x = (3⁻¹ : ℚ) • star (-y) :=
    fun h ↦ by rw [star_neg, smul_neg, h]
  fin_cases i <;> fin_cases t
  exacts [hneg hA, hB, hC, hA, hB, hC, hA, hneg hB, hneg hC]

/- Norm bookkeeping over `ℤ[ν₃]`: every matrix entry below is `(X + Y·ν₃)/M` with
`X, Y, M ∈ ℤ`.  The two workhorses bound and compute such norms from the congruence
`ν₃ ≡ 22 mod 27` (itself from `ν₃ ≡ 2695 mod 3¹⁰`, `2673 = 3³·99`): a `3`-adic
divisibility of `X + 22·Y`, checked by `norm_num`, is the entire input. -/

private theorem norm_ν₃_sub_22 : ‖ν₃ - 22‖ ≤ ‖(3 : K₃)‖ ^ 3 := by
  refine Jacobs.norm_le_of_sub (y := (2673 : K₃)) ?_ ?_
  · rw [show ν₃ - 22 - 2673 = ν₃ - 2695 by ring]
    exact ν₃_near.trans
      (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le (by norm_num))
  · rw [show (2673 : K₃) = (3 : K₃) ^ 3 * 99 by norm_num, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) 3)
      (IsUltrametricDist.norm_natCast_le_one (R := K₃) 99)

-- `‖m‖ = 1` for an integer prime to `3`.
private theorem norm_intCast_eq_one_of_not_dvd {m : ℤ} (hm : ¬ (3 : ℤ) ∣ m) : ‖(m : K₃)‖ = 1 := by
  rw [← norm_natAbs]
  refine Jacobs.norm_natCast_eq_one_of_coprime norm_three_lt_one (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h ↦
      hm (Int.natAbs_dvd_natAbs.mp (by simpa using h))))

-- `‖X + Y·ν₃‖ ≤ ‖3‖^k` from `X + 22·Y = 3^k·m` (`k ≤ 3`).
private theorem norm_lin_le (X Y m : ℤ) (k : ℕ) (hk : k ≤ 3) (hm : X + 22 * Y = 3 ^ k * m) :
    ‖(X : K₃) + (Y : K₃) * ν₃‖ ≤ ‖(3 : K₃)‖ ^ k := by
  refine Jacobs.norm_le_of_sub (y := (X : K₃) + 22 * (Y : K₃)) ?_ ?_
  · rw [show (X : K₃) + (Y : K₃) * ν₃ - ((X : K₃) + 22 * (Y : K₃))
        = (Y : K₃) * (ν₃ - 22) by ring, norm_mul]
    exact ((mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one (R := K₃) Y)).trans norm_ν₃_sub_22).trans
      (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le hk)
  · rw [show (X : K₃) + 22 * (Y : K₃) = (3 : K₃) ^ k * (m : K₃) by exact_mod_cast hm,
      norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) k)
      (IsUltrametricDist.norm_intCast_le_one (R := K₃) m)

-- `‖X + Y·ν₃‖ = ‖3‖^k` when moreover the cofactor is prime to `3` (`k ≤ 2`).
private theorem norm_lin_eq (X Y m : ℤ) (k : ℕ) (hk : k ≤ 2) (hm : X + 22 * Y = 3 ^ k * m)
    (hm3 : ¬ (3 : ℤ) ∣ m) : ‖(X : K₃) + (Y : K₃) * ν₃‖ = ‖(3 : K₃)‖ ^ k := by
  have hmain : ‖(X : K₃) + 22 * (Y : K₃)‖ = ‖(3 : K₃)‖ ^ k := by
    rw [show (X : K₃) + 22 * (Y : K₃) = (3 : K₃) ^ k * (m : K₃) by exact_mod_cast hm,
      norm_mul, norm_pow, norm_intCast_eq_one_of_not_dvd hm3, mul_one]
  rw [show (X : K₃) + (Y : K₃) * ν₃
      = ((X : K₃) + 22 * (Y : K₃)) + (Y : K₃) * (ν₃ - 22) by ring, ← hmain]
  refine Jacobs.norm_eq_of_sub_lt ?_
  rw [add_sub_cancel_left, norm_mul, hmain]
  exact ((mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_intCast_le_one (R := K₃) Y)).trans norm_ν₃_sub_22).trans_lt
    (pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.mpr (by norm_num)) norm_three_lt_one (by lia))

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

/-- The candidate level element `u(i,t) := (d(i,t)·c_{σ(i,t)})⁻¹ · cᵢ · wₜ` — *defined*,
not guessed (module header): `factorisation` is then true by construction and the whole
certificate content is `uCand_mem`. -/
noncomputable def uCand (i t : Fin 3) : Dfx ℚ D :=
  (unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t))⁻¹ * (classRep i * etaRep t)

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

-- Away from `3`, the candidate's component is `d(i,t)⁻¹` (everything else is
-- single-place at `3`).
private theorem toLocal_uCand_ne (i t : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((uCand i t : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = (((dTable i t)⁻¹ : Dˣ) : D) ⊗ₜ[ℚ] 1 := by
  simp only [uCand, mul_inv_rev, ← map_inv (unitsIncl ℚ D), Units.val_mul, map_mul,
    toLocal_classRep_inv_ne _ hw, toLocal_unitsIncl, toLocal_classRep_ne _ hw,
    toLocal_etaRep_ne _ hw, one_mul, mul_one]

-- Away from `3`, the candidate's inverse has component `d(i,t)`.
private theorem toLocal_uCand_inv_ne (i t : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((uCand i t)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
      = ((dTable i t : Dˣ) : D) ⊗ₜ[ℚ] 1 := by
  simp only [uCand, mul_inv_rev, inv_inv, Units.val_mul, map_mul,
    toLocal_etaRep_inv_ne _ hw, toLocal_classRep_inv_ne _ hw, toLocal_unitsIncl,
    toLocal_classRep_ne _ hw, one_mul, mul_one]

-- `((3⁻¹ • e) ⊗ 1` is `w`-integral for Hurwitz `e`, `w ≠ v₃`.
private theorem smul_third_tmul_mem {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) {e : D} (he : e ∈ hurwitzOrder) :
    ((3⁻¹ : ℚ) • e) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ localOrder w := by
  rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  exact tmul_mem_localOrder he ⟨_, inv_three_mem_adicCompletionIntegers hw⟩

-- The away-from-`3` halves of `uCand`'s `U₀(1)`-membership.
private theorem uCand_away (i t : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((uCand i t : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w ∧
      toLocal ℚ D w (((uCand i t)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w := by
  constructor
  · rw [toLocal_uCand_ne i t hw, dTable_inv_val]
    exact smul_third_tmul_mem hw (star_mem (dTable_val_mem i t))
  · simpa [toLocal_uCand_inv_ne i t hw] using tmul_mem_localOrder (dTable_val_mem i t) 1

/- The nine level matrices `E(i,t) = toMatrix (uCand i t)`: transcribed from the
certificate search (`certificate_search.py`, section `LEAN LITERALS`), in the canonical
shape `(X + Y·ν₃)/M` with `X, Y ∈ ℤ`, `M ∈ ℕ` that the norm workhorses consume.  The simp
set of each pair is its own: it names only the `d(i,t)` entry that pair actually uses. -/

private theorem toMatrix_uCand₀₀ :
    toMatrix ℚ D v₃ (uCand 0 0)
      = !![((((-1) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((21 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          0, ((((-1) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 0
      = (unitsIncl ℚ D (-uA) * classRep 2)⁻¹ * (classRep 0 * etaRep 0) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uA_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dAi_re, dAi_imI, dAi_imJ, dAi_imK, map_neg, map_zero, map_one, map_div₀, map_ofNat,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, mul_zero, zero_mul, add_zero, zero_add,
        neg_zero]
      push_cast
      ring

private theorem toMatrix_uCand₀₁ :
    toMatrix ℚ D v₃ (uCand 0 1)
      = !![(((8 : ℤ) : K₃) + ((4 : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃);
          ((((-2) : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 1
      = (unitsIncl ℚ D (uB) * classRep 1)⁻¹ * (classRep 0 * etaRep 1) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB_inv_val, dBi_re, dBi_imI, dBi_imJ, dBi_imK, map_neg, map_one,
        map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero,
        zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₀₂ :
    toMatrix ℚ D v₃ (uCand 0 2)
      = !![(((12 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃);
          ((((-32) : ℤ) : K₃) + (((-55) : ℤ) : K₃) * ν₃) / ((12 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 0 2
      = (unitsIncl ℚ D (uC) * classRep 1)⁻¹ * (classRep 0 * etaRep 2) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC_inv_val, dCi_re, dCi_imI, dCi_imJ, dCi_imK, map_neg, map_one,
        map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero,
        zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₁₀ :
    toMatrix ℚ D v₃ (uCand 1 0)
      = !![(((5 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((3 : ℕ) : K₃),
          ((((-4) : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          0, (((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 1 0
      = (unitsIncl ℚ D (uA) * classRep 0)⁻¹ * (classRep 1 * etaRep 0) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA_inv_val, dAi_re, dAi_imI, dAi_imJ, dAi_imK, map_neg, map_zero,
        map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one,
        ht, mul_zero, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₁₁ :
    toMatrix ℚ D v₃ (uCand 1 1)
      = !![(((26 : ℤ) : K₃) + ((13 : ℤ) : K₃) * ν₃) / ((42 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          ((((-20) : ℤ) : K₃) + ((23 : ℤ) : K₃) * ν₃) / ((24 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 1 1
      = (unitsIncl ℚ D (uB) * classRep 2)⁻¹ * (classRep 1 * etaRep 1) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB_inv_val, dBi_re, dBi_imI, dBi_imJ, dBi_imK, map_neg, map_one,
        map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero,
        zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₁₂ :
    toMatrix ℚ D v₃ (uCand 1 2)
      = !![(((24 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          ((((-52) : ℤ) : K₃) + (((-113) : ℤ) : K₃) * ν₃) / ((24 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃)] := by
  have huc : uCand 1 2
      = (unitsIncl ℚ D (uC) * classRep 2)⁻¹ * (classRep 1 * etaRep 2) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC_inv_val, dCi_re, dCi_imI, dCi_imJ, dCi_imK, map_neg, map_one,
        map_div₀, map_ofNat, Int.cast_ofNat, Nat.cast_ofNat, ht, zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₂₀ :
    toMatrix ℚ D v₃ (uCand 2 0)
      = !![(((7 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃),
          ((((-8) : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃);
          0, (((2 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 0
      = (unitsIncl ℚ D (uA) * classRep 1)⁻¹ * (classRep 2 * etaRep 0) := rfl
  have ht : (((0 : Fin 3) : ℕ) : K₃) = 0 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA_inv_val, dAi_re, dAi_imI, dAi_imJ, dAi_imK, map_neg, map_zero,
        map_one, map_div₀, map_ofNat, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one, ht, mul_zero,
        zero_mul, add_zero, zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₂₁ :
    toMatrix ℚ D v₃ (uCand 2 1)
      = !![((((-58) : ℤ) : K₃) + (((-29) : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          ((((-4) : ℤ) : K₃) + (((-2) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((28 : ℤ) : K₃) + (((-43) : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + (((-2) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 1
      = (unitsIncl ℚ D (-uB) * classRep 0)⁻¹ * (classRep 2 * etaRep 1) := rfl
  have ht : (((1 : Fin 3) : ℕ) : K₃) = 1 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uB_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dBi_re, dBi_imI, dBi_imJ, dBi_imK, map_neg, map_one, map_div₀, map_ofNat,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one, ht, zero_mul, add_zero,
        zero_add]
      push_cast
      ring

private theorem toMatrix_uCand₂₂ :
    toMatrix ℚ D v₃ (uCand 2 2)
      = !![((((-48) : ℤ) : K₃) + ((17 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          ((((-4) : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((116 : ℤ) : K₃) + ((223 : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃),
          (((4 : ℤ) : K₃) + ((6 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  have huc : uCand 2 2
      = (unitsIncl ℚ D (-uC) * classRep 0)⁻¹ * (classRep 2 * etaRep 2) := rfl
  have ht : (((2 : Fin 3) : ℕ) : K₃) = 2 := by norm_num
  rw [huc, mul_inv_rev, ← map_inv (unitsIncl ℚ D), map_mul, map_mul, map_mul,
    toMatrix_classRep_inv, toMatrix_unitsIncl, toMatrix_classRep, toMatrix_etaRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, inv_neg, Units.val_neg, uC_inv_val, re_neg, imI_neg, imJ_neg,
        imK_neg, dCi_re, dCi_imI, dCi_imJ, dCi_imK, map_neg, map_one, map_div₀, map_ofNat,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one, ht, zero_mul, add_zero,
        zero_add]
      push_cast
      ring

-- `Valued.v x ≤ γ₉` from the norm bound `‖x‖ ≤ ‖3‖²`.
private theorem valued_le_γ₉_of_norm {x : K₃} (h : ‖x‖ ≤ ‖(3 : K₃)‖ ^ 2) :
    Valued.v x ≤ γ₉ := by
  rw [← valued_nine_eq, ← Valued.toNormedField.norm_le_iff]
  rwa [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, ← sq]

-- `Valued.v x ≤ 1` from `‖x‖ ≤ 1`.
-- The full-entry workhorse: `‖(X + Y·ν₃)/M‖ ≤ ‖3‖^T`.
private theorem norm_frac_le (X Y : ℤ) (M T e : ℕ) (m : ℤ) (M' : ℕ) (hTe : T + e ≤ 3)
    (hnum : X + 22 * Y = 3 ^ (T + e) * m) (hM : M = 3 ^ e * M') (hM' : Nat.Coprime M' 3) :
    ‖((X : K₃) + (Y : K₃) * ν₃) / (M : K₃)‖ ≤ ‖(3 : K₃)‖ ^ T := by
  rw [norm_div, Jacobs.norm_ofNat_eq_pow norm_three_lt_one hM' hM rfl,
    div_le_iff₀ (pow_pos (norm_pos_iff.mpr (by norm_num : (3 : K₃) ≠ 0)) e), ← pow_add]
  exact norm_lin_le X Y m (T + e) hTe hnum

-- The full-entry workhorse, unit form: numerator and denominator share the `3`-adic
-- valuation `e` with coprime cofactors.
private theorem norm_frac_eq_one (X Y : ℤ) (M e : ℕ) (m : ℤ) (M' : ℕ) (he : e ≤ 2)
    (hnum : X + 22 * Y = 3 ^ e * m) (hm3 : ¬ (3 : ℤ) ∣ m) (hM : M = 3 ^ e * M')
    (hM' : Nat.Coprime M' 3) : ‖((X : K₃) + (Y : K₃) * ν₃) / (M : K₃)‖ = 1 := by
  rw [norm_div, Jacobs.norm_ofNat_eq_pow norm_three_lt_one hM' hM rfl,
    norm_lin_eq X Y m e he hnum hm3,
    div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (by norm_num : (3 : K₃) ≠ 0)))]

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
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-1) 1 21 1 7 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₀, det_uCand₀₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-1) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((21 : ℕ) : K₃) : K₃) - 1
        = ((((-22) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((21 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-22) 1 21 2 1 0 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₀ : Valued.v ((toMatrix ℚ D v₃ (uCand 0 0)).det) = 1 := by
  rw [det_uCand₀₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₀₁ : (toMatrix ℚ D v₃ (uCand 0 1)).det = (1 : K₃) / (10 : K₃) := by
  rw [toMatrix_uCand₀₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1 / 60 : K₃) * sq_ν₃

private theorem int_uCand₀₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 0 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₀₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 8 4 15 0 1 32 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 1 10 0 0 24 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) 5 6 0 1 36 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 1 4 0 0 22 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₀₁ : toMatrix ℚ D v₃ (uCand 0 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₀₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₀₁] using int_uCand₀₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-2) 5 6 2 1 4 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 8 4 15 1 32 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₁, det_uCand₀₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((8 : ℤ) : K₃) + ((4 : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃) : K₃) - 1
        = ((((-7) : ℤ) : K₃) + ((4 : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-7) 4 15 2 1 3 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₁ : Valued.v ((toMatrix ℚ D v₃ (uCand 0 1)).det) = 1 := by
  rw [det_uCand₀₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₀₂ : (toMatrix ℚ D v₃ (uCand 0 2)).det = (1 : K₃) / (10 : K₃) := by
  rw [toMatrix_uCand₀₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1 / 12 : K₃) * sq_ν₃

private theorem int_uCand₀₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 0 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₀₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 12 (-5) 10 0 0 (-98) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 (-1) 10 0 0 (-20) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-32) (-55) 12 0 1 (-414) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-3) 4 0 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₀₂ : toMatrix ℚ D v₃ (uCand 0 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₀₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₀₂] using int_uCand₀₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-32) (-55) 12 2 1 (-46) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 12 (-5) 10 0 (-98) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₀₂, det_uCand₀₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((12 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) : K₃) - 1
        = (((2 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) by
      ring]
    exact norm_frac_le 2 (-5) 10 2 0 (-12) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₀₂ : Valued.v ((toMatrix ℚ D v₃ (uCand 0 2)).det) = 1 := by
  rw [det_uCand₀₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₀ : (toMatrix ℚ D v₃ (uCand 1 0)).det = (10 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₁₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-10 / 3 : K₃) * sq_ν₃

private theorem int_uCand₁₀ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 0)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 5 (-5) 3 0 1 (-35) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) 0 1 0 0 (-4) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 2 1 0 0 46 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₀ : toMatrix ℚ D v₃ (uCand 1 0) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₀] using int_uCand₁₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 5 (-5) 3 1 (-35) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₀, det_uCand₁₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((5 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((3 : ℕ) : K₃) : K₃) - 1
        = (((2 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((3 : ℕ) : K₃) by
      ring]
    exact norm_frac_le 2 (-5) 3 2 1 (-4) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₀ : Valued.v ((toMatrix ℚ D v₃ (uCand 1 0)).det) = 1 := by
  rw [det_uCand₁₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 10) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₁ : (toMatrix ℚ D v₃ (uCand 1 1)).det = (5 : K₃) / (14 : K₃) := by
  rw [toMatrix_uCand₁₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-5 / 84 : K₃) * sq_ν₃

private theorem int_uCand₁₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 26 13 42 0 1 104 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 1 7 0 0 24 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-20) 23 24 0 1 162 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 1 4 0 0 22 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₁ : toMatrix ℚ D v₃ (uCand 1 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₁] using int_uCand₁₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-20) 23 24 2 1 18 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 26 13 42 1 104 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₁, det_uCand₁₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((26 : ℤ) : K₃) + ((13 : ℤ) : K₃) * ν₃) / ((42 : ℕ) : K₃) : K₃) - 1
        = ((((-16) : ℤ) : K₃) + ((13 : ℤ) : K₃) * ν₃) / ((42 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-16) 13 42 2 1 10 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₁ : Valued.v ((toMatrix ℚ D v₃ (uCand 1 1)).det) = 1 := by
  rw [det_uCand₁₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₁₂ : (toMatrix ℚ D v₃ (uCand 1 2)).det = (5 : K₃) / (14 : K₃) := by
  rw [toMatrix_uCand₁₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-25 / 84 : K₃) * sq_ν₃

private theorem int_uCand₁₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 1 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₁₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 24 (-7) 14 0 0 (-130) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 (-1) 7 0 0 (-20) 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-52) (-113) 24 0 1 (-846) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-3) 4 0 0 (-68) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₁₂ : toMatrix ℚ D v₃ (uCand 1 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₁₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₁₂] using int_uCand₁₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-52) (-113) 24 2 1 (-94) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 24 (-7) 14 0 (-130) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₁₂, det_uCand₁₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((24 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) : K₃) - 1
        = (((10 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) by
      ring]
    exact norm_frac_le 10 (-7) 14 2 0 (-16) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₁₂ : Valued.v ((toMatrix ℚ D v₃ (uCand 1 2)).det) = 1 := by
  rw [det_uCand₁₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₀ : (toMatrix ℚ D v₃ (uCand 2 0)).det = (14 : K₃) / (5 : K₃) := by
  rw [toMatrix_uCand₂₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-14 / 15 : K₃) * sq_ν₃

private theorem int_uCand₂₀ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 0)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 7 (-7) 15 0 1 (-49) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-8) 0 5 0 0 (-8) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 2 1 0 0 46 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₀ : toMatrix ℚ D v₃ (uCand 2 0) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₀] using int_uCand₂₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 7 (-7) 15 1 (-49) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₀, det_uCand₂₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((7 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃) : K₃) - 1
        = ((((-8) : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((15 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-8) (-7) 15 2 1 (-6) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₀ : Valued.v ((toMatrix ℚ D v₃ (uCand 2 0)).det) = 1 := by
  rw [det_uCand₂₀]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 14) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₁ : (toMatrix ℚ D v₃ (uCand 2 1)).det = (28 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₂₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-14 / 3 : K₃) * sq_ν₃

private theorem int_uCand₂₁ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 1)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-58) (-29) 6 0 1 (-232) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (-2) 1 0 0 (-48) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 28 (-43) 6 0 1 (-306) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 (-2) 1 0 0 (-44) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₁ : toMatrix ℚ D v₃ (uCand 2 1) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₁] using int_uCand₂₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le 28 (-43) 6 2 1 (-34) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-58) (-29) 6 1 (-232) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₁, det_uCand₂₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-58) : ℤ) : K₃) + (((-29) : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃) : K₃) - 1
        = ((((-64) : ℤ) : K₃) + (((-29) : ℤ) : K₃) * ν₃) / ((6 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-64) (-29) 6 2 1 (-26) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₁ : Valued.v ((toMatrix ℚ D v₃ (uCand 2 1)).det) = 1 := by
  rw [det_uCand₂₁]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

private theorem det_uCand₂₂ : (toMatrix ℚ D v₃ (uCand 2 2)).det = (28 : K₃) / (1 : K₃) := by
  rw [toMatrix_uCand₂₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-70 / 3 : K₃) * sq_ν₃

private theorem int_uCand₂₂ : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand 2 2)) r c) ≤ 1 := by
  rw [toMatrix_uCand₂₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-48) 17 2 0 0 326 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) 2 1 0 0 40 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 116 223 6 0 1 1674 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 4 6 1 0 0 136 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_uCand₂₂ : toMatrix ℚ D v₃ (uCand 2 2) ∈ Sigma1 := by
  rw [toMatrix_uCand₂₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_uCand₂₂] using int_uCand₂₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le 116 223 6 2 1 186 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-48) 17 2 0 326 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_uCand₂₂, det_uCand₂₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-48) : ℤ) : K₃) + ((17 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) : K₃) - 1
        = ((((-50) : ℤ) : K₃) + ((17 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-50) 17 2 2 0 36 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem valued_det_uCand₂₂ : Valued.v ((toMatrix ℚ D v₃ (uCand 2 2)).det) = 1 := by
  rw [det_uCand₂₂]
  refine valued_eq_one_of_norm_eq_one ?_
  rw [norm_div, Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 28) (by norm_num)
    (by norm_num), Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 1) (by norm_num)
    (by norm_num), div_one]

-- **The certificate content**: every candidate lies in `U₁(9)`.
private theorem uCand_mem (i t : Fin 3) : uCand i t ∈ U1_9 := by
  have h1 : toMatrix ℚ D v₃ (uCand i t) * toMatrix ℚ D v₃ ((uCand i t)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : toMatrix ℚ D v₃ ((uCand i t)⁻¹) * toMatrix ℚ D v₃ (uCand i t) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  obtain ⟨hdet, hs⟩ : Valued.v ((toMatrix ℚ D v₃ (uCand i t)).det) = 1 ∧
      toMatrix ℚ D v₃ (uCand i t) ∈ Sigma1 := by
    fin_cases i <;> fin_cases t
    exacts [⟨valued_det_uCand₀₀, sigma1_uCand₀₀⟩, ⟨valued_det_uCand₀₁, sigma1_uCand₀₁⟩,
      ⟨valued_det_uCand₀₂, sigma1_uCand₀₂⟩, ⟨valued_det_uCand₁₀, sigma1_uCand₁₀⟩,
      ⟨valued_det_uCand₁₁, sigma1_uCand₁₁⟩, ⟨valued_det_uCand₁₂, sigma1_uCand₁₂⟩,
      ⟨valued_det_uCand₂₀, sigma1_uCand₂₀⟩, ⟨valued_det_uCand₂₁, sigma1_uCand₂₁⟩,
      ⟨valued_det_uCand₂₂, sigma1_uCand₂₂⟩]
  have hint : ∀ r c, Valued.v ((toMatrix ℚ D v₃ (uCand i t)) r c) ≤ 1 := hs.1.1
  have hint' : ∀ r c, Valued.v ((toMatrix ℚ D v₃ ((uCand i t)⁻¹)) r c) ≤ 1 :=
    valued_inv_entries_le hint hdet h1
  refine mem_U1_9_of_toMatrix (fun w => uCand_away i t) ?_ ?_ hs
    (sigma1_of_mul_eq_one hs hint' h1 h2)
  · exact mem_integralMatrices_iff.mpr fun r c =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hint r c)
  · exact mem_integralMatrices_iff.mpr fun r c =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hint' r c)

/-- The level factor `u(i,t)` of each certificate: the candidate together with its
membership certificate. -/
noncomputable def uTable : Fin 3 → Fin 3 → U1_9 := fun i t => ⟨uCand i t, uCand_mem i t⟩

/-- **The nine certificates** ([Jacobs pp. 26–27, §B.1]): the factorisation identities
`classRep i · etaRep t = d(i,t) · classRep (σ(i,t)) · u(i,t)` in `D_f^×`. -/
theorem factorisation (i t : Fin 3) : classRep i * etaRep t =
    unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t) * (uTable i t : Dfx ℚ D) :=
  (mul_inv_cancel_left _ _).symm

/- The acting matrices `G(i,t) = θ₃(etaRep t · u(i,t)⁻¹) = θ₃(cᵢ⁻¹ · d · c_σ)`. -/

-- The acting element of a certificate collapses to `cᵢ⁻¹ · d(i,t) · c_{σ(i,t)}`.
private theorem acting_eq (i t : Fin 3) :
    etaRep t * ((uTable i t : Dfx ℚ D))⁻¹
      = (classRep i)⁻¹ * (unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t)) := by
  show etaRep t * (uCand i t)⁻¹ = _
  rw [uCand]
  group

private theorem toMatrix_acting₀₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 0 0 : Dfx ℚ D))⁻¹)
      = !![((((-7) : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃),
          ((((-8) : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          0, ((((-4) : ℤ) : K₃) + ((4 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (0 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 0 0) * classRep (sigmaTable 0 0))
      = (classRep 0)⁻¹ * (unitsIncl ℚ D (-uA) * classRep 2) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, Units.val_neg, uA_val, re_neg, imI_neg, imJ_neg, imK_neg, dA_re,
        dA_imI, dA_imJ, dA_imK, map_neg, map_zero, map_one, Int.cast_one, Int.cast_ofNat,
        Nat.cast_one, zero_mul, add_zero, neg_zero, neg_neg]
      push_cast
      ring

private theorem det_acting₀₀ :
    (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 0 0 : Dfx ℚ D))⁻¹)).det = (84 : K₃) / (1 : K₃) := by
  rw [toMatrix_acting₀₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((-28) : K₃) * sq_ν₃

private theorem int_acting₀₀ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 0 * ((uTable 0 0 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₀₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-7) (-7) 1 0 0 (-161) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-8) 0 1 0 0 (-8) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) 4 1 0 0 84 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₀₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 0 0 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₀₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₀₀] using int_acting₀₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-7) (-7) 1 0 (-161) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₀₀, det_acting₀₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-7) : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) : K₃) - 1
        = ((((-8) : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-8) (-7) 1 2 0 (-18) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₀₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 0 1 : Dfx ℚ D))⁻¹)
      = !![(((0 : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          (((20 : ℤ) : K₃) + (((-5) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (0 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 0 1) * classRep (sigmaTable 0 1))
      = (classRep 0)⁻¹ * (unitsIncl ℚ D (uB) * classRep 1) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB_val, dB_re, dB_imI, dB_imJ, dB_imK, map_neg, map_one, map_div₀,
        map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one]
      push_cast
      ring

private theorem det_acting₀₁ :
    (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 0 1 : Dfx ℚ D))⁻¹)).det = (30 : K₃) / (1 : K₃) := by
  rw [toMatrix_acting₀₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((-5) : K₃) * sq_ν₃

private theorem int_acting₀₁ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 1 * ((uTable 0 1 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₀₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 5 2 0 0 110 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-1) 1 0 0 (-24) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 20 (-5) 2 0 0 (-90) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-1) 1 0 0 (-24) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₀₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 0 1 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₀₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₀₁] using int_acting₀₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le 20 (-5) 2 2 0 (-10) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 0 5 2 0 110 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₀₁, det_acting₀₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) : K₃) - 1
        = ((((-2) : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-2) 5 2 2 0 12 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₀₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 0 2 : Dfx ℚ D))⁻¹)
      = !![((((-10) : ℤ) : K₃) + (((-15) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃);
          ((((-20) : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((3 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (0 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 0 2) * classRep (sigmaTable 0 2))
      = (classRep 0)⁻¹ * (unitsIncl ℚ D (uC) * classRep 1) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC_val, dC_re, dC_imI, dC_imJ, dC_imK, map_neg, map_one, map_div₀,
        map_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one]
      push_cast
      ring

private theorem det_acting₀₂ :
    (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 0 2 : Dfx ℚ D))⁻¹)).det = (30 : K₃) / (1 : K₃) := by
  rw [toMatrix_acting₀₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((-25) : K₃) * sq_ν₃

private theorem int_acting₀₂ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 2 * ((uTable 0 2 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₀₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-10) (-15) 2 0 0 (-340) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) 1 1 0 0 20 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-20) 5 2 0 0 90 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 3 1 0 0 66 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₀₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 0 2 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₀₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₀₂] using int_acting₀₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-20) 5 2 2 0 10 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-10) (-15) 2 0 (-340) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₀₂, det_acting₀₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-10) : ℤ) : K₃) + (((-15) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) : K₃) - 1
        = ((((-12) : ℤ) : K₃) + (((-15) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-12) (-15) 2 2 0 (-38) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₁₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 1 0 : Dfx ℚ D))⁻¹)
      = !![(((1 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃);
          0, (((1 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (1 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 1 0) * classRep (sigmaTable 1 0))
      = (classRep 1)⁻¹ * (unitsIncl ℚ D (uA) * classRep 0) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA_val, dA_re, dA_imI, dA_imJ, dA_imK, map_neg, map_zero, map_one,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, zero_mul, add_zero]
      push_cast
      ring

private theorem det_acting₁₀ :
    (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 1 0 : Dfx ℚ D))⁻¹)).det = (3 : K₃) / (10 : K₃) := by
  rw [toMatrix_acting₁₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1 / 10 : K₃) * sq_ν₃

private theorem int_acting₁₀ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 0 * ((uTable 1 0 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₁₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 1 1 5 0 0 23 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 0 5 0 0 2 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 1 (-1) 2 0 0 (-21) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₁₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 1 0 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₁₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₁₀] using int_acting₁₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 1 1 5 0 23 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₁₀, det_acting₁₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((1 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃) : K₃) - 1
        = ((((-4) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-4) 1 5 2 0 2 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₁₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 1 1 : Dfx ℚ D))⁻¹)
      = !![(((0 : ℤ) : K₃) + ((7 : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃),
          ((((-4) : ℤ) : K₃) + (((-2) : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃);
          (((28 : ℤ) : K₃) + (((-7) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃),
          ((((-2) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (1 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 1 1) * classRep (sigmaTable 1 1))
      = (classRep 1)⁻¹ * (unitsIncl ℚ D (uB) * classRep 2) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uB_val, dB_re, dB_imI, dB_imJ, dB_imK, map_neg, map_one, map_div₀,
        map_ofNat, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one]
      push_cast
      ring

private theorem det_acting₁₁ :
    (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 1 1 : Dfx ℚ D))⁻¹)).det = (42 : K₃) / (5 : K₃) := by
  rw [toMatrix_acting₁₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-7 / 5 : K₃) * sq_ν₃

private theorem int_acting₁₁ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 1 * ((uTable 1 1 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₁₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 7 10 0 0 154 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) (-2) 5 0 0 (-48) 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 28 (-7) 4 0 0 (-126) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-2) (-1) 1 0 0 (-24) 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₁₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 1 1 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₁₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₁₁] using int_acting₁₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le 28 (-7) 4 2 0 (-14) 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 0 7 10 0 154 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₁₁, det_acting₁₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + ((7 : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) : K₃) - 1
        = ((((-10) : ℤ) : K₃) + ((7 : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-10) 7 10 2 0 16 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₁₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 1 2 : Dfx ℚ D))⁻¹)
      = !![((((-14) : ℤ) : K₃) + (((-21) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃),
          ((((-4) : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((5 : ℕ) : K₃);
          ((((-28) : ℤ) : K₃) + ((7 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + ((3 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (1 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 1 2) * classRep (sigmaTable 1 2))
      = (classRep 1)⁻¹ * (unitsIncl ℚ D (uC) * classRep 2) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uC_val, dC_re, dC_imI, dC_imJ, dC_imK, map_neg, map_one, map_div₀,
        map_ofNat, Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one]
      push_cast
      ring

private theorem det_acting₁₂ :
    (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 1 2 : Dfx ℚ D))⁻¹)).det = (42 : K₃) / (5 : K₃) := by
  rw [toMatrix_acting₁₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((-7) : K₃) * sq_ν₃

private theorem int_acting₁₂ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 2 * ((uTable 1 2 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₁₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-14) (-21) 10 0 0 (-476) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) 2 5 0 0 40 5 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-28) 7 4 0 0 126 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 3 1 0 0 66 1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₁₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 1 2 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₁₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₁₂] using int_acting₁₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-28) 7 4 2 0 14 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one (-14) (-21) 10 0 (-476) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₁₂, det_acting₁₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show (((((-14) : ℤ) : K₃) + (((-21) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) : K₃) - 1
        = ((((-24) : ℤ) : K₃) + (((-21) : ℤ) : K₃) * ν₃) / ((10 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-24) (-21) 10 2 0 (-54) 10 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₂₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 2 0 : Dfx ℚ D))⁻¹)
      = !![(((5 : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃),
          (((4 : ℤ) : K₃) + ((0 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃);
          0, (((1 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((2 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (2 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 2 0) * classRep (sigmaTable 2 0))
      = (classRep 2)⁻¹ * (unitsIncl ℚ D (uA) * classRep 1) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, uA_val, dA_re, dA_imI, dA_imJ, dA_imK, map_neg, map_zero, map_one,
        Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, zero_mul, add_zero]
      push_cast
      ring

private theorem det_acting₂₀ :
    (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 2 0 : Dfx ℚ D))⁻¹)).det = (15 : K₃) / (14 : K₃) := by
  rw [toMatrix_acting₂₀, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-5 / 14 : K₃) * sq_ν₃

private theorem int_acting₂₀ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 0 * ((uTable 2 0 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₂₀]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 5 5 7 0 0 115 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 4 0 7 0 0 4 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 1 (-1) 2 0 0 (-21) 2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₂₀ :
    toMatrix ℚ D v₃ (etaRep 0 * ((uTable 2 0 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₂₀]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₂₀] using int_acting₂₀
  · simp
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 5 5 7 0 115 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₂₀, det_acting₂₀]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((5 : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃) : K₃) - 1
        = ((((-2) : ℤ) : K₃) + ((5 : ℤ) : K₃) * ν₃) / ((7 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-2) 5 7 2 0 12 7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₂₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 2 1 : Dfx ℚ D))⁻¹)
      = !![(((0 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃);
          ((((-4) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((8 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((8 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (2 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 2 1) * classRep (sigmaTable 2 1))
      = (classRep 2)⁻¹ * (unitsIncl ℚ D (-uB) * classRep 0) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, Units.val_neg, uB_val, re_neg, imI_neg, imJ_neg, imK_neg, dB_re,
        dB_imI, dB_imJ, dB_imK, map_neg, map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, neg_neg]
      push_cast
      ring

private theorem det_acting₂₁ :
    (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 2 1 : Dfx ℚ D))⁻¹)).det = (3 : K₃) / (28 : K₃) := by
  rw [toMatrix_acting₂₁, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-1 / 56 : K₃) * sq_ν₃

private theorem int_acting₂₁ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 1 * ((uTable 2 1 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₂₁]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 (-1) 14 0 0 (-22) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 1 14 0 0 24 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le (-4) 1 8 0 0 18 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 1 8 0 0 24 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₂₁ :
    toMatrix ℚ D v₃ (etaRep 1 * ((uTable 2 1 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₂₁]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₂₁] using int_acting₂₁
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le (-4) 1 8 2 0 2 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 0 (-1) 14 0 (-22) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₂₁, det_acting₂₁]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((0 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) : K₃) - 1
        = ((((-14) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-14) (-1) 14 2 0 (-4) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem toMatrix_acting₂₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 2 2 : Dfx ℚ D))⁻¹)
      = !![(((2 : ℤ) : K₃) + ((3 : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃),
          (((2 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃);
          (((4 : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((8 : ℕ) : K₃),
          (((0 : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((8 : ℕ) : K₃)] := by
  rw [acting_eq]
  have hpin : (classRep (2 : Fin 3))⁻¹
        * (unitsIncl ℚ D (dTable 2 2) * classRep (sigmaTable 2 2))
      = (classRep 2)⁻¹ * (unitsIncl ℚ D (-uC) * classRep 0) := rfl
  rw [hpin, map_mul, map_mul, toMatrix_classRep_inv, toMatrix_unitsIncl,
    toMatrix_classRep]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, classDiag, Units.val_neg, uC_val, re_neg, imI_neg, imJ_neg, imK_neg, dC_re,
        dC_imI, dC_imJ, dC_imK, map_one, map_div₀, map_ofNat, Int.cast_one, Int.cast_ofNat,
        Nat.cast_ofNat, neg_neg]
      push_cast
      ring

private theorem det_acting₂₂ :
    (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 2 2 : Dfx ℚ D))⁻¹)).det = (3 : K₃) / (28 : K₃) := by
  rw [toMatrix_acting₂₂, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-5 / 56 : K₃) * sq_ν₃

private theorem int_acting₂₂ :
    ∀ r c, Valued.v ((toMatrix ℚ D v₃ (etaRep 2 * ((uTable 2 2 : Dfx ℚ D))⁻¹)) r c) ≤ 1 := by
  rw [toMatrix_acting₂₂]
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 3 14 0 0 68 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 2 (-1) 14 0 0 (-20) 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 4 (-1) 8 0 0 (-18) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · refine Valued.toNormedField.norm_le_one_iff.mp ?_
    simpa using norm_frac_le 0 (-3) 8 0 0 (-66) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

private theorem sigma1_acting₂₂ :
    toMatrix ℚ D v₃ (etaRep 2 * ((uTable 2 2 : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  rw [toMatrix_acting₂₂]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [toMatrix_acting₂₂] using int_acting₂₂
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    exact norm_frac_le 4 (-1) 8 2 0 (-2) 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_eq_one_of_norm_eq_one ?_
    exact norm_frac_eq_one 2 3 14 0 68 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← toMatrix_acting₂₂, det_acting₂₂]
    norm_num
  · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    refine valued_le_γ₉_of_norm ?_
    rw [show ((((2 : ℤ) : K₃) + ((3 : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) : K₃) - 1
        = ((((-12) : ℤ) : K₃) + ((3 : ℤ) : K₃) * ν₃) / ((14 : ℕ) : K₃) by
      ring]
    exact norm_frac_le (-12) 3 14 2 0 6 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

/-- The acting matrices of the factorisations lie in `Σ₁(9)`:
`(etaRep t · u(i,t)⁻¹)₃ ∈ Σ₁(9)` — the elements whose `κ`-action assembles the blocks. -/
theorem toMatrix_etaRep_mul_inv_uTable_mem_sigma1 (i t : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t * ((uTable i t : Dfx ℚ D))⁻¹) ∈ Sigma1 := by
  fin_cases i <;> fin_cases t <;>
    first
      | exact sigma1_acting₀₀ | exact sigma1_acting₀₁ | exact sigma1_acting₀₂
      | exact sigma1_acting₁₀ | exact sigma1_acting₁₁ | exact sigma1_acting₁₂
      | exact sigma1_acting₂₀ | exact sigma1_acting₂₁ | exact sigma1_acting₂₂

/-- The determinant `dᵢ·eᵢ ∈ {1, 10, 28}` of `θ₃(classRep i)`.  The handedness scalar of
the `ε`-identification is the ratio `classDet j / classDet i` (module header, computed
tables); all three values are `≡ 1 mod 9`, so the ratios are `1`-units. -/
def classDet (i : Fin 3) : ℤ := (classDiag i).1 * (classDiag i).2

/-- The transcribed `ε`-matrix acting at `(i, t')` ([Jacobs p. 28] displays as recorded
in `PhD.Jacobs.U3Data`, instantiated at `ν₃`), in the `t'`-assignment found by the
certificate search (module header): `t' = 0` carries the single-matrix blocks, and
`t' = 1, 2` respectively the second and first matrices of the two-matrix blocks. -/
noncomputable def epsTable : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) K₃ :=
  ![![Jacobs.eps02M ν₃, Jacobs.eps01M2 ν₃, Jacobs.eps01M1 ν₃],
    ![Jacobs.eps10M ν₃, Jacobs.eps12M2 ν₃, Jacobs.eps12M1 ν₃],
    ![Jacobs.eps21M ν₃, Jacobs.eps20M2 ν₃, Jacobs.eps20M1 ν₃]]

private theorem adjParams_acting₀₀ :
    adjParams (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 0 0 : Dfx ℚ D))⁻¹))
      = ((28 : K₃) / (1 : K₃)) • Jacobs.eps02M ν₃ := by
  rw [toMatrix_acting₀₀, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps02M, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₀₁ :
    adjParams (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 0 1 : Dfx ℚ D))⁻¹))
      = ((10 : K₃) / (1 : K₃)) • Jacobs.eps01M2 ν₃ := by
  rw [toMatrix_acting₀₁, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps01M2, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₀₂ :
    adjParams (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 0 2 : Dfx ℚ D))⁻¹))
      = ((10 : K₃) / (1 : K₃)) • Jacobs.eps01M1 ν₃ := by
  rw [toMatrix_acting₀₂, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps01M1, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₁₀ :
    adjParams (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 1 0 : Dfx ℚ D))⁻¹))
      = ((1 : K₃) / (10 : K₃)) • Jacobs.eps10M ν₃ := by
  rw [toMatrix_acting₁₀, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps10M, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₁₁ :
    adjParams (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 1 1 : Dfx ℚ D))⁻¹))
      = ((28 : K₃) / (10 : K₃)) • Jacobs.eps12M2 ν₃ := by
  rw [toMatrix_acting₁₁, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps12M2, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₁₂ :
    adjParams (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 1 2 : Dfx ℚ D))⁻¹))
      = ((28 : K₃) / (10 : K₃)) • Jacobs.eps12M1 ν₃ := by
  rw [toMatrix_acting₁₂, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps12M1, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₂₀ :
    adjParams (toMatrix ℚ D v₃ (etaRep 0 * ((uTable 2 0 : Dfx ℚ D))⁻¹))
      = ((10 : K₃) / (28 : K₃)) • Jacobs.eps21M ν₃ := by
  rw [toMatrix_acting₂₀, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps21M, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₂₁ :
    adjParams (toMatrix ℚ D v₃ (etaRep 1 * ((uTable 2 1 : Dfx ℚ D))⁻¹))
      = ((1 : K₃) / (28 : K₃)) • Jacobs.eps20M2 ν₃ := by
  rw [toMatrix_acting₂₁, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps20M2, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

private theorem adjParams_acting₂₂ :
    adjParams (toMatrix ℚ D v₃ (etaRep 2 * ((uTable 2 2 : Dfx ℚ D))⁻¹))
      = ((1 : K₃) / (28 : K₃)) • Jacobs.eps20M1 ν₃ := by
  rw [toMatrix_acting₂₂, adjParams_apply]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    · simp only [Jacobs.eps20M1, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.isValue, smul_eq_mul]
      push_cast
      ring

-- The three class determinants, cast to `K₃` (public: `04_Matrix.lean` reuses them for the
-- determinant-twist coboundary).
theorem cd0 : ((classDet (0 : Fin 3) : ℤ) : K₃) = 1 :=
  mod_cast show classDet (0 : Fin 3) = 1 by decide

theorem cd1 : ((classDet (1 : Fin 3) : ℤ) : K₃) = 10 :=
  mod_cast show classDet (1 : Fin 3) = 10 by decide

theorem cd2 : ((classDet (2 : Fin 3) : ℤ) : K₃) = 28 :=
  mod_cast show classDet (2 : Fin 3) = 28 by decide

/-- `‖3ⁿ‖ ≤ ‖3‖` for `n ≥ 1` — the shape the three class determinants need. -/
private theorem norm_three_pow_le {n : ℕ} (hn : 1 ≤ n) : ‖(3 : K₃) ^ n‖ ≤ ‖(3 : K₃)‖ := by
  rw [norm_pow]
  exact (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le hn).trans_eq (pow_one _)

/-- The three class determinants are `1`-units: `1, 10, 28` are all `≡ 1 mod 9`. -/
theorem norm_one_sub_one_le : ‖(1 : K₃) - 1‖ ≤ ‖(3 : K₃)‖ := by simp

theorem norm_ten_sub_one_le : ‖(10 : K₃) - 1‖ ≤ ‖(3 : K₃)‖ := by
  rw [show (10 : K₃) - 1 = 3 ^ 2 by norm_num]
  exact norm_three_pow_le one_le_two

theorem norm_twentyEight_sub_one_le : ‖(28 : K₃) - 1‖ ≤ ‖(3 : K₃)‖ := by
  rw [show (28 : K₃) - 1 = 3 ^ 3 by norm_num]
  exact norm_three_pow_le (by norm_num)

/-- `classDet ∈ {1, 10, 28}` are all `≡ 1 mod 9`, so their casts are `1`-units. -/
theorem norm_classDet_sub_one_le (i : Fin 3) : ‖(classDet i : K₃) - 1‖ ≤ ‖(3 : K₃)‖ := by
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [cd0]; exact norm_one_sub_one_le
  · rw [cd1]; exact norm_ten_sub_one_le
  · rw [cd2]; exact norm_twentyEight_sub_one_le

/-- A quotient of `1`-units is a `1`-unit: `‖v‖ = 1` by the isosceles principle, and
`u/v − 1 = ((u−1) − (v−1))/v`. -/
theorem norm_div_sub_one_le {u v : K₃} (hu : ‖u - 1‖ ≤ ‖(3 : K₃)‖)
    (hv : ‖v - 1‖ ≤ ‖(3 : K₃)‖) : ‖u / v - 1‖ ≤ ‖(3 : K₃)‖ := by
  have hv1 : ‖v‖ = 1 :=
    Jacobs.norm_eq_one_of_norm_sub_one_lt_one (hv.trans_lt norm_three_lt_one)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by simp [hv1])
  have key : u / v - 1 = (u - v) / v := by
    rw [eq_div_iff hv0, sub_mul, div_mul_cancel₀ _ hv0, one_mul]
  calc ‖u / v - 1‖ = ‖u - v‖ := by rw [key, norm_div, hv1, div_one]
    _ = ‖(u - 1) - (v - 1)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ max ‖u - 1‖ ‖v - 1‖ := Jacobs.norm_sub_le_max' _ _
    _ ≤ ‖(3 : K₃)‖ := max_le hu hv

/-- **The `ε`-matrix identification, matrix level** ([Jacobs p. 28 displays, as
transcribed — with the misprint corrected — in `PhD.Jacobs.U3Data`]; the exact content
of the certificates, machine-verified by `certificate_search.py`): the Jacobs-form
parameter matrix of the acting element of certificate `(i, t')` is the transcribed
`ε`-matrix scaled by the determinant ratio of the class representatives — equivalently,
`ε_{i,j}(t') = θ₃ (c_j⁻¹ · star (d(i,t')) · cᵢ)` on the nose.  The scalar is the
handedness normalisation of the module header, a `1`-unit. -/
theorem adjParams_toMatrix_eq_smul_epsTable (i t' : Fin 3) :
    adjParams (toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹))
      = ((classDet (sigmaTable i t') : K₃) / (classDet i : K₃)) • epsTable i t' := by
  fin_cases i <;> fin_cases t' <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, sigmaTable, epsTable,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, cd0, cd1, cd2]
  exacts [adjParams_acting₀₀, adjParams_acting₀₁, adjParams_acting₀₂, adjParams_acting₁₀,
    adjParams_acting₁₁, adjParams_acting₁₂, adjParams_acting₂₀, adjParams_acting₂₁,
    adjParams_acting₂₂]

private theorem hd_eps01M1 : ‖(Jacobs.eps01M1 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps01M1, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (-3 / 4 * ν₃ - 1 / 2 : K₃) - 1
      = ((((-6) : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-6) (-3) 4 1 0 (-24) 4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps01M2 : ‖(Jacobs.eps01M2 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps01M2, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (1 / 4 * ν₃ : K₃) - 1
      = ((((-4) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-4) 1 4 1 0 6 4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps02M : ‖(Jacobs.eps02M ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps02M, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (-1 / 4 * ν₃ - 1 / 4 : K₃) - 1
      = ((((-5) : ℤ) : K₃) + (((-1) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-5) (-1) 4 1 0 (-9) 4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps10M : ‖(Jacobs.eps10M ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps10M, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (2 * ν₃ + 2 : K₃) - 1
      = (((1 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le 1 2 1 1 0 15 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps12M1 : ‖(Jacobs.eps12M1 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps12M1, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (-3 / 4 * ν₃ - 1 / 2 : K₃) - 1
      = ((((-6) : ℤ) : K₃) + (((-3) : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-6) (-3) 4 1 0 (-24) 4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps12M2 : ‖(Jacobs.eps12M2 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps12M2, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (1 / 4 * ν₃ : K₃) - 1
      = ((((-4) : ℤ) : K₃) + ((1 : ℤ) : K₃) * ν₃) / ((4 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-4) 1 4 1 0 6 4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps20M1 : ‖(Jacobs.eps20M1 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps20M1, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (6 * ν₃ + 4 : K₃) - 1
      = (((3 : ℤ) : K₃) + ((6 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le 3 6 1 1 0 45 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps20M2 : ‖(Jacobs.eps20M2 ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps20M2, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (-2 * ν₃ : K₃) - 1
      = ((((-1) : ℤ) : K₃) + (((-2) : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le (-1) (-2) 1 1 0 (-15) 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hd_eps21M : ‖(Jacobs.eps21M ν₃) 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  simp only [Jacobs.eps21M, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  rw [show (2 * ν₃ + 2 : K₃) - 1
      = (((1 : ℤ) : K₃) + ((2 : ℤ) : K₃) * ν₃) / ((1 : ℕ) : K₃) by
    ring]
  simpa using norm_frac_le 1 2 1 1 0 15 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem hs_10_1 : ‖((10 : K₃) / (1 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_ten_sub_one_le norm_one_sub_one_le

private theorem hs_28_1 : ‖((28 : K₃) / (1 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_twentyEight_sub_one_le norm_one_sub_one_le

private theorem hs_1_10 : ‖((1 : K₃) / (10 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_one_sub_one_le norm_ten_sub_one_le

private theorem hs_28_10 : ‖((28 : K₃) / (10 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_twentyEight_sub_one_le norm_ten_sub_one_le

private theorem hs_10_28 : ‖((10 : K₃) / (28 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_ten_sub_one_le norm_twentyEight_sub_one_le

private theorem hs_1_28 : ‖((1 : K₃) / (28 : K₃)) - 1‖ ≤ ‖(3 : K₃)‖ :=
  norm_div_sub_one_le norm_one_sub_one_le norm_twentyEight_sub_one_le

/-- **The `ε`-identification, series level** (the form consumed by `04_Matrix.lean`): for
each `(i, j)` with `j ≠ i`, the sum of `weightGenFun tw` over the acting matrices of
`{t' | σ(i,t') = j}` is the transcribed block generating function `h_{i,j}` of
`PhD.Jacobs.U3Data`, up to the handedness scalar `κ(s)·s⁻²`, `s = classDet j / classDet i`
(a `1`-unit — the recorded B15 statement amendment, module header).  Follows from
`adjParams_toMatrix_eq_smul_epsTable` by `Jacobs.weightGenFun_smul` and summing the
fibre, which is why the weight hypothesis `‖tw‖ ≤ 1` now appears.

The scalar is a coboundary in `(i, j)` — it factors as `φⱼ/φᵢ`
(`Jacobs.U3.twist_factor`) — so it cancels from the characteristic power series of the
assembled block matrix and no slope statement is affected (module header, "Why the
twist is harmless"; `Jacobs.U3.charPowerSeries_blockOp_eq_U3MatrixOp`). -/
theorem sum_weightGenFun_eq_h (tw : K₃) (htw : ‖tw‖ ≤ 1) (i j : Fin 3) (hij : j ≠ i) :
    ∑ t' ∈ {t' | sigmaTable i t' = j},
        Jacobs.weightGenFun tw
          (adjParams (toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹)))
      = (Jacobs.unitPow tw ((classDet j : K₃) / (classDet i : K₃)) *
            ((classDet j : K₃) / (classDet i : K₃))⁻¹ *
            ((classDet j : K₃) / (classDet i : K₃))⁻¹) •
          ![![0, Jacobs.h01 tw ν₃, Jacobs.h02 tw ν₃],
            ![Jacobs.h10 tw ν₃, 0, Jacobs.h12 tw ν₃],
            ![Jacobs.h20 tw ν₃, Jacobs.h21 tw ν₃, 0]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cd0, cd1, cd2,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    try exact absurd rfl hij
  · rw [show ({t' | sigmaTable 0 t' = 1} : Finset (Fin 3)) = {2, 1} by decide,
      Finset.sum_pair (by decide), adjParams_acting₀₁, adjParams_acting₀₂,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_10_1 hd_eps01M2,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_10_1 hd_eps01M1,
      Jacobs.h01, ← smul_add]
  · rw [show ({t' | sigmaTable 0 t' = 2} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, adjParams_acting₀₀,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_28_1 hd_eps02M,
      Jacobs.h02]
    rfl
  · rw [show ({t' | sigmaTable 1 t' = 0} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, adjParams_acting₁₀,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_1_10 hd_eps10M,
      Jacobs.h10]
  · rw [show ({t' | sigmaTable 1 t' = 2} : Finset (Fin 3)) = {2, 1} by decide,
      Finset.sum_pair (by decide), adjParams_acting₁₁, adjParams_acting₁₂,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_28_10 hd_eps12M2,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_28_10 hd_eps12M1,
      Jacobs.h12, ← smul_add]
    rfl
  · rw [show ({t' | sigmaTable 2 t' = 0} : Finset (Fin 3)) = {2, 1} by decide,
      Finset.sum_pair (by decide), adjParams_acting₂₁, adjParams_acting₂₂,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_1_28 hd_eps20M2,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_1_28 hd_eps20M1,
      Jacobs.h20, ← smul_add]
    rfl
  · rw [show ({t' | sigmaTable 2 t' = 1} : Finset (Fin 3)) = {0} by decide,
      Finset.sum_singleton, adjParams_acting₂₀,
      Jacobs.weightGenFun_smul norm_three_lt_one htw (by norm_num) hs_10_28 hd_eps21M,
      Jacobs.h21]
    rfl

end Jacobs.U3
