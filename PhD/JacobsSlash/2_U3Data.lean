/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.«1_PadicAnalytic»
import PhD.TateFredholm.GenFun
import PhD.TateFredholm.WeightGenFun
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The matrix of `U₃`: the generating functions `h_{i,j}` ([Jacobs, §2.1])

[Jacobs, *Slopes of Compact Hecke Operators*, §2.1] computes the Hecke operator `U₃` at
level `U₁(9)`, weight `κ`, as a `3 × 3` block matrix of endomorphisms `ε_{i,j}` of the
Tate algebra `A₃`, each given ([Jacobs, Proposition 2.6]) by a generating function

  `h(x, y) = κ(cx + d) / ((cx + d)(cx + d − axy − by))`

for an explicit `2 × 2` matrix `(a b; c d)` over `ℤ₃[ν]`, `ν = √−2 ≡ 508 mod 3⁷`
(displays (2.1.4)–(2.1.9)).  This file records that data over an abstract complete
ultrametric field `K` with `‖3‖ < 1`, elements `ν, ω, t : K` with `ν² = −2`,
`ν ≡ 2695 mod 3¹⁰` (the thesis's substitution p. 39), `ω² + ω + 1 = 0`, `‖t‖ < 1`
(the weight disc `v₃(t) > 0`):

* `JacobsSlash.eps*M*` — the eight matrices read off the `ε_{i,j}` displays (p. 28); the
  second `ε_{1,2}` matrix's `a`-entry is `−5ν/14 − 5/7` per displays (2.1.7)/B.3
  (p. 28 misprints it as `−15/14 ν₃ − 5/7`; the Lemma 2.11 identities force `−5/14`).
* `JacobsSlash.weightGenFun t γ` — the generating function of `‖_κ γ` above.
* `JacobsSlash.h01 … h21` — the six block generating functions (2.1.4)–(2.1.9).
* `JacobsSlash.M22genFun`, `JacobsSlash.M22op` — the eigenblock
  `M₂,₂ = (1/16)ω²κ(4) D(7/4) ε₀,₂ + (1/4)ωκ(−2) D(7/10) ε₁,₂` ([Jacobs, p. 34]).
* [Jacobs, Lemma 2.7] in quantitative form: `‖h(x^m y^r-coeff)‖ ≤ ‖3‖^m`.
* [Jacobs, Lemma 2.11]: the six-way commutation identities among the `h`'s.

## The parameter `ν` (and its hypotheses `hν2`, `hνc`)

`ν` is the abstract stand-in for the thesis's `ν₃ = √−2 ∈ ℤ₃` [Jacobs, p. 22]: the
splitting isomorphism `θ₃ : D ⊗ ℚ₃ ≅ M₂(ℚ₃)` of the quaternion algebra requires elements
with `ν² + ξ² = −1`; the thesis takes `ξ₃ = 1` and `ν₃` the Hensel square root of `−2`
"that is 508 mod 3⁷".  Every entry of the matrices below is a polynomial in this `ν`.
Working over an abstract field `K`, we impose two axioms in place of the concrete root:

* `hν2 : ν ^ 2 = -2` — the defining algebraic identity (which of `±ν` is meant is NOT
  determined by this);
* `hνc : ‖ν - 2695‖ ≤ ‖3‖ ^ 10` — the 3-adic location `ν ≡ 2695 mod 3¹⁰`.  This selects
  the thesis's root (`2695 ≡ 508 mod 3⁷`; `2695` is the thesis's own refined value from
  the p. 39 substitution `ν₃ = 2695 + 3¹⁰S`, consistent since `2695² + 2 = 3¹¹·41`) and
  fixes the first ten 3-adic digits of `ν`, from which the entry-valuation table of
  `section RowIntegrality` is derived (`‖ν−1‖ = ‖3‖`, `‖ν+2‖ ≤ ‖3‖`, `‖ν−4‖ ≤ ‖3‖²`, …)
  — the quantitative inputs to Lemma 2.7's integrality and Theorem 2.14's residue
  computation, which is why the precision is `3¹⁰` and not less.

At instantiation (`K` ⊇ a completion of `ℚ₃(ζ₃)`, `ν` the genuine Hensel root) both
hypotheses become theorems.  Execution note: `hνc` alone suffices for most of the chain
(`hν2` was linter-confirmed unused in Lemmas 2.7/2.13 and Thm 2.14 as proved) — a
future `/generalise` candidate.

## The parameter `ω` (and why `3` is only a *pseudo*-uniformizer)

`ω` is a primitive cube root of unity (`hω : ω ^ 2 + ω + 1 = 0`, i.e. `ω = ζ₃`).  It enters
because `U₃` is a `3 × 3` block matrix whose `ℤ/3`-action diagonalises over `ℚ₃(ζ₃)`:
`M22genFun` below is the `ω²`-eigenblock [Jacobs, p. 34].  So `hω` forces `K ⊇ ℚ₃(ζ₃)`.

That extension is *ramified* of degree `2`, which is why every valuation statement downstream
(`PhD/Jacobs/SlopeReading.lean`) takes a `PseudoUniformizer` `ϖ` with `(ϖ : K) = 3` rather than
a uniformizer: `3` is **not** a uniformizer of `K`.  A uniformizer is `2ω + 1 = √−3`
(`sq_two_omega_add_one`), so `3 = −(2ω + 1)²`, `‖3‖ = ‖2ω + 1‖²` and `v₃(K^×) = (1/2)ℤ`.
`PseudoUniformizer` asks only for a topologically nilpotent unit with multiplicative norm,
which `3` is; it does not ask for a generator of the value group, which `3` is not.  The
ramification is load-bearing: it is exactly what lets `val_charCoeff_M22op` return the
half-integers `m²/2` — over `ℚ₃` no element has `v₃ = 1/2` and all of case B would be vacuous.
(`h3 : ‖(3 : K)‖ < 1`, the residue-characteristic hypothesis threaded through the definitions
below, is the *same* condition seen from the norm side, not a competing one.)

## The identification (PROVED — `PhD.JacobsSlash.U3.Matrix`)

The matrices below are *transcriptions* of the thesis's displays and `weightGenFun` is
Proposition 2.6's closed formula taken as a *definition*, so this file by itself only
makes unconditional statements about explicitly-defined operators.  **That these
definitions really are the matrix of the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on
`L(U₁(9), A₃)` is now a theorem** — everything the thesis proves *before* the displays
(2.1.4)–(2.1.9) has been formalised:

* Theorem 2.1 (`D^×_f = ∐ D^× cᵢ U₁(9)`) — `JacobsSlash.U3.classRep_complete`, and
  Lemma 2.2 (`Γᵢ = 1`) — `JacobsSlash.U3.stabilizerAt_classRep`, both in `PhD.JacobsSlash.U3.ClassSet`;
* Lemma 2.3 (the decomposition of `Uη₃U`) — `JacobsSlash.U3.bijOn_etaRep`
  (`PhD.JacobsSlash.U3.EtaDecomposition`);
* Lemmas 2.4/2.5 and §B.1 (the nine factorisations `cᵢv_t⁻¹ = d·c(i,t)·u(i,t)`) —
  `JacobsSlash.U3.factorisation` and the tables `sigmaTable`/`dTable`/`uTable`
  (`PhD.JacobsSlash.U3.Factorisations`), *recomputed* by exhaustive search
  (`PhD/Jacobs/U3/certificate_search.py`), not transcribed;
* Proposition 2.6 (the generating function of the weight-`κ` action) —
  `JacobsSlash.matrixCoeff_kappaSlash_jacobsWeight` (`PhD.JacobsSlash.U3.«5_KappaWeight»`), whose composition law
  needed the analytic-substitution development of `PhD.JacobsSlash.U3.Compose` and
  `PhD.JacobsSlash.BinomialTheorem`;
* the identification itself — `JacobsSlash.U3.heckeU3_apply_classRep` (unconditional) and
  `JacobsSlash.U3.eval_classRep_injective` (under the class-number-one hypothesis), in
  `PhD.JacobsSlash.U3.Matrix`.

The certificate blocks differ from the `ε`-transcriptions below by a `1`-unit
*coboundary* scalar (the determinant twist; see `U3.Matrix`'s module header for the
decision record).  It is spectrally inert: `JacobsSlash.U3.charPowerSeries_blockOp_eq_U3MatrixOp`
proves that the assembled Hecke matrix and the transcribed `JacobsSlash.U3MatrixOp` have the
*same* characteristic power series, so the Fredholm determinant, eigenvalues and
Newton-polygon slopes computed downstream are those of the genuine `U₃`.

Two independent validations of the transcribed data remain worth recording: Lemma 2.11's
identities and Lemma 2.7's integrality are *proved* from it below (they caught the
thesis misprint at `eps12M2`), and the certificate search reproduced all nine `ε`
displays exactly, with the corrected `a`-entry and never the printed one.

The endgame is also proved: `det(1 − T·U₃)` is packaged as
`JacobsSlash.charPowerSeriesU3` with `charPowerSeriesU3_eq_U3MatrixOp`
(`PhD.JacobsSlash.U3.«7_Fredholm»` — twist-free in this fork's right-slash
orientation), and the eigenblock factorisation
`det(1 − T·U₃) = ∏ₜ det(1 − T·M_{t,t})` holds over every isometric extension
containing `ω`, witnessed at `L₃ = ℚ₃(ζ₃)` (`PhD.JacobsSlash.U3.«8_HeckeSlopes»`).
There are no external sorries: `hClassNumberOne` ([Jacobs, Lemma 1.22]) is proven in
`PhD/JacobsSlash/CN1/` (Voight's Euclidean → principal → idelic-dictionary route);
every consumer carries it as an explicit hypothesis, and none of the factorisation
chain needs it.

## Main definitions

* `JacobsSlash.eps01M1 … JacobsSlash.eps21M`: the nine matrices read off the `ε_{i,j}` displays
  [Jacobs p. 28] — with `eps12M2`'s `a`-entry corrected, see the erratum note above.
* `JacobsSlash.weightGenFun`: the generating function `κ(cx+d)/((cx+d)(cx+d−axy−by))` of the
  weight-`κ` action [Jacobs, Proposition 2.6], taken here as the definition.
* `JacobsSlash.h01 … JacobsSlash.h21`: the six block generating functions (2.1.4)–(2.1.9).
* `JacobsSlash.M22genFun`, `JacobsSlash.M22op`: the `ω²`-eigenblock [Jacobs p. 34].

## Main results

* `JacobsSlash.norm_coeff_h02_le`, `JacobsSlash.norm_coeff_h12_le`: [Jacobs, Lemma 2.7] in
  quantitative form — the `xᵐyʳ` coefficient has norm `≤ ‖3‖ᵐ`, which is what makes the
  blocks compact.
* `JacobsSlash.lemma211_first`, `JacobsSlash.lemma211_first'`, `JacobsSlash.lemma211_second`,
  `JacobsSlash.lemma211_second'`: [Jacobs, Lemma 2.11]'s four commutation identities — the
  internal consistency check that caught the p. 28 misprint.
* `TateFredholm.diagRescale_weightGenFun`, `JacobsSlash.weightGenFun_smul`: the substitution and
  homogeneity calculus the identities above run on.
-/

open TateFredholm MvPowerSeries
open scoped TateFredholm

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section Data

/-!  The eight matrices below are **transcribed** from the thesis's `ε_{i,j}` displays
(p. 28); their derivation (Lemmas 2.3–2.5, §B.1) is proved in `PhD.JacobsSlash.U3.Factorisations`
— see the module header — and their internal consistency is machine-checked by
Lemma 2.7/2.11 below. -/

variable (ν : K)

/-- First matrix of `ε₀,₁` [Jacobs, p. 28]. -/
noncomputable def eps01M1 : Matrix (Fin 2) (Fin 2) K :=
  !![3 / 10 * ν, -1 / 10 * ν + 1 / 5; -1 / 4 * ν + 1, -3 / 4 * ν - 1 / 2]

/-- Second matrix of `ε₀,₁` [Jacobs, p. 28]. -/
noncomputable def eps01M2 : Matrix (Fin 2) (Fin 2) K :=
  !![-1 / 10 * ν - 1 / 5, 1 / 10 * ν + 1 / 5; 1 / 4 * ν - 1, 1 / 4 * ν]

/-- The matrix of `ε₀,₂` [Jacobs, p. 28]. -/
noncomputable def eps02M : Matrix (Fin 2) (Fin 2) K :=
  !![1 / 7 * ν - 1 / 7, 2 / 7; 0, -1 / 4 * ν - 1 / 4]

/-- The matrix of `ε₁,₀` [Jacobs, p. 28]. -/
noncomputable def eps10M : Matrix (Fin 2) (Fin 2) K :=
  !![-5 * ν + 5, -4; 0, 2 * ν + 2]

/-- First matrix of `ε₁,₂` [Jacobs, p. 28]. -/
noncomputable def eps12M1 : Matrix (Fin 2) (Fin 2) K :=
  !![15 / 14 * ν, -1 / 7 * ν + 2 / 7; -5 / 8 * ν + 5 / 2, -3 / 4 * ν - 1 / 2]

/-- Second matrix of `ε₁,₂` [Jacobs, (2.1.7) and §B.3; the `a`-entry `−5ν/14 − 5/7`
corrects the misprint `−15/14 ν₃ − 5/7` on p. 28 — forced by Lemma 2.11]. -/
noncomputable def eps12M2 : Matrix (Fin 2) (Fin 2) K :=
  !![-5 / 14 * ν - 5 / 7, 1 / 7 * ν + 2 / 7; 5 / 8 * ν - 5 / 2, 1 / 4 * ν]

/-- First matrix of `ε₂,₀` [Jacobs, p. 28]. -/
noncomputable def eps20M1 : Matrix (Fin 2) (Fin 2) K :=
  !![-21 / 2 * ν, 2 * ν - 4; 7 / 2 * ν - 14, 6 * ν + 4]

/-- Second matrix of `ε₂,₀` [Jacobs, p. 28]. -/
noncomputable def eps20M2 : Matrix (Fin 2) (Fin 2) K :=
  !![7 / 2 * ν + 7, -2 * ν - 4; -7 / 2 * ν + 14, -2 * ν]

/-- The matrix of `ε₂,₁` [Jacobs, p. 28]. -/
noncomputable def eps21M : Matrix (Fin 2) (Fin 2) K :=
  !![-7 / 5 * ν + 7 / 5, -8 / 5; 0, 2 * ν + 2]

end Data

section WeightGenFun

/- `linSeries` and `quadSeries` (the two universal factors of the weight generating
function) now live in `PhD/TateFredholm/WeightGenFun.lean` (namespace `TateFredholm`),
so the general weight layer can consume them. -/

/-- The power series `κ(cx + d) = κ(d) · ∑ₙ (t choose n) (c/d)ⁿ xⁿ` in two variables
(`y`-degree `0`).  [Jacobs, §2.1 p. 29]: "`κ(cx + d) = (cx + d)^t`", expanded via the
binomial series; this is `Definition 1.27`'s "power series expansion of `κ(cz + d)` at
zero", specialised as in the thesis to `κ = ⟨4⟩ ↦ 4^t` on `1`-units. -/
noncomputable def kappaSeries₂ (t c d : K) : MvPowerSeries (Fin 2) K :=
  fun p => if p 1 = 0 then unitPow t d * (binomialCoeff t (p 0) * (c / d) ^ (p 0)) else 0

set_option linter.unusedSectionVars false in
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The coefficients of `kappaSeries₂` (definitional). -/
@[simp] theorem coeff_kappaSeries₂ (t c d : K) (p : Fin 2 →₀ ℕ) :
    coeff p (kappaSeries₂ t c d) =
      if p 1 = 0 then unitPow t d * (binomialCoeff t (p 0) * (c / d) ^ (p 0)) else 0 :=
  rfl

/-- **The generating function of the weight-`κ` action** `‖_κ (a b; c d)`
[Jacobs, Proposition 2.6]:

  `κ(cx + d) / ((cx + d)(cx + d − axy − by))`.

We take it as the **definition** of the block data.  The thesis derives the formula from
the weight-`κ` action on the basis `e_r` ([Jacobs, proof of Prop. 2.6]); that derivation
is formalised in `JacobsSlash.matrixCoeff_kappaSlash_jacobsWeight` (`PhD.JacobsSlash.U3.«5_KappaWeight»`), which
proves this series really is the generating function of `‖_κ γ` acting on the Tate
algebra, and `JacobsSlash.U3.sum_weightGenFun_eq_h` (`PhD.JacobsSlash.U3.Factorisations`) assembles
the blocks from the certificates.  Inverses are `MvPowerSeries` field inverses — genuine
two-sided inverses whenever `d ≠ 0`. -/
noncomputable def weightGenFun (t : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries (Fin 2) K :=
  kappaSeries₂ t (γ 1 0) (γ 1 1) * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹

variable (t ν : K)

/-- `h₀,₁` [Jacobs, (2.1.4)]. -/
noncomputable def h01 : MvPowerSeries (Fin 2) K :=
  weightGenFun t (eps01M1 ν) + weightGenFun t (eps01M2 ν)

/-- `h₀,₂` [Jacobs, (2.1.5)]. -/
noncomputable def h02 : MvPowerSeries (Fin 2) K := weightGenFun t (eps02M ν)

/-- `h₁,₀` [Jacobs, (2.1.6)]. -/
noncomputable def h10 : MvPowerSeries (Fin 2) K := weightGenFun t (eps10M ν)

/-- `h₁,₂` [Jacobs, (2.1.7)]. -/
noncomputable def h12 : MvPowerSeries (Fin 2) K :=
  weightGenFun t (eps12M1 ν) + weightGenFun t (eps12M2 ν)

/-- `h₂,₀` [Jacobs, (2.1.8)]. -/
noncomputable def h20 : MvPowerSeries (Fin 2) K :=
  weightGenFun t (eps20M1 ν) + weightGenFun t (eps20M2 ν)

/-- `h₂,₁` [Jacobs, (2.1.9)]. -/
noncomputable def h21 : MvPowerSeries (Fin 2) K := weightGenFun t (eps21M ν)

end WeightGenFun

section Omega

/-!
### The cube root of unity `ω = ζ₃`, and the ramification it forces

`hω` puts `ζ₃` in `K` (module header: `ω` indexes the eigenblock of `U₃`), so `K` is ramified
over `ℚ₃`, with `2ω + 1 = ω − ω² = √−3` a uniformizer.  Hence `3 = −(2ω + 1)²` has valuation `2`
in the uniformizer normalisation: it is only a *pseudo*-uniformizer of `K`, and `v₃` takes
half-integer values — the source of the `1/2, 3/2, 5/2, …` slopes downstream.
-/

set_option linter.unusedSectionVars false

variable {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
include hω

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `(2ω + 1)² = −3` for a primitive cube root of unity `ω`: `2ω + 1 = ω − ω²` is `√−3`, the
a uniformizer of `ℚ₃(ζ₃)`, so `3 = −(2ω + 1)²` is a square and is *not* a uniformizer of `K`. -/
theorem sq_two_omega_add_one : (2 * ω + 1) ^ 2 = -3 := by
  linear_combination 4 * hω

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖2ω + 1‖² = ‖3‖` — the ramified valuation `v₃(2ω + 1) = 1/2` in squared-norm form. -/
theorem sq_norm_two_omega_add_one : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := by
  rw [← norm_pow, sq_two_omega_add_one hω, norm_neg]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖ω‖ = 1`. -/
theorem norm_omega : ‖ω‖ = 1 := by
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hn : ‖ω‖ ^ 3 = 1 := by rw [← norm_pow, hcube, norm_one]
  nlinarith [norm_nonneg ω, hn, sq_nonneg (‖ω‖ - 1), sq_nonneg (‖ω‖ + 1)]

end Omega

section RowIntegrality

/-!
### [Jacobs, Lemma 2.7]: the `x^m y^r` coefficients of `h₀,₂`, `h₁,₂` have norm `≤ ‖3‖ ^ m`

The estimate only uses the valuations of the entries `(a b; c d)` of the matrices: `d` is a
`1`-unit (`‖d - 1‖ ≤ ‖3‖`), `‖c‖ ≤ ‖3‖²`, `‖a‖ ≤ ‖3‖` and `‖b‖ ≤ 1`.  Under these bounds all
three factors of `weightGenFun` are *row-integral* (`RowInt` below), a condition preserved by
sums, products, and inverses with unit constant coefficient.
-/

set_option linter.unusedSectionVars false

omit [CompleteSpace K] [CharZero K] in
/-- `‖N‖ = 1` for a numeral `N` coming from a natural number coprime to `3`. -/
lemma norm_ofNat_eq_one (h3 : ‖(3 : K)‖ < 1) {N : K} {n : ℕ} (hn : Nat.Coprime n 3)
    (hN : N = (n : ℕ)) : ‖N‖ = 1 := by
  rw [hN]; exact norm_natCast_eq_one_of_coprime h3 hn

omit [CompleteSpace K] [CharZero K] in
/-- `‖N‖ = ‖3‖ ^ e` for a numeral `N` coming from `n = 3 ^ e * k` with `k` coprime to `3`. -/
lemma norm_ofNat_eq_pow (h3 : ‖(3 : K)‖ < 1) {N : K} {n e k : ℕ} (hk : Nat.Coprime k 3)
    (hn : n = 3 ^ e * k) (hN : N = (n : ℕ)) : ‖N‖ = ‖(3 : K)‖ ^ e := by
  subst hN; subst hn
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_eq_one_of_coprime h3 hk, mul_one]

omit [CompleteSpace K] [CharZero K] in
/-- Ultrametric bookkeeping: `‖x‖ ≤ M` follows from `‖x - y‖ ≤ M` and `‖y‖ ≤ M`. -/
lemma norm_le_of_sub {x y : K} {M : ℝ} (hxy : ‖x - y‖ ≤ M) (hy : ‖y‖ ≤ M) : ‖x‖ ≤ M := by
  have hx : x = x - y + y := by ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxy hy)

omit [CompleteSpace K] [CharZero K] in
/-- Ultrametric bound for differences: `‖x - y‖ ≤ max ‖x‖ ‖y‖`. -/
lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [norm_neg])

omit [CompleteSpace K] [CharZero K] in
/-- The isosceles principle: `‖x‖ = ‖y‖` as soon as `‖x - y‖ < ‖y‖`. -/
lemma norm_eq_of_sub_lt {x y : K} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  refine le_antisymm (norm_le_of_sub h.le le_rfl) ?_
  have h2 : ‖y‖ ≤ max ‖x‖ ‖x - y‖ := by
    have hy : y = x + -(x - y) := by ring
    calc ‖y‖ = ‖x + -(x - y)‖ := by rw [← hy]
      _ ≤ max ‖x‖ ‖-(x - y)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖x‖ ‖x - y‖ := by rw [norm_neg]
  rcases max_cases ‖x‖ ‖x - y‖ with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at h2; exact h2
  · rw [he] at h2; linarith

variable {ν : K}

omit [CompleteSpace K] [CharZero K] in
/-- `2695 = 5 · 7² · 11` is prime to `3`, so `ν` is a unit. -/
lemma norm_nu (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖ν‖ = 1 := by
  have h2695 : ‖(2695 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2695) (by norm_num) (by norm_num)
  have hlt : ‖ν - 2695‖ < ‖(2695 : K)‖ := by
    rw [h2695]; exact hνc.trans_lt (pow_lt_one₀ (norm_nonneg _) h3 (by norm_num))
  rw [norm_eq_of_sub_lt hlt, h2695]

omit [CompleteSpace K] [CharZero K] in
/-- `2696 = 2³ · 337` is prime to `3`. -/
lemma norm_nu_add_one (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    ‖ν + 1‖ = 1 := by
  have h2696 : ‖(2696 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2696) (by norm_num) (by norm_num)
  have hlt : ‖ν + 1 - 2696‖ < ‖(2696 : K)‖ := by
    rw [show ν + 1 - 2696 = ν - 2695 by ring, h2696]
    exact hνc.trans_lt (pow_lt_one₀ (norm_nonneg _) h3 (by norm_num))
  rw [norm_eq_of_sub_lt hlt, h2696]

omit [CompleteSpace K] [CharZero K] in
/-- `2694 = 3 · 898`. -/
lemma norm_nu_sub_one (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    ‖ν - 1‖ ≤ ‖(3 : K)‖ := by
  have h2694 : ‖(2694 : K)‖ = ‖(3 : K)‖ ^ 1 :=
    norm_ofNat_eq_pow h3 (n := 2694) (e := 1) (k := 898) (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one] at h2694
  refine norm_le_of_sub (y := (2694 : K)) ?_ h2694.le
  rw [show ν - 1 - 2694 = ν - 2695 by ring]
  exact hνc.trans (by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 10))

omit [CompleteSpace K] [CharZero K] in
/-- `2697 = 3 · 29 · 31`. -/
lemma norm_nu_add_two (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    ‖ν + 2‖ ≤ ‖(3 : K)‖ := by
  have h2697 : ‖(2697 : K)‖ = ‖(3 : K)‖ ^ 1 :=
    norm_ofNat_eq_pow h3 (n := 2697) (e := 1) (k := 899) (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one] at h2697
  refine norm_le_of_sub (y := (2697 : K)) ?_ h2697.le
  rw [show ν + 2 - 2697 = ν - 2695 by ring]
  exact hνc.trans (by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 10))

omit [CompleteSpace K] [CharZero K] in
/-- `2691 = 3² · 13 · 23`. -/
lemma norm_nu_sub_four (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    ‖ν - 4‖ ≤ ‖(3 : K)‖ ^ 2 := by
  have h2691 : ‖(2691 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 2691) (e := 2) (k := 299) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (2691 : K)) ?_ h2691.le
  rw [show ν - 4 - 2691 = ν - 2695 by ring]
  exact hνc.trans (pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num))

omit [CompleteSpace K] [CharZero K] in
/-- `2700 = 3³ · 100`. -/
lemma norm_nu_add_five (h3 : ‖(3 : K)‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    ‖ν + 5‖ ≤ ‖(3 : K)‖ := by
  have h2700 : ‖(2700 : K)‖ = ‖(3 : K)‖ ^ 3 :=
    norm_ofNat_eq_pow h3 (n := 2700) (e := 3) (k := 100) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (2700 : K)) ?_ ?_
  · rw [show ν + 5 - 2700 = ν - 2695 by ring]
    exact hνc.trans (by
      simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 10))
  · rw [h2700]
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 3)

omit [CompleteSpace K] [CharZero K] in
/-- `‖3 ν‖ = ‖3‖ < 1 = ‖2‖`, so `3 ν + 2` is a unit. -/
lemma norm_three_mul_nu_add_two (h3 : ‖(3 : K)‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖3 * ν + 2‖ = 1 := by
  have h2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hlt : ‖3 * ν + 2 - 2‖ < ‖(2 : K)‖ := by
    rw [show 3 * ν + 2 - 2 = 3 * ν by ring, norm_mul, norm_nu h3 hνc, mul_one, h2]
    exact h3
  rw [norm_eq_of_sub_lt hlt, h2]

/-- **Row integrality**: the `x^m y^r` coefficient has norm at most `‖3‖ ^ m`, i.e. the series
becomes integral after the substitution `x ↦ x / 3` ([Jacobs, Lemma 2.7]). -/
def RowInt (φ : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖coeff p φ‖ ≤ ‖(3 : K)‖ ^ p 0

/- `fin2_eq_zero` moved to `PhD/TateFredholm/WeightGenFun.lean`. -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A monomial whose coefficient obeys the row bound is row-integral. -/
lemma rowInt_monomial {n : Fin 2 →₀ ℕ} {v : K} (hv : ‖v‖ ≤ ‖(3 : K)‖ ^ n 0) :
    RowInt (monomial n v : MvPowerSeries (Fin 2) K) := by
  intro p
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact hv
  · simp [pow_nonneg (norm_nonneg (3 : K)) (p 0)]

omit [CompleteSpace K] [CharZero K] in
/-- Row integrality is preserved by sums (the ultrametric inequality). -/
lemma rowInt_add {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowInt φ) (hψ : RowInt ψ) :
    RowInt (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Row integrality is preserved by negation. -/
lemma rowInt_neg {φ : MvPowerSeries (Fin 2) K} (hφ : RowInt φ) : RowInt (-φ) := fun p => by
  rw [map_neg, norm_neg]; exact hφ p

omit [CompleteSpace K] [CharZero K] in
/-- Row integrality is preserved by differences. -/
lemma rowInt_sub {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowInt φ) (hψ : RowInt ψ) :
    RowInt (φ - ψ) := by
  rw [sub_eq_add_neg]; exact rowInt_add hφ (rowInt_neg hψ)

omit [CompleteSpace K] [CharZero K] in
/-- Row integrality is multiplicative: the `x`-degrees add along the antidiagonal. -/
lemma rowInt_mul {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowInt φ) (hψ : RowInt ψ) :
    RowInt (φ * ψ) := by
  intro p
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg (norm_nonneg _) _) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have h0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
  calc ‖coeff x.1 φ * coeff x.2 ψ‖ ≤ ‖(3 : K)‖ ^ x.1 0 * ‖(3 : K)‖ ^ x.2 0 := by
        rw [norm_mul]
        exact mul_le_mul (hφ _) (hψ _) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = ‖(3 : K)‖ ^ p 0 := by rw [← pow_add, h0]

omit [CompleteSpace K] [CharZero K] in
/-- Row integrality passes to inverses with unit constant coefficient: strong induction on
`p 0 + p 1` through the recurrence `MvPowerSeries.coeff_inv`. -/
lemma rowInt_inv {φ : MvPowerSeries (Fin 2) K} (hφ : RowInt φ)
    (h1 : ‖constantCoeff φ‖ = 1) : RowInt φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → ‖coeff p φ⁻¹‖ ≤ ‖(3 : K)‖ ^ p 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (pow_nonneg (norm_nonneg _) _) fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
          have hne : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with h | h
            · exact absurd (fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          calc ‖coeff x.1 φ * coeff x.2 φ⁻¹‖ ≤ ‖(3 : K)‖ ^ x.1 0 * ‖(3 : K)‖ ^ x.2 0 := by
                rw [norm_mul]
                exact mul_le_mul (hφ _) (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
                  (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
            _ = ‖(3 : K)‖ ^ p 0 := by rw [← pow_add, e0]
        · simp [pow_nonneg (norm_nonneg (3 : K)) (p 0)]
  exact fun p => key _ p rfl

/- `linSeries_eq` / `quadSeries_eq` moved to `PhD/TateFredholm/WeightGenFun.lean`. -/

omit [CompleteSpace K] [CharZero K] in
/-- The linear factor is row-integral when `‖d‖ ≤ 1` and `‖c‖ ≤ ‖3‖`. -/
lemma rowInt_linSeries {γ : Matrix (Fin 2) (Fin 2) K} (hd : ‖γ 1 1‖ ≤ 1)
    (hc : ‖γ 1 0‖ ≤ ‖(3 : K)‖) : RowInt (linSeries γ) := by
  rw [linSeries_eq]
  refine rowInt_add (rowInt_monomial ?_) (rowInt_monomial ?_)
  · simpa using hd
  · simpa using hc

omit [CompleteSpace K] [CharZero K] in
/-- The quadratic factor is row-integral under the entry bounds of [Jacobs, Lemma 2.7]. -/
lemma rowInt_quadSeries {γ : Matrix (Fin 2) (Fin 2) K} (hd : ‖γ 1 1‖ ≤ 1)
    (hc : ‖γ 1 0‖ ≤ ‖(3 : K)‖) (ha : ‖γ 0 0‖ ≤ ‖(3 : K)‖) (hb : ‖γ 0 1‖ ≤ 1) :
    RowInt (quadSeries γ) := by
  rw [quadSeries_eq]
  refine rowInt_sub (rowInt_sub (rowInt_add (rowInt_monomial ?_) (rowInt_monomial ?_))
    (rowInt_monomial ?_)) (rowInt_monomial ?_)
  · simpa using hd
  · simpa using hc
  · simpa using ha
  · simpa using hb

/- `constantCoeff_linSeries` / `constantCoeff_quadSeries` moved to
`PhD/TateFredholm/WeightGenFun.lean`. -/

omit [CompleteSpace K] [CharZero K] in
/-- `‖3‖ ^ n ≤ ‖n !‖`: the unsquared form of `sq_norm_factorial_ge` (`v₃(n!) ≤ n`). -/
lemma norm_pow_le_norm_factorial (h3 : ‖(3 : K)‖ < 1) (n : ℕ) :
    ‖(3 : K)‖ ^ n ≤ ‖((Nat.factorial n : ℕ) : K)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hsq := sq_norm_factorial_ge h3 hn
    have h1 : ‖(3 : K)‖ ^ (n * 2) ≤ ‖(3 : K)‖ ^ (n - 1) :=
      pow_le_pow_of_le_one (norm_nonneg _) h3.le (by omega)
    refine (pow_le_pow_iff_left₀ (pow_nonneg (norm_nonneg _) _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [← pow_mul]
    exact h1.trans hsq

omit [CompleteSpace K] in
/-- The binomial term of `κ(cx + d)` decays like `‖3‖ ^ n` as soon as `‖c/d‖ ≤ ‖3‖²`:
`‖(t choose n) eⁿ‖ ≤ ‖3‖^{2n} / ‖n !‖ ≤ ‖3‖^{2n} / ‖3‖^n`. -/
lemma norm_binomialCoeff_mul_pow_le (h3 : ‖(3 : K)‖ < 1) {t e : K} (ht : ‖t‖ ≤ 1)
    (he : ‖e‖ ≤ ‖(3 : K)‖ ^ 2) (n : ℕ) : ‖binomialCoeff t n * e ^ n‖ ≤ ‖(3 : K)‖ ^ n := by
  have hfac : (0 : ℝ) < ‖((Nat.factorial n : ℕ) : K)‖ := by
    rw [norm_pos_iff, Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero n
  have hprod : ‖∏ k ∈ Finset.range n, (t - (k : K))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun k _ => norm_nonneg _) fun k _ => ?_
    exact (norm_sub_le_max' _ _).trans (max_le ht (IsUltrametricDist.norm_natCast_le_one K k))
  have hpow : ‖e ^ n‖ ≤ ‖(3 : K)‖ ^ (2 * n) := by
    rw [norm_pow, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) he n
  have key : ‖binomialCoeff t n * e ^ n‖
      = ‖∏ k ∈ Finset.range n, (t - (k : K))‖ * ‖e ^ n‖ / ‖((Nat.factorial n : ℕ) : K)‖ := by
    rw [binomialCoeff, div_mul_eq_mul_div, norm_div, norm_mul]
  rw [key, div_le_iff₀ hfac]
  calc ‖∏ k ∈ Finset.range n, (t - (k : K))‖ * ‖e ^ n‖ ≤ 1 * ‖(3 : K)‖ ^ (2 * n) :=
        mul_le_mul hprod hpow (norm_nonneg _) zero_le_one
    _ = ‖(3 : K)‖ ^ n * ‖(3 : K)‖ ^ n := by rw [one_mul, two_mul, pow_add]
    _ ≤ ‖(3 : K)‖ ^ n * ‖((Nat.factorial n : ℕ) : K)‖ :=
        mul_le_mul_of_nonneg_left (norm_pow_le_norm_factorial h3 n) (pow_nonneg (norm_nonneg _) _)

/-- `κ(d) = d^t` is a unit for a `1`-unit `d`. -/
lemma norm_unitPow_le_one (h3 : ‖(3 : K)‖ < 1) {t d : K} (ht : ‖t‖ < 1)
    (hd : ‖d - 1‖ ≤ ‖(3 : K)‖) : ‖unitPow t d‖ ≤ 1 := by
  refine norm_le_of_sub ((norm_unitPow_sub_one_le h3 ht hd).trans ?_) norm_one.le
  nlinarith [norm_nonneg t, norm_nonneg (3 : K)]

/-- The `κ`-series is row-integral for `‖t‖ < 1`, a `1`-unit `d` and `‖c/d‖ ≤ ‖3‖²`. -/
lemma rowInt_kappaSeries₂ (h3 : ‖(3 : K)‖ < 1) {t c d : K} (ht : ‖t‖ < 1)
    (hd : ‖d - 1‖ ≤ ‖(3 : K)‖) (hcd : ‖c / d‖ ≤ ‖(3 : K)‖ ^ 2) :
    RowInt (kappaSeries₂ t c d) := by
  intro p
  rw [coeff_kappaSeries₂]
  split_ifs with h
  · calc ‖unitPow t d * (binomialCoeff t (p 0) * (c / d) ^ p 0)‖
        = ‖unitPow t d‖ * ‖binomialCoeff t (p 0) * (c / d) ^ p 0‖ := norm_mul _ _
      _ ≤ 1 * ‖(3 : K)‖ ^ p 0 :=
          mul_le_mul (norm_unitPow_le_one h3 ht hd)
            (norm_binomialCoeff_mul_pow_le h3 ht.le hcd _) (norm_nonneg _) zero_le_one
      _ = ‖(3 : K)‖ ^ p 0 := one_mul _
  · simp [pow_nonneg (norm_nonneg (3 : K)) (p 0)]

/-- **[Jacobs, Lemma 2.7]**, uniform form: a weight generating function is row-integral as soon
as `d` is a `1`-unit, `‖c‖ ≤ ‖3‖²`, `‖a‖ ≤ ‖3‖` and `‖b‖ ≤ 1`. -/
lemma rowInt_weightGenFun (h3 : ‖(3 : K)‖ < 1) {t : K} (ht : ‖t‖ < 1)
    (γ : Matrix (Fin 2) (Fin 2) K) (hd : ‖γ 1 1‖ = 1) (hd1 : ‖γ 1 1 - 1‖ ≤ ‖(3 : K)‖)
    (hc : ‖γ 1 0‖ ≤ ‖(3 : K)‖ ^ 2) (ha : ‖γ 0 0‖ ≤ ‖(3 : K)‖) (hb : ‖γ 0 1‖ ≤ 1) :
    RowInt (weightGenFun t γ) := by
  have hsq : ‖(3 : K)‖ ^ 2 ≤ ‖(3 : K)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 2)
  have hcd : ‖γ 1 0 / γ 1 1‖ ≤ ‖(3 : K)‖ ^ 2 := by rw [norm_div, hd, div_one]; exact hc
  rw [weightGenFun]
  exact rowInt_mul (rowInt_mul (rowInt_kappaSeries₂ h3 ht hd1 hcd)
      (rowInt_inv (rowInt_linSeries hd.le (hc.trans hsq))
        (by rw [constantCoeff_linSeries]; exact hd)))
    (rowInt_inv (rowInt_quadSeries hd.le (hc.trans hsq) ha hb)
      (by rw [constantCoeff_quadSeries]; exact hd))

/-- `ε₀,₂`: `(a b; c d) = ((ν-1)/7, 2/7; 0, -(ν+1)/4)`. -/
lemma rowInt_h02 (h3 : ‖(3 : K)‖ < 1) {t : K} (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps02M ν)) := by
  have h2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have h4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have h7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have e00 : eps02M ν 0 0 = 1 / 7 * ν - 1 / 7 := by simp [eps02M]
  have e01 : eps02M ν 0 1 = 2 / 7 := by simp [eps02M]
  have e10 : eps02M ν 1 0 = 0 := by simp [eps02M]
  have e11 : eps02M ν 1 1 = -1 / 4 * ν - 1 / 4 := by simp [eps02M]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (-1 / 4 * ν - 1 / 4 : K) = -((ν + 1) / 4) by ring, norm_neg, norm_div,
      norm_nu_add_one h3 hνc, h4, div_one]
  · rw [e11, show (-1 / 4 * ν - 1 / 4 - 1 : K) = -((ν + 5) / 4) by ring, norm_neg, norm_div, h4,
      div_one]
    exact norm_nu_add_five h3 hνc
  · rw [e10, norm_zero]
    exact pow_nonneg (norm_nonneg _) 2
  · rw [e00, show (1 / 7 * ν - 1 / 7 : K) = (ν - 1) / 7 by ring, norm_div, h7, div_one]
    exact norm_nu_sub_one h3 hνc
  · have hb : ‖eps02M ν 0 1‖ = 1 := by rw [e01, norm_div, h2, h7, div_one]
    exact hb.le

/-- First matrix of `ε₁,₂`: `(a b; c d) = (15ν/14, -(ν-2)/7; -5(ν-4)/8, -(3ν+2)/4)`. -/
lemma rowInt_h12M1 (h3 : ‖(3 : K)‖ < 1) {t : K} (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps12M1 ν)) := by
  have h2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have h4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have h5 : ‖(5 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 5) (by norm_num) (by norm_num)
  have h7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have h8 : ‖(8 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 8) (by norm_num) (by norm_num)
  have h14 : ‖(14 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 14) (by norm_num) (by norm_num)
  have e00 : eps12M1 ν 0 0 = 15 / 14 * ν := by simp [eps12M1]
  have e01 : eps12M1 ν 0 1 = -1 / 7 * ν + 2 / 7 := by simp [eps12M1]
  have e10 : eps12M1 ν 1 0 = -5 / 8 * ν + 5 / 2 := by simp [eps12M1]
  have e11 : eps12M1 ν 1 1 = -3 / 4 * ν - 1 / 2 := by simp [eps12M1]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (-3 / 4 * ν - 1 / 2 : K) = -((3 * ν + 2) / 4) by ring, norm_neg, norm_div,
      norm_three_mul_nu_add_two h3 hνc, h4, div_one]
  · rw [e11, show (-3 / 4 * ν - 1 / 2 - 1 : K) = -(3 * (ν + 2) / 4) by ring, norm_neg, norm_div,
      h4, div_one, norm_mul]
    calc ‖(3 : K)‖ * ‖ν + 2‖ ≤ ‖(3 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((norm_nu_add_two h3 hνc).trans h3.le) (norm_nonneg _)
      _ = ‖(3 : K)‖ := mul_one _
  · rw [e10, show (-5 / 8 * ν + 5 / 2 : K) = -(5 * (ν - 4) / 8) by ring, norm_neg, norm_div, h8,
      div_one, norm_mul, h5, one_mul]
    exact norm_nu_sub_four h3 hνc
  · have ha : ‖eps12M1 ν 0 0‖ = ‖(3 : K)‖ := by
      rw [e00, show (15 / 14 * ν : K) = 3 * (5 * ν) / 14 by ring, norm_div, h14, div_one,
        norm_mul, norm_mul, h5, one_mul, norm_nu h3 hνc, mul_one]
    exact ha.le
  · rw [e01, show (-1 / 7 * ν + 2 / 7 : K) = -((ν - 2) / 7) by ring, norm_neg, norm_div, h7,
      div_one]
    exact (norm_sub_le_max' _ _).trans (by rw [norm_nu h3 hνc, h2]; simp)

/-- Second matrix of `ε₁,₂`: `(a b; c d) = (-5(ν+2)/14, (ν+2)/7; 5(ν-4)/8, ν/4)`. -/
lemma rowInt_h12M2 (h3 : ‖(3 : K)‖ < 1) {t : K} (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps12M2 ν)) := by
  have hsq : ‖(3 : K)‖ ^ 2 ≤ ‖(3 : K)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 2)
  have h4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have h5 : ‖(5 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 5) (by norm_num) (by norm_num)
  have h7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have h8 : ‖(8 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 8) (by norm_num) (by norm_num)
  have h14 : ‖(14 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 14) (by norm_num) (by norm_num)
  have e00 : eps12M2 ν 0 0 = -5 / 14 * ν - 5 / 7 := by simp [eps12M2]
  have e01 : eps12M2 ν 0 1 = 1 / 7 * ν + 2 / 7 := by simp [eps12M2]
  have e10 : eps12M2 ν 1 0 = 5 / 8 * ν - 5 / 2 := by simp [eps12M2]
  have e11 : eps12M2 ν 1 1 = 1 / 4 * ν := by simp [eps12M2]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (1 / 4 * ν : K) = ν / 4 by ring, norm_div, norm_nu h3 hνc, h4, div_one]
  · rw [e11, show (1 / 4 * ν - 1 : K) = (ν - 4) / 4 by ring, norm_div, h4, div_one]
    exact (norm_nu_sub_four h3 hνc).trans hsq
  · rw [e10, show (5 / 8 * ν - 5 / 2 : K) = 5 * (ν - 4) / 8 by ring, norm_div, h8, div_one,
      norm_mul, h5, one_mul]
    exact norm_nu_sub_four h3 hνc
  · rw [e00, show (-5 / 14 * ν - 5 / 7 : K) = -(5 * (ν + 2) / 14) by ring, norm_neg, norm_div,
      h14, div_one, norm_mul, h5, one_mul]
    exact norm_nu_add_two h3 hνc
  · rw [e01, show (1 / 7 * ν + 2 / 7 : K) = (ν + 2) / 7 by ring, norm_div, h7, div_one]
    exact (norm_nu_add_two h3 hνc).trans h3.le

end RowIntegrality

section Integrality

variable {t ν : K} (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
  (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)
include h3 ht hνc

/-- **[Jacobs, Lemma 2.7]** for `ε₀,₂`, quantitative form: the `x^m y^r` coefficient of
`h₀,₂` has norm `≤ ‖3‖ ^ m` (i.e. `h₀,₂(x/3, y)` is integral, whence `D(1/3) ε₀,₂` is
integral and `ε₀,₂` is compact by Corollary 1.10). -/
theorem norm_coeff_h02_le (m r : ℕ) :
    ‖coeff (idx m r) (h02 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_h02 h3 ht hνc (idx m r)
  rw [idx_apply_zero] at h
  exact h

/-- **[Jacobs, Lemma 2.7]** for `ε₁,₂`, quantitative form. -/
theorem norm_coeff_h12_le (m r : ℕ) :
    ‖coeff (idx m r) (h12 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_add (rowInt_h12M1 h3 ht hνc) (rowInt_h12M2 h3 ht hνc) (idx m r)
  rw [idx_apply_zero] at h
  exact h

end Integrality

section Rescale

/-!
### The substitution calculus behind [Jacobs, Lemma 2.11]

`diagRescale α β` is the substitution `F ↦ F(αx, βy)`.  Applied to `weightGenFun t γ` it acts on
the matrix by `(a b; c d) ↦ (αβ a, β b; α c, d)` (`rescaleMat`), and multiplying *all four*
entries of `γ` by a `1`-unit `s` multiplies `weightGenFun t γ` by `κ(s) s⁻²` (`weightGenFun_smul`;
one `s⁻¹` from each of the two denominators).  Together these reduce each of the four identities
of [Jacobs, Lemma 2.11] to an entrywise identity of `2 × 2` matrices plus one `unitPow`
multiplicativity step.
-/

set_option linter.unusedSectionVars false

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `diagRescale` kills the zero series. -/
lemma diagRescale_zero (α β : K) :
    diagRescale α β (0 : MvPowerSeries (Fin 2) K) = 0 := by
  ext p
  simp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `diagRescale` is compatible with differences. -/
lemma diagRescale_sub (α β : K) (F G : MvPowerSeries (Fin 2) K) :
    diagRescale α β (F - G) = diagRescale α β F - diagRescale α β G := by
  ext p
  simp only [coeff_diagRescale, map_sub]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Rescaling fixes the constant coefficient. -/
lemma constantCoeff_diagRescale (α β : K) (F : MvPowerSeries (Fin 2) K) :
    constantCoeff (diagRescale α β F) = constantCoeff F := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_diagRescale]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Rescaling commutes with inversion: both sides invert the same constant coefficient. -/
lemma diagRescale_inv (α β : K) (F : MvPowerSeries (Fin 2) K) :
    diagRescale α β F⁻¹ = (diagRescale α β F)⁻¹ := by
  rcases eq_or_ne (constantCoeff F) 0 with h | h
  · rw [MvPowerSeries.inv_eq_zero.mpr h, diagRescale_zero,
      MvPowerSeries.inv_eq_zero.mpr (by rw [constantCoeff_diagRescale]; exact h)]
  · rw [MvPowerSeries.eq_inv_iff_mul_eq_one (by rwa [constantCoeff_diagRescale]),
      ← diagRescale_mul, MvPowerSeries.inv_mul_cancel _ h, diagRescale_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Rescaling a monomial multiplies its coefficient by `α ^ (x-degree) * β ^ (y-degree)`. -/
lemma diagRescale_monomial (α β : K) (n : Fin 2 →₀ ℕ) (v : K) :
    diagRescale α β (monomial n v : MvPowerSeries (Fin 2) K) =
      monomial n (α ^ n 0 * β ^ n 1 * v) := by
  ext p
  rw [coeff_diagRescale, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- The matrix of the rescaled weight generating function: `F(αx, βy)` for
`F = weightGenFun t (a b; c d)` is `weightGenFun t (αβ a, β b; α c, d)`. -/
noncomputable def rescaleMat (α β : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![α * β * γ 0 0, β * γ 0 1; α * γ 1 0, γ 1 1]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `c`-entry of `rescaleMat` picks up the factor `α`. -/
lemma rescaleMat_apply_one_zero (α β : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    rescaleMat α β γ 1 0 = α * γ 1 0 := by simp [rescaleMat]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `d`-entry of `rescaleMat` is unchanged. -/
lemma rescaleMat_apply_one_one (α β : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    rescaleMat α β γ 1 1 = γ 1 1 := by simp [rescaleMat]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Rescaling the linear factor rescales its matrix. -/
lemma diagRescale_linSeries (α β : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    diagRescale α β (linSeries γ) = linSeries (rescaleMat α β γ) := by
  rw [linSeries_eq, diagRescale_add, diagRescale_monomial, diagRescale_monomial, linSeries_eq]
  simp [rescaleMat]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Rescaling the quadratic factor rescales its matrix. -/
lemma diagRescale_quadSeries (α β : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    diagRescale α β (quadSeries γ) = quadSeries (rescaleMat α β γ) := by
  rw [quadSeries_eq, diagRescale_sub, diagRescale_sub, diagRescale_add, diagRescale_monomial,
    diagRescale_monomial, diagRescale_monomial, diagRescale_monomial, quadSeries_eq]
  simp [rescaleMat]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The substitution `x ↦ αx` scales the ratio `c/d` of the `κ`-series by `α`. -/
lemma diagRescale_kappaSeries₂ (α β t c d : K) :
    diagRescale α β (kappaSeries₂ t c d) = kappaSeries₂ t (α * c) d := by
  ext p
  rw [coeff_diagRescale, coeff_kappaSeries₂, coeff_kappaSeries₂]
  split_ifs with h
  · have hpow : (α * c / d) ^ p 0 = α ^ p 0 * (c / d) ^ p 0 := by rw [mul_div_assoc, mul_pow]
    rw [h, pow_zero, mul_one, hpow]
    ring
  · rw [mul_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[Jacobs, Proposition 1.3] for the weight generating functions**: the substitution
`x ↦ αx`, `y ↦ βy` acts on the defining matrix by `(a b; c d) ↦ (αβ a, β b; α c, d)`. -/
lemma diagRescale_weightGenFun (α β t : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    diagRescale α β (weightGenFun t γ) = weightGenFun t (rescaleMat α β γ) := by
  rw [weightGenFun, weightGenFun, rescaleMat_apply_one_zero, rescaleMat_apply_one_one,
    diagRescale_mul, diagRescale_mul, diagRescale_kappaSeries₂, diagRescale_inv, diagRescale_inv,
    diagRescale_linSeries, diagRescale_quadSeries]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `linSeries` is homogeneous in the matrix. -/
lemma linSeries_smul (s : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    linSeries (s • γ) = s • linSeries γ := by
  rw [linSeries, linSeries, MvPowerSeries.smul_eq_C_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `quadSeries` is homogeneous in the matrix. -/
lemma quadSeries_smul (s : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    quadSeries (s • γ) = s • quadSeries γ := by
  rw [quadSeries, quadSeries, MvPowerSeries.smul_eq_C_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

/-- `κ(s c x + s d) = κ(s) κ(c x + d)`: scaling the linear form by a `1`-unit multiplies the
`κ`-series by the scalar `κ(s)` (the ratio `c/d` is unchanged). -/
lemma kappaSeries₂_smul (h3 : ‖(3 : K)‖ < 1) {t s c d : K} (ht : ‖t‖ ≤ 1) (hs0 : s ≠ 0)
    (hs : ‖s - 1‖ ≤ ‖(3 : K)‖) (hd : ‖d - 1‖ ≤ ‖(3 : K)‖) :
    kappaSeries₂ t (s * c) (s * d) = unitPow t s • kappaSeries₂ t c d := by
  ext p
  rw [MvPowerSeries.coeff_smul, coeff_kappaSeries₂, coeff_kappaSeries₂]
  split_ifs with h
  · rw [unitPow_mul h3 ht hs hd, mul_div_mul_left _ _ hs0]
    ring
  · rw [mul_zero]

/-- **Homogeneity**: scaling all four entries of `γ` by a `1`-unit `s` multiplies the weight
generating function by `κ(s) s⁻²` — one `s⁻¹` from each of the two denominators. -/
lemma weightGenFun_smul (h3 : ‖(3 : K)‖ < 1) {t s : K} (ht : ‖t‖ ≤ 1) (hs0 : s ≠ 0)
    (hs : ‖s - 1‖ ≤ ‖(3 : K)‖) {γ : Matrix (Fin 2) (Fin 2) K}
    (hd : ‖γ 1 1 - 1‖ ≤ ‖(3 : K)‖) :
    weightGenFun t (s • γ) = (unitPow t s * s⁻¹ * s⁻¹) • weightGenFun t γ := by
  have e10 : (s • γ) 1 0 = s * γ 1 0 := rfl
  have e11 : (s • γ) 1 1 = s * γ 1 1 := rfl
  rw [weightGenFun, weightGenFun, e10, e11, kappaSeries₂_smul h3 ht hs0 hs hd, linSeries_smul,
    quadSeries_smul, MvPowerSeries.smul_inv, MvPowerSeries.smul_inv]
  simp only [MvPowerSeries.smul_eq_C_mul, map_mul]
  ring

/- The scale factor `-8` of [Jacobs, Lemma 2.11]: both chains match their two sides
through the entrywise scaling
`s = -8`, computed from the matrices themselves (`hR`, `hA`, `hB` below).  It is a `1`-unit
because `‖-8 - 1‖ = ‖-9‖ = ‖3‖² ≤ ‖3‖`. -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `-8 ≠ 0` in characteristic zero. -/
lemma neg_eight_ne_zero : (-8 : K) ≠ 0 := by norm_num

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `-8` is a `1`-unit: `‖-8 - 1‖ = ‖3‖² ≤ ‖3‖`. -/
lemma norm_neg_eight_sub_one (h3 : ‖(3 : K)‖ < 1) : ‖(-8 : K) - 1‖ ≤ ‖(3 : K)‖ := by
  rw [show ((-8 : K) - 1) = -(3 * 3) by norm_num, norm_neg, norm_mul]
  nlinarith [norm_nonneg (3 : K)]

end Rescale

section Lemma211

set_option linter.unusedSectionVars false

variable {t ν : K} (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
  (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)
include h3 ht hνc

/-- **[Jacobs, Lemma 2.11], first chain**:
`(1/16) κ(4) h₀,₂(7x/4, y) = 4 κ(−1/2) h₂,₁(x, 10y/7)`.

Both sides are `weightGenFun` of a single matrix up to scalars: `h₂,₁(x, 10y/7)`'s matrix is
`(-8)` times `h₀,₂(7x/4, y)`'s, and `(-1/2) · (-8) = 4` matches the two `κ`-arguments. -/
theorem lemma211_first :
    ((16 : K)⁻¹ * unitPow t 4) • diagRescale ((7 : K) / 4) 1 (h02 t ν) =
      ((4 : K) * unitPow t (-1 / 2)) • diagRescale 1 ((10 : K) / 7) (h21 t ν) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hhalf : ‖(-1 / 2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show ((-1 / 2 : K) - 1) = -(3 / 2) by norm_num, norm_neg, norm_div, hn2, div_one]
  have e11 : eps02M ν 1 1 = -1 / 4 * ν - 1 / 4 := by simp [eps02M]
  have hd : ‖rescaleMat ((7 : K) / 4) 1 (eps02M ν) 1 1 - 1‖ ≤ ‖(3 : K)‖ := by
    rw [rescaleMat_apply_one_one, e11,
      show (-1 / 4 * ν - 1 / 4 - 1 : K) = -((ν + 5) / 4) by ring, norm_neg, norm_div, hn4, div_one]
    exact norm_nu_add_five h3 hνc
  have hR : rescaleMat (1 : K) ((10 : K) / 7) (eps21M ν) =
      (-8 : K) • rescaleMat ((7 : K) / 4) 1 (eps02M ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps02M, eps21M] <;> ring
  have hscal : (16 : K)⁻¹ * unitPow t 4 =
      (4 : K) * unitPow t (-1 / 2) * (unitPow t (-8) * (-8 : K)⁻¹ * (-8 : K)⁻¹) := by
    have hmul : unitPow t ((-1 / 2 : K) * (-8)) = unitPow t (-1 / 2) * unitPow t (-8) :=
      unitPow_mul h3 ht.le hhalf (norm_neg_eight_sub_one h3)
    rw [show ((-1 / 2 : K) * (-8)) = 4 by norm_num] at hmul
    rw [hmul]
    field_simp
    ring
  simp only [h02, h21, diagRescale_weightGenFun, hR,
    weightGenFun_smul h3 ht.le neg_eight_ne_zero (norm_neg_eight_sub_one h3) hd, smul_smul,
    ← hscal]

omit [IsUltrametricDist K] [CompleteSpace K] in
omit h3 ht hνc in
/-- **[Jacobs, Lemma 2.11], first chain, second equality**:
`4 κ(−1/2) h₂,₁(x, 10y/7) = 4 κ(−1/2) h₁,₀(7x/10, 4y/7)`.

Here the two rescaled matrices are *equal* (scale factor `1`), so no `κ`-bookkeeping occurs. -/
theorem lemma211_first' :
    ((4 : K) * unitPow t (-1 / 2)) • diagRescale 1 ((10 : K) / 7) (h21 t ν) =
      ((4 : K) * unitPow t (-1 / 2)) •
        diagRescale ((7 : K) / 10) ((4 : K) / 7) (h10 t ν) := by
  have hM : rescaleMat (1 : K) ((10 : K) / 7) (eps21M ν) =
      rescaleMat ((7 : K) / 10) ((4 : K) / 7) (eps10M ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps21M, eps10M] <;> ring
  simp only [h21, h10, diagRescale_weightGenFun, hM]

/-- **[Jacobs, Lemma 2.11], second chain**:
`16 κ(1/4) h₂,₀(x, 4y/7) = (1/4) κ(−2) h₁,₂(7x/10, y)`.

Again the scale factor is `-8`, this time on the left-hand matrices, and
`(1/4) · (-8) = -2` matches the `κ`-arguments. -/
theorem lemma211_second :
    ((16 : K) * unitPow t (1 / 4)) • diagRescale 1 ((4 : K) / 7) (h20 t ν) =
      ((4 : K)⁻¹ * unitPow t (-2)) • diagRescale ((7 : K) / 10) 1 (h12 t ν) := by
  have hsq : ‖(3 : K)‖ ^ 2 ≤ ‖(3 : K)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 2)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hquarter : ‖(1 / 4 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show ((1 / 4 : K) - 1) = -(3 / 4) by norm_num, norm_neg, norm_div, hn4, div_one]
  have e11a : eps12M1 ν 1 1 = -3 / 4 * ν - 1 / 2 := by simp [eps12M1]
  have e11b : eps12M2 ν 1 1 = 1 / 4 * ν := by simp [eps12M2]
  have hd1 : ‖rescaleMat ((7 : K) / 10) 1 (eps12M1 ν) 1 1 - 1‖ ≤ ‖(3 : K)‖ := by
    rw [rescaleMat_apply_one_one, e11a,
      show (-3 / 4 * ν - 1 / 2 - 1 : K) = -(3 * (ν + 2) / 4) by ring, norm_neg, norm_div, hn4,
      div_one, norm_mul]
    calc ‖(3 : K)‖ * ‖ν + 2‖ ≤ ‖(3 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((norm_nu_add_two h3 hνc).trans h3.le) (norm_nonneg _)
      _ = ‖(3 : K)‖ := mul_one _
  have hd2 : ‖rescaleMat ((7 : K) / 10) 1 (eps12M2 ν) 1 1 - 1‖ ≤ ‖(3 : K)‖ := by
    rw [rescaleMat_apply_one_one, e11b, show (1 / 4 * ν - 1 : K) = (ν - 4) / 4 by ring, norm_div,
      hn4, div_one]
    exact (norm_nu_sub_four h3 hνc).trans hsq
  have hA : rescaleMat (1 : K) ((4 : K) / 7) (eps20M1 ν) =
      (-8 : K) • rescaleMat ((7 : K) / 10) 1 (eps12M1 ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps20M1, eps12M1] <;> ring
  have hB : rescaleMat (1 : K) ((4 : K) / 7) (eps20M2 ν) =
      (-8 : K) • rescaleMat ((7 : K) / 10) 1 (eps12M2 ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps20M2, eps12M2] <;> ring
  have hscal : (16 : K) * unitPow t (1 / 4) * (unitPow t (-8) * (-8 : K)⁻¹ * (-8 : K)⁻¹) =
      (4 : K)⁻¹ * unitPow t (-2) := by
    have hmul : unitPow t ((1 / 4 : K) * (-8)) = unitPow t (1 / 4) * unitPow t (-8) :=
      unitPow_mul h3 ht.le hquarter (norm_neg_eight_sub_one h3)
    rw [show ((1 / 4 : K) * (-8)) = -2 by norm_num] at hmul
    rw [hmul]
    field_simp
    ring
  simp only [h20, h12, diagRescale_add, diagRescale_weightGenFun, hA, hB,
    weightGenFun_smul h3 ht.le neg_eight_ne_zero (norm_neg_eight_sub_one h3) hd1,
    weightGenFun_smul h3 ht.le neg_eight_ne_zero (norm_neg_eight_sub_one h3) hd2, smul_add,
    smul_smul, hscal]

omit [IsUltrametricDist K] [CompleteSpace K] in
omit h3 ht hνc in
/-- **[Jacobs, Lemma 2.11], second chain, second equality**:
`(1/4) κ(−2) h₁,₂(7x/10, y) = (1/4) κ(−2) h₀,₁(7x/4, 10y/7)`.

As for the first chain's second equality, the two rescaled matrices agree on the nose. -/
theorem lemma211_second' :
    ((4 : K)⁻¹ * unitPow t (-2)) • diagRescale ((7 : K) / 10) 1 (h12 t ν) =
      ((4 : K)⁻¹ * unitPow t (-2)) •
        diagRescale ((7 : K) / 4) ((10 : K) / 7) (h01 t ν) := by
  have hM1 : rescaleMat ((7 : K) / 10) 1 (eps12M1 ν) =
      rescaleMat ((7 : K) / 4) ((10 : K) / 7) (eps01M1 ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps12M1, eps01M1] <;> ring
  have hM2 : rescaleMat ((7 : K) / 10) 1 (eps12M2 ν) =
      rescaleMat ((7 : K) / 4) ((10 : K) / 7) (eps01M2 ν) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rescaleMat, eps12M2, eps01M2] <;> ring
  simp only [h12, h01, diagRescale_add, diagRescale_weightGenFun, hM1, hM2]

end Lemma211

section M22

variable (t ν ω : K)

/-- The generating function of the eigenblock `M₂,₂` [Jacobs, p. 34, eq. (2.1.14)]:
`H₂,₂(x, y) = (1/16) ω² κ(4) h₀,₂(7x/4, y) + (1/4) ω κ(−2) h₁,₂(7x/10, y)`. -/
noncomputable def M22genFun : MvPowerSeries (Fin 2) K :=
  ((16 : K)⁻¹ * ω ^ 2 * unitPow t 4) • diagRescale ((7 : K) / 4) 1 (h02 t ν) +
    ((4 : K)⁻¹ * ω * unitPow t (-2)) • diagRescale ((7 : K) / 10) 1 (h12 t ν)

variable {t ν : K}

set_option linter.unusedSectionVars false in
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Neither a scalar of norm `≤ 1` nor a rescaling `x ↦ αx` by a unit `α` moves the row-decay
bound `‖x^m y^r`-coefficient`‖ ≤ ‖3‖ ^ m`. -/
lemma norm_coeff_smul_diagRescale_le {c α : K} {F : MvPowerSeries (Fin 2) K}
    (hc : ‖c‖ ≤ 1) (hα : ‖α‖ = 1) {m r : ℕ} (hF : ‖coeff (idx m r) F‖ ≤ ‖(3 : K)‖ ^ m) :
    ‖coeff (idx m r) (c • diagRescale α 1 F)‖ ≤ ‖(3 : K)‖ ^ m := by
  rw [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one, one_pow, mul_one,
    norm_mul, norm_mul, norm_pow, hα, one_pow, one_mul]
  calc ‖c‖ * ‖coeff (idx m r) F‖ ≤ 1 * ‖(3 : K)‖ ^ m :=
        mul_le_mul hc hF (norm_nonneg _) zero_le_one
    _ = ‖(3 : K)‖ ^ m := one_mul _

/-- Row decay of `H₂,₂`: `‖x^m y^r`-coefficient`‖ ≤ ‖3‖ ^ m` (from `norm_coeff_h02_le`,
`norm_coeff_h12_le`; the scalars and the unit rescales `7/4`, `7/10` do not move norms). -/
theorem norm_coeff_M22genFun_le (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (m r : ℕ) :
    ‖coeff (idx m r) (M22genFun t ν ω)‖ ≤ ‖(3 : K)‖ ^ m := by
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have hn10 : ‖(10 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 10) (by norm_num) (by norm_num)
  have hn16 : ‖(16 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 16) (by norm_num) (by norm_num)
  have hnω : ‖ω‖ = 1 := norm_omega hω
  have hu4 : ‖unitPow t (4 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3 ht (le_of_eq (by rw [show (4 : K) - 1 = 3 by norm_num]))
  have hu2 : ‖unitPow t (-2 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3 ht (le_of_eq (by rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg]))
  have hc1 : ‖(16 : K)⁻¹ * ω ^ 2 * unitPow t 4‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_inv, hn16, inv_one, one_mul, norm_pow, hnω, one_pow, one_mul]
    exact hu4
  have hc2 : ‖(4 : K)⁻¹ * ω * unitPow t (-2)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_inv, hn4, inv_one, one_mul, hnω, one_mul]
    exact hu2
  have hα1 : ‖(7 : K) / 4‖ = 1 := by rw [norm_div, hn7, hn4, div_one]
  have hα2 : ‖(7 : K) / 10‖ = 1 := by rw [norm_div, hn7, hn10, div_one]
  simp only [M22genFun, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact norm_coeff_smul_diagRescale_le hc1 hα1 (norm_coeff_h02_le h3 ht hνc m r)
  · exact norm_coeff_smul_diagRescale_le hc2 hα2 (norm_coeff_h12_le h3 ht hνc m r)

/-- The operator `M₂,₂ : c(ℕ, K) →L[K] c(ℕ, K)`, *defined* by its generating function
`M22genFun`.  Per [Jacobs, pp. 32–34] this is the block of `U₃` acting on the
`ω²`-eigenspace of `W` in the topological basis `𝔅₂`.  What is proved: `M22op` is the
middle factor of `det(1 − T·U₃)` — see `JacobsSlash.charPowerSeries_U3MatrixOp`
(`PhD.JacobsSlash.DiamondW`) for the factorisation and `JacobsSlash.U3.heckeU3_apply_classRep`
(`PhD.JacobsSlash.U3.Matrix`) for the identification of `U₃`.  The *eigenspace* reading is
not formalised (it needs [Jacobs, Lemma 2.9]; see `PhD.JacobsSlash.DiamondW`'s header). -/
noncomputable def M22op (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (M22genFun t ν ω)
    (⟨1, fun j i => le_trans (by simpa using norm_coeff_M22genFun_le ω hω h3 ht hνc j i)
      (pow_le_one₀ (norm_nonneg _) h3.le)⟩)
    (fun i => by
      exact (hyps_of_row_decay
        (M := fun j i => MvPowerSeries.coeff (idx j i) (M22genFun t ν ω))
        (q := (3 : K)) (c := (1 : K)) h3 (fun j i' => by
          rw [norm_one, one_mul]
          exact norm_coeff_M22genFun_le ω hω h3 ht hνc j i')).2 i)

/-- The matrix of `M22op` reads off `H₂,₂`. -/
theorem matrixCoeff_M22op (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (j i : ℕ) :
    matrixCoeff (M22op ω hω h3 ht hνc) j i = coeff (idx j i) (M22genFun t ν ω) :=
  matrixCoeff_ofGenFun _ _ _ j i

/-- `M₂,₂` is compactoid ([Jacobs, Lemma 2.7] for the block). -/
theorem isCompactoid_M22op (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : IsCompactoid (M22op ω hω h3 ht hνc) := by
  refine isCompactoid_of_row_decay (q := (3 : K)) (c := (1 : K)) h3 fun j i => ?_
  rw [matrixCoeff_M22op ω hω h3 ht hνc, norm_one, one_mul]
  exact norm_coeff_M22genFun_le ω hω h3 ht hνc j i

end M22

end JacobsSlash
