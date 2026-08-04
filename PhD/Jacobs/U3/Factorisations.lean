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
recomputed rather than copied — see `PhD/QMF/Sigma0.lean`'s header for why the library is
left-handed and why the adjugate is the standard dictionary.
-/

open Quaternion IsDedekindDomain NumberField QMF

namespace Jacobs.U3

/-- The class-index table `σ(i,t)` of the nine factorisations ([Jacobs pp. 26–27]; in
the thesis's right-handed indexing the table is `σ(0,·) = (2,1,1)`, `σ(1,·) = (0,2,2)`,
`σ(2,·) = (1,0,0)` — the left-coset reindexing is fixed with the certificates). -/
def sigmaTable : Fin 3 → Fin 3 → Fin 3 := sorry

/-- The diagonal never occurs: `σ(i,t) ≠ i` — the source of `ε_{i,i} = 0` and hence
`trace U₃ = 0` [Jacobs, p. 28: "noticing that ε_{i,i} = 0 … the trace of U₃ is zero"]. -/
theorem sigmaTable_ne (i t : Fin 3) : sigmaTable i t ≠ i := sorry

/-- The global factor `d(i,t)` of each certificate, as a unit of `D`. -/
noncomputable def dTable : Fin 3 → Fin 3 → Dˣ := sorry

theorem dTable_mem (i t : Fin 3) : unitsIncl ℚ D (dTable i t) ∈ globalUnits ℚ D := sorry

/-- The level factor `u(i,t)` of each certificate. -/
noncomputable def uTable : Fin 3 → Fin 3 → U1_9 := sorry

/-- **The nine certificates** ([Jacobs pp. 26–27, §B.1]): the factorisation identities
`classRep i · etaRep t = d(i,t) · classRep (σ(i,t)) · u(i,t)` in `D_f^×`. -/
theorem factorisation (i t : Fin 3) :
    classRep i * etaRep t
      = unitsIncl ℚ D (dTable i t) * classRep (sigmaTable i t) * (uTable i t : Dfx ℚ D) :=
  sorry

/-- The acting matrices of the factorisations lie in `Σ₁(9)`:
`(etaRep t · u(i,t)⁻¹)₃ ∈ Σ₁(9)` — the elements whose `κ`-action assembles the blocks. -/
theorem toMatrix_etaRep_mul_inv_uTable_mem_sigma1 (i t : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t * ((uTable i t : Dfx ℚ D))⁻¹) ∈ Sigma1 := sorry

/-- **The `ε`-matrix identification** ([Jacobs p. 28 displays, as transcribed — with the
misprint corrected — in `PhD.Jacobs.U3Data`]): the Jacobs-form parameter matrices of the
acting elements are exactly the transcribed `ε`-matrices, e.g. for the two `t` with
`σ(0,t) = 1` they are `Jacobs.eps01M1 ν₃` and `Jacobs.eps01M2 ν₃`.  Stated here as the
generating-function form consumed by `Matrix.lean`: for each `(i, j)` with `j ≠ i`, the
sum of `weightGenFun t` over the acting matrices of `{t' | σ(i,t') = j}` equals the
transcribed block generating function `h_{i,j}` of `PhD.Jacobs.U3Data`. -/
theorem sum_weightGenFun_eq_h (tw : K₃) (i j : Fin 3) (hij : j ≠ i) :
    ∑ t' ∈ {t' | sigmaTable i t' = j},
        Jacobs.weightGenFun tw
          (adjParams (toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹)))
      = ![![0, Jacobs.h01 tw ν₃, Jacobs.h02 tw ν₃],
          ![Jacobs.h10 tw ν₃, 0, Jacobs.h12 tw ν₃],
          ![Jacobs.h20 tw ν₃, Jacobs.h21 tw ν₃, 0]] i j := sorry

end Jacobs.U3
