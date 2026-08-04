# Decomposition — Jacobs, *Slopes of Compact Hecke Operators*, Chapter 2

**BOARD PATH: `.mathlib-quality/jacobs/`** — this project's tickets/plan/decomposition live
HERE.  The default `.mathlib-quality/` path is the parallel NewtonPolygon board; the QMF
board is `.mathlib-quality/qmf/`.  Never touch either from Jacobs work; every `/beastmode`
invocation for Jacobs must be told this path explicitly.

## Skeleton location (all `lake build PhD.Jacobs.Slopes` clean, 59 sorries, 0 errors — verified 2026-08-03)
- `PhD/Jacobs/PadicAnalytic.lean` (178 lines) — p-adic exp/log/binomial (API gap, own tree)
- `PhD/Jacobs/GenFun.lean` (152) — matrices ↔ generating functions ↔ operators on `c(ℕ,K)`
- `PhD/Jacobs/SlopeTheorem.lean` (96) — [Jac, Thm 2.12] abstract slope theorem
- `PhD/Jacobs/U3Data.lean` (263) — the ε-matrices, the six `h_{i,j}`, Lemma 2.7/2.11, `M₂,₂`
- `PhD/Jacobs/Slopes.lean` (150) — Lemma 2.13, Thm 2.14, Cor 2.15/2.16 (milestone)

## Sources
- [Jac] Daniel Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College
  London, January 2003.  (Full PDF supplied by the user this session; page refs to the PDF.)
- [Ser62] Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  IHÉS 12 (1962) — [Jac §1.2]'s source; formalised as `PhD/TateFredholm/` (sorry-free).
- [Kob84] Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58 —
  [Jac §1.3]'s source; supplies the standard p-adic exp/log convergence facts (Ch. IV)
  behind the terse analytic steps of [Jac pp. 29, 38–39] (fallback-chain cross-reference).
- Infrastructure: `PhD/TateFredholm/*` (Banach–Tate compact operators, `charCoeff`,
  `charPowerSeries`, trace property), `PhD/QMF/*` (adelic tranche only, see AG-B).

## Setting (generality decision, applies to every leaf)
[Jac] works over `ℂ₃` with `ν₃ = √−2 ∈ ℤ₃` (`≡ 508 mod 3⁷`, p. 22) and
`ω = (−1+√−3)/2 ∈ ℂ₃` (p. 32).  We work over an abstract
`[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` with
parameters `(t ν ω : K)` and hypotheses `‖3‖ < 1`, `‖t‖ < 1` (= `v₃(t) > 0`, the weight
disc, [Jac p. 22 item 2]), `ν² = −2`, `‖ν − 2695‖ ≤ ‖3‖¹⁰` (the substitution [Jac p. 39];
`2695 ≡ 508 mod 3⁷` so this pins the same root), `ω² + ω + 1 = 0`.  `‖2ω+1‖² = ‖3‖` is
DERIVED (`(2ω+1)² = −3`), not assumed.  "mod `𝔪₃`" statements are phrased as norm
inequalities `‖·‖ < 1`; half-integer valuations as squared norms (`‖·‖² = ‖3‖^k`), so no
`rpow` and no residue rings anywhere.  Everything instantiates at `K = ℚ₃(ζ₃)`-completions
or `ℂ₃` later (deferred; no leaf needs a concrete field).

## Prior-B2 log consultation
`.mathlib-quality/b2_log.jsonl` read (2 entries, 2026-08-03): both concern
`NewtonPolygon₀.unitSlope_cases` / `lengths_final` representation defects on the parallel
NewtonPolygon board.  No name or shape match with any Jacobs leaf.  Consequence drawn
anyway: the milestone is stated as a `charCoeff`-valuation identity
(`val_charCoeff_M22op`), NOT against `NewtonPolygon₀.unitSlope` — that API was under
active repair today; the polygon-language wrapper is a recorded seam (see AG-NP below).

---

## Adversarial findings on the source data (Step 4.5 outcomes, recorded up front)

1. **[Jac p. 28] misprint in the second `ε₁,₂` matrix.**  p. 28 prints its `a`-entry as
   `−15/14 ν₃ − 5/7`; display (2.1.7) and the PARI listing §B.3 (`5/14*(x3 + 2)*x*y`)
   give `a = −5(ν+2)/14 = −5/14 ν − 5/7`.  Hand-check via the Lemma 2.11 identity
   `16κ(1/4)h₂,₀(x, 4y/7) = (1/4)κ(−2)h₁,₂(7x/10, y)`: matching the second-term
   denominators forces `(−8)·a·(7/10) = −2(ν+2)`, i.e. `a = −5(ν+2)/14`.  The first
   `ε₁,₂` matrix's `a = 15ν/14` is correct (same check on first terms).  Skeleton uses
   the corrected value (`eps12M2`, docstring records the erratum).
2. **[Jac (2.1.6)] display vs. code sign.**  (2.1.6) as printed reads `− 4y` in the
   denominator of `h₁,₀`, while p. 28's `ε₁,₀` matrix (`b = −4`) and §B.3's code
   (`+ 4*y`) give `+4y`.  We transcribe only the p. 28 *matrices* and let all
   denominators be *computed* by `weightGenFun`, eliminating this error class; the
   Lemma 2.11 ticket (J014) machine-checks the cross-relations of the whole data set.
3. **[Jac p. 39] "`ν₃ = 2695 + 3¹⁰S` for `S ∈ ℤ₃ˣ`".**  Since `2695² + 2 = 3¹¹·41`,
   the true root has `ν ≡ 2695 mod 3¹¹`, so `S ≡ 0 mod 3` — the unit claim is a slip.
   Harmless: the proof only uses the congruence `ν ≡ 2695 mod 3¹⁰` (our `hνc`), never
   `S`'s unit-ness.
4a. **[2026-08-04] Skeleton statement defect (fixed).**  `norm_coeff_M22genFun_le`/`M22op`
   family lacked any hypothesis on `ω` — false for `‖ω‖ > 1`.  Caught by the J015
   dispatch-prompt's adversarial instruction; fixed by adding `hω : ω²+ω+1 = 0` and
   moving the Omega lemmas into `U3Data.lean` (see jacobs-local `b2_log.jsonl`).
4. **Plausibility audit of Thm 2.14's shape** (edge-instantiation attack, passed): with
   `ν ≡ 2695`, every `a`-entry of the nine matrices has `v₃ = 1` *exactly*
   (`ν−1, ν+2 ≡ 0 mod 3`, `∤ 9`; `3,15,21,30`), every `c`-entry has `v₃ ≥ 2`
   (`ν ≡ 4 mod 9`), every relevant `d`-entry is a unit.  After the `x ↦ x/(3(2ω+1))`,
   `y ↦ (2ω+1)y` scaling the surviving-mod-`𝔪₃` monomials are exactly the powers of
   `xy` coming off the `a`-diagonal — matching the claimed residue `−1/(1−xy)`, a
   function of `xy` alone.  (This is evidence, not proof; J018 is the proof.)

---

## Tranche A (this board's tickets): the slope computation for `M₂,₂`

The thesis's chain [Jac §2.1 pp. 28–39] from the displayed generating functions to
Corollary 2.16.  **EXPLICIT SKIP (user-flagged 2026-08-04): everything up to the
displays (2.1.4)–(2.1.9) is assumed** — Thm 2.1 (class set), Lemma 2.2 (Γᵢ = 1),
Lemma 2.3 (Uη₃U cosets), Lemmas 2.4/2.5 + §B.1 (factorisations), and Prop 2.6's
derivation of the generating-function formula.  The `eps*M*` matrices are
transcriptions; `weightGenFun` is Prop 2.6's formula taken as a definition.  Tranche A's
results are therefore unconditional about the defined operators and become statements
about `U₃ = [U η₃ U]` only when AG-B (+ AG-W for the eigenblock reading) is discharged —
that is the "go back and prove the definitions are what we want" work, and it is the
acceptance criterion for any final U₃-slopes claim.  This is exactly the split the
thesis itself makes: from (2.1.4) on, every argument is about the matrices.  The
docstring of `PhD/Jacobs/U3Data.lean` carries the same notice.

### Result R1 (API gap, own tree): p-adic exp/log/binomial — `PadicAnalytic.lean`

Not in mathlib (checked: no `padicExp`/p-adic exponential anywhere in
`Mathlib.NumberTheory.Padics.*` or `Mathlib.Analysis.*` at this revision).  [Jac] uses
these facts tersely; per the source-gap fallback chain the proofs are taken from the
thesis's own reference [Kob84, Ch. IV §§1–2].

Source claim (verbatim, [Jac p. 29]):
> "Then κ(cx + d) = κ(4^ρ) = κ(4)^ρ = 4^{tρ} = (4^ρ)^t = (cx + d)^t. Lastly, we write
> (cx + d)^t = exp₃(t log(cx + d)). A simple calculation shows that t log(cx + d) is in
> the radius of convergence of exp₃ so that exp₃(t log(cx + d)) converges to an element
> of 𝒪₃[[x]]."

and (verbatim, [Jac p. 29]):
> "4^ρ = ∑_{h=0}^∞ 3^h (ρ choose h) … where by (ρ choose h) we mean 1/h! ∏_{k=0}^{h−1} (ρ − k)."

Lean ↔ source: `unitPow t u := padicExp (t * padicLog u)` is literally the first quote;
`binomialCoeff`/`binomialSeries` the second.  The convergence-disc facts are [Kob84,
Ch. IV]: log converges on `‖u−1‖ < 1`, exp on `v > 1/(p−1) = 1/2` (our squared-norm
form `‖w‖² < ‖3‖`), `v₃(n!) = (n − s₃(n))/2 ≤ (n−1)/2` (Legendre).

Leaves (all in `PadicAnalytic.lean`, each `:= by sorry`):
- **L1.1** `norm_natCast_eq_one_of_coprime`, `norm_natCast_eq_pow_padicValNat`,
  `sq_norm_factorial_ge` — residue characteristic 3 forces `‖n‖ = ‖3‖^{v₃(n)}`.
  Discharge: ultrametric `‖n‖ ≤ 1` (mathlib `IsUltrametricDist.norm_natCast_le_one` —
  name to verify at execution, family exists), Bézout for coprimality, mathlib
  `padicValNat`, `Nat.Prime.factorial` Legendre lemmas
  (`sub_one_mul_padicValNat_factorial`-family, verified to exist).
  Attacks: [edge] n = 1 ✓ (both sides 1); n = 3^k ✓; [hyp] CharZero needed else `(n:K)=0`
  ✓ carried; [counterexample search] none — this is the standard residue-char argument.
- **L1.2** `padicLog_one`, `padicExp_zero`, `norm_padicLog_le`,
  `norm_padicExp_sub_one_le` — series bookkeeping: term-norm bounds + mathlib
  ultrametric summability (`summable_of_tendsto_cofinite` is in TateFredholm/Tate.lean if
  mathlib's shape doesn't fit).  Source: [Kob84 Ch. IV §1]; [Jac p. 38] "log₃(−ν₃−1) =
  3 + 9L₀" is the `norm_padicLog_le` instance.  Attacks: [edge] u = 1: log = 0 ✓ bound
  holds; w = 0 ✓; [hyp-strength] `‖u−1‖ ≤ ‖3‖` cannot weaken to `< 1` for the *bound*
  `≤ ‖3‖` (v(u−1) = 1/2 gives v(log) = 1/2 only) ✓ hypothesis is necessary for this
  conclusion.
- **L1.3** `padicExp_add`, `padicExp_padicLog`, `padicLog_mul` — [Kob84 Ch. IV §2]
  (Cauchy product; formal-identity + convergence).  The hardest analytic leaves
  (source proves them in ~2 pages; expect the largest PadicAnalytic ticket).
  Attacks: [edge] a = 0 ✓; [hyp] both summands must be in exp's disc — at
  `v = 1/2` exactly, exp diverges (3-adic: `v(3^{1/2·n}/n!)` does not → ∞) ✓ strict
  hypothesis correct; [drift] statements match [Kob84 IV.2 Prop.] restricted to the
  smaller disc we need ✓.
- **L1.4** `unitPow_one`, `unitPow_mul`, `norm_unitPow_sub_one_le` — assembly of L1.2/L1.3.
  `unitPow_mul` = `padicLog_mul` + `padicExp_add` (in-disc checks: ‖t·log‖ ≤ ‖t‖‖3‖,
  squared < ‖3‖ since ‖t‖,‖3‖ < 1 ✓).  Attacks: [edge] u = 1 ✓; [discharge] 2-lemma
  composition ✓.
- **L1.5** `binomialCoeff_zero`, `sq_norm_binomialCoeff_mul_pow_le` — the tail bound
  `v((t choose n) eⁿ) ≥ v(t) + 1/2` for `n ≥ 1`, `v(e) ≥ 1/2`, from L1.1's factorial
  bound: `v(∏(t−k)) ≥ v(t)` (each `t−k` integral, k ≥ 1 terms have `v ≥ 0`), minus
  `v(n!) ≤ (n−1)/2`, plus `n·v(e) ≥ n/2`.  Attacks: [edge] n = 1: `v(t·e) ≥ v(t)+1/2` ✓;
  [hyp] `n = 0` genuinely fails (coefficient 1) ✓ excluded; [source-drift] this is
  [Jac p. 29]'s `∑ 3^h (ρ choose h)` convergence made quantitative ✓.

### Result R2: matrices ↔ generating functions ↔ operators — `GenFun.lean`

Source claims (verbatim, [Jac §1.1 pp. 7–8]):
> "Multiplication of a given infinite matrix A = (a_{i,j}) by D(α) on the left
> (respectively right) simply has the effect of multiplying each entry in row n
> (respectively column n) by α^n."
> "**1.3 Proposition.** Let A = (a_{i,j}) be an infinite matrix over a ring R with
> generating function H_A(x, y). Let α, β ∈ R − {0}. Then, the generating function of
> D(α) A D(β) is H_A(αx, βy)."

and ([Jac §1.2 p. 10], Serre's Corollary):
> "**1.10 Corollary.** Suppose that the matrix (n_{ji}) of u has all its entries in 𝒪_K.
> If D(1/p)(n_{ji}) has all its entries in 𝒪_K, then u is compact."

Lean ↔ source: `diagRescale α β F` IS `H(αx, βy)` (coefficientwise `α^j β^i`);
`matrixCoeff_diagOp_comp` is Prop 1.3 in operator form; `isCompactoid_of_row_decay` is
Cor 1.10 generalised to geometric decay rate `‖q‖ < 1` (the thesis uses `q = 3`; rows
`j` in `TateFredholm.rowNorm` convention `r_j(u) = sup_i ‖a_{ji}‖`, matching [Ser62]'s
`r_j`).  `ofCoeffs` is the operator-from-bounded-matrix construction of [Ser62 Prop. 3] /
[Jac Prop. 1.7] — `TateFredholm.exists_coeffEquiv` is its norm-preserving ∃-form; we need
the definite description with columns-in-`c₀` (a `def` + spec lemma, new but standard —
built from `cSpace` API + `summable_of_tendsto_cofinite`).

Leaves: **L2.1** `idx` API (Finsupp.single arithmetic — `Finsupp.single_apply`,
`Finsupp.add_apply`); **L2.2** `ofCoeffs` + `matrixCoeff_ofCoeffs` + `hyps_of_row_decay`
(the construction: for `f ∈ c(ℕ,K)`, `j ↦ ∑'_i M j i * f i` is bounded and in `c₀` —
uses `norm_tsum_le_iSup` [TateFredholm], continuity from the uniform bound); **L2.3**
`diagRescale` family (coeff lemmas: `rfl`-adjacent since `MvPowerSeries` is a function
type); **L2.4** `diagOp`, `matrixCoeff_diagOp`, `matrixCoeff_diagOp_comp`,
`isCompactoid_of_row_decay`, `matrixCoeff_ofGenFun`.
Attacks: [convention] the row/column convention was checked against
`TateFredholm.matrixCoeff (u) (j) (i)` and `rowNorm u j = sup_i` — rows = output index =
thesis's first index = our `x`-degree ✓ (this is the #1 silent-death risk of the project;
J005/J006 must re-verify against `Matrix.lean:34` before anything builds on it);
[edge] `M = 0` ✓; α = 0 in diagRescale: thesis excludes α = 0 (`R − {0}`), our
coefficientwise def is total and the lemmas hold ✓ generalisation safe.

### Result R3: the abstract slope theorem — `SlopeTheorem.lean`

Source claim (verbatim, [Jac Theorem 2.12, p. 34]):
> "Suppose that M = (M_{i,j}) is an infinite matrix over 𝒪₃ and is compact. Define
> N = (N_{i,j}) as follows, N_{i,j} := (1/3^i) M_{i,j}. If N_{i,j} ∈ 𝒪₃ for all
> 0 ≤ i, j ∈ ℤ and det(N_{i,j})_{0≤i,j≤n} is a unit for all 0 ≤ n ∈ ℤ, then the slopes
> of M are 0, 1, 2, 3, 4, 5, …."

Source proof structure ([Jac pp. 34–35], read in full): (i) `c_{S_m}` is the top-left
minor, `v₃ = v₃(det D_m(3)) = m(m−1)/2`; (ii) for `S ≠ S_m`, `|S| = m`:
`v₃(M_{S,σ}) = ∑ v₃(M_{σ(i),i}) ≥ ∑_{i∈S} σ(i) = ∑_{i∈S} i ≥ m(m−1)/2 + 1` ("the
smallest possible value for the sum of m non-negative distinct integers"); (iii) `c_m` =
sum of one term of valuation `m(m−1)/2` + strictly bigger ⇒ equality; (iv) the points
lie on the parabola `½x(x−1)` ⇒ vertices ⇒ slopes `0,1,2,…`.  Our conclusion is stated
at stage (iii) (`‖c_m‖ = ‖3‖^{m.choose 2}` and its `val` reading) — stage (iv) is the
polygon-language wrapper, AG-NP.

Leaves mirror (i)–(iii) exactly: **L3.1** `norm_det_le_of_row_bound` (Leibniz +
ultrametric sum bound; mathlib `Matrix.det_apply` + `IsUltrametricDist.norm_sum_le`-family);
**L3.2** `det_row_smul_pow` (row-multilinearity, mathlib `Matrix.det_mul_column` —
re-verified 2026-08-03: `det_mul_column (v) (A) : det (of fun i j => v i * A i j) =
(∏ i, v i) * det A` at `Determinant/Basic.lean:306` scales the FIRST index — that is our
row shape; `det_mul_row` scales the second); **L3.3**
`choose_two_lt_sum_of_ne_range` (pure `Finset ℕ` combinatorics; expect induction/
`Finset.sum_range_id` + exchange argument — small but genuinely fiddly); **L3.4**
`norm_tsum_eq_of_dominant` (split `tsum = f i₀ + ∑ rest`, `norm_tsum_le_iSup`,
ultrametric `norm_add_eq_left`-family); **L3.5** `charCoeff_smul`
(`TateFredholm.charCoeff` unfold + minor `m`-homogeneity via `Matrix.det_smul`);
**L3.6** assembly `norm_charCoeff_of_unit_minors` + `val_charCoeff_of_unit_minors`
(consumes `TateFredholm.charCoeff` = `(−1)^n ∑_S det(minor)` [Fredholm.lean:155] and
`summable_minor`).
Attacks: [gap-analysis] the family `S ≠ S_m` is infinite: dominance needs a UNIFORM gap —
supplied by integrality: valuations are in `ℕ`, so `> m(m−1)/2` means `≥ m(m−1)/2 + 1`,
uniform ✓ (this is why `hdiv` is stated with `ℕ`-power bounds); [edge] m = 0: `c₀ = 1`,
`‖3‖⁰ = 1` ✓; m = 1: `c₁ = −tr`, minor hyp at n = 1 gives `‖M₀₀‖ = ‖3‖⁰`… `‖c₁‖ =` sup
over diagonal? NO — `c₁ = −∑ M_{ii}`, dominant term `M₀₀` norm 1, others ≤ ‖3‖^i ✓ ;
[hyp] `h3 : ‖3‖ < 1` is NECESSARY (at ‖3‖ = 1 all bounds collapse, no dominance) ✓
included; [drift] thesis says "compact" as a hypothesis — implied by `hdiv` (row decay),
so dropped ✓ recorded generalisation.

### Result R4: the data + Lemma 2.7 + Lemma 2.11 — `U3Data.lean`

Source claim (verbatim, [Jac Proposition 2.6, p. 29]):
> "The generating function of the operator ‖_κ (a b; c d) is given by
> κ(cx + d) / ((cx + d)(cx + d − axy − by))."

Source claim (verbatim, [Jac Lemma 2.7, p. 30]):
> "Every non-zero ε_{k,l} is compact. Proof. Note that by definition, h_{k,l}(x, y) ∈
> 𝒪₃[[x, y]]. By Corollary 1.10, it suffices to prove that every entry in D(1/3) ε_{k,l}
> is in 𝒪₃. Equivalently, we need to show that h_{k,l}(x/3, y) lies in 𝒪₃[[x, y]]."

Source claim (verbatim, [Jac Lemma 2.11, p. 33]):
> "The following equalities hold: (1/16)κ(4)h₀,₂(7x/4, y) = 4κ(−1/2)h₂,₁(x, 10y/7) =
> 4κ(−1/2)h₁,₀(7x/10, 4y/7) and 16κ(1/4)h₂,₀(x, 4y/7) = (1/4)κ(−2)h₁,₂(7x/10, x, y) =
> (1/4)κ(−2)h₀,₁(7x/4, 10y/7)."

Lean ↔ source: `weightGenFun t γ = kappaSeries₂ · (linSeries γ)⁻¹ · (quadSeries γ)⁻¹` is
Prop 2.6's display taken as *definition* (the thesis's own working object from p. 30 on;
the derivation from the `‖_κ`-action is AG-B glue).  `kappaSeries₂ t c d` =
`κ(d)·∑ (t choose n)(c/d)ⁿ xⁿ`, which equals the thesis's `κ(cx+d)` by
`κ(cx+d) = κ(d)κ(1+(c/d)x)` — the normalisation is legitimate because every `d`-entry in
play is a 1-unit (verified entry-by-entry, finding 4 above).  The six `h`'s sum
`weightGenFun` over the p. 28 matrices (finding 1/2: matrices are ground truth,
denominators computed).  Lemma 2.11 is stated as four `diagRescale`-equalities of series.

Leaves: **L4.1** `coeff_kappaSeries₂` (rfl-adjacent); **L4.2** integrality
`norm_coeff_h02_le`, `norm_coeff_h12_le` ([Jac Lemma 2.7]'s "simply a case of checking",
made honest: expand the product of `kappaSeries₂`, two geometric inverses; every
`x`-degree carries `v ≥ 1` — `a`-entries `v = 1`, `c`-entries `v ≥ 2`, κ-tails
`v ≥ n/2·2` — bookkeeping over `MvPowerSeries.coeff_mul` convolutions; source spends
4 lines, expect a chunky Lean proof, the first genuinely computational ticket);
**L4.3** Lemma 2.11 (four statements; per-term: scalar `unitPow_mul` bookkeeping
[products of κ-arguments agree: `4·(−(ν+1)/4) = (−1/2)(2ν+2) = −(ν+1)` etc.] + linear
algebra of the rescaled denominators [hand-verified in finding 1] + `MvPowerSeries`
`field_simp/ring`-style manipulation); **L4.4** `M22genFun` bounds + `M22op` glue
(`norm_coeff_M22genFun_le` from L4.2 + `‖ω‖ = 1`, κ-scalars ≤ 1; the column-decay sorry
inside `M22op`; `matrixCoeff_M22op` via `matrixCoeff_ofCoeffs`; `isCompactoid_M22op`
via `isCompactoid_of_row_decay`).
Attacks: [data-integrity] the whole file's data was cross-checked against §B.3's PARI
code and the 2.11 identities (findings 1–3); J014 re-checks it machine-side — if J014
fails, suspect data entry FIRST; [edge] `quadSeries` at y-degree ≥ its support ✓ series
are total; [hyp] `d ≠ 0` needed for the inverses to be genuine — all `d`'s are 1-units
under `hνc` ✓ carried through norm hypotheses; [drift] (2.1.6) sign issue resolved by
computing denominators (finding 2).

### Result R5: Lemma 2.13, Theorem 2.14, Corollary 2.16 — `Slopes.lean`

Source claim (verbatim, [Jac Theorem 2.14, p. 36]):
> "H′₂,₂(x/3, y) ≡ −1/(1 − xy) mod 𝔪₃."

Source claim (verbatim, [Jac Corollary 2.15/2.16, pp. 36, 39]):
> "N ≡ −D(1) mod 𝔪₃."  …  "The n-th slope of M₂,₂ is n − 1/2 for n ∈ ℕ."

Source proof structure ([Jac pp. 36–39], read in full):
1. p. 36: `M′₂,₂ = (1/(ω(2ω+1))) D(1/(2ω+1)) M₂,₂ D(2ω+1)`; same characteristic power
   series via Prop 1.14 with `u = D(1/(2ω+1))M₂,₂` (compact — "compactness of u now
   follows from the proof of Lemma 2.7, since u is the sum of two compact operators"),
   `v = D(2ω+1)`; the scalar multiplies each slope by adding `v₃(ω(2ω+1)) = 1/2`.
2. pp. 37–38: the numerator/denominator of `H′₂,₂(x/3, y)` displayed explicitly (the
   "monster" polynomials — three κ-multiplied polynomial cofactors summed, over one
   polynomial denominator).
3. pp. 38–39: the three κ-values evaluated: each is `1 + (2ω+1)t·Lᵢ`, `Lᵢ ∈ 𝒪₃[[x]]`
   ("For the case, −ν₃−1 … log₃(−ν₃−1) = 3 + 9L₀ … exp₃(t(3+9L₀)) converges to an
   element 1 + (2ω+1)tL₁"; the two `x`-dependent cases have "v₃(c) = 1/2 and
   v₃(d−1) = 1 … gives an element of 1 + (2ω+1)t𝒪₃[[x]]").
4. p. 39: substitute `ν = 2695 + 3¹⁰S`; numerator `= 3⁶(−(2ω+1)(x²y²+xy+1) +
   t(2ω+1)(L₁+L₂+L₃-terms)) + 3⁷L₄`, denominator `= 3⁶(−(2ω+1)x³y³ + 2ω+1) + 3⁷L₅`;
   divide by `3⁶(2ω+1)`, reduce mod `𝔪₃` (recall `t, 2ω+1 ∈ 𝔪₃`):
   `−(x²y²+xy+1)/(1−x³y³) = −1/(1−xy)`.

Leaves:
- **L5.1** `sq_two_omega_add_one`, `sq_norm_two_omega_add_one`, `norm_omega` —
  `(2ω+1)² = −3` by `ring_nf` from `hω`; norms via `‖·²‖ = ‖·‖²`, `‖ω‖³ = ‖ω³‖ = 1`.
  Attacks: [edge] both roots of `ω²+ω+1` behave identically ✓ statement root-symmetric;
  [counterexample] none (`char K = 0` excludes `ω = 1`).
- **L5.2 (THE CRUX)** `norm_coeff_NgenFun_sub_negGeom_lt` — Theorem 2.14.
  Sub-decomposition mirrors the source's steps 3–4:
  - (i) κ-estimates: instances of `norm_unitPow_sub_one_le` (constant parts; the
    `d`-values `−(ν+1)/4, −(3ν+2)/4, ν/4, 4, −2` all have `‖d−1‖ ≤ ‖3‖` under `hνc`)
    and `sq_norm_binomialCoeff_mul_pow_le` (`x`-tails; the scaled ratios `c/d` have
    `v ≥ 2 − 3/2 = 1/2` after the `x`-rescale).  ≡ source step 3.
  - (ii) the collection identity ≡ source step 4's display.  Tactical realisation
    (recorded deviation-in-tactics, not in mathematics): do NOT expand to the pp. 37–38
    monster; work with the 3-term sum `H′ = ∑ cₖ·κ-part·(lin)⁻¹(quad)⁻¹` over the
    common denominator `∏(lin·quad)` — the thesis's monster IS this sum expanded, so the
    displayed polynomials serve as the verification anchor.  Two execution routes,
    worker's choice: (a) certificate style — exhibit the `3⁶(2ω+1)`-decomposition with
    explicit junk polynomials and close coefficient bounds by `norm_num`-arithmetic on
    `ℤ[ν,ω]`-coefficients (`ν ↦ 2695 + 3¹⁰S`, `ω²↦−ω−1`); (b) coefficientwise — prove
    the bound for each `(j,i)`-coefficient class directly from the entry-valuation table
    (finding 4): survivors mod `𝔪₃` are exactly the `a`-diagonal `(xy)^m` chains.
  - (iii) the residue endgame: `(1−xy)(1+xy+x²y²) = 1−x³y³` (`ring`) transported
    through the norm-inequality phrasing.
  This is the project's largest ticket (source: ~3 pages of displays); ticket J018 is
  marked for a `/develop --decompose` refinement pass into named private sub-lemmas
  before work starts if the worker wants finer rails.
- **L5.3** `norm_coeff_NgenFun_le` (Lemma 2.13) — one-line corollary of L5.2:
  `‖N-coeff‖ ≤ max(‖target-coeff‖, ‖diff‖) ≤ 1` (target coefficients are `0/±1`).
  Mirrors the thesis: "The result will follow from our proof of Theorem 2.14."
- **L5.4** `norm_det_NgenFun_minor` (Cor 2.15 consumed form) — `det` of a matrix
  `≡ −1 mod 𝔪₃` entrywise: `‖det A − det(−1)‖ < 1` by multilinearity/Leibniz over the
  entrywise bounds, `‖det(−1)‖ = 1`, ultrametric.  Attacks: [edge] n = 0: `det = 1` ✓.
- **L5.5** `M22half`, `charCoeff_conj_eq` — the trace-property step ≡ source step 1.
  Discharge: `TateFredholm.charPowerSeries_comm` (verified present, Fredholm.lean:756)
  with `u = M22half` (compactoid: rows gain `‖3‖^j`, `D(1/(2ω+1))` spends
  `‖3‖^{j/2}` — needs the *squared-norm* variant of L4.2's bound), `v = diagOp
  ((2ω+1)^·)` (`‖2ω+1‖ ≤ 1` ✓); operator identities `v∘u = M22op`,
  `u∘v = conjugate` by `matrixCoeff` ext (L2.4).
- **L5.6** `charCoeff_M22op_eq` — L5.5 + `charCoeff_smul` (L3.5) for the scalar
  `(ω(2ω+1))⁻¹`.
- **L5.7 (MILESTONE)** `sq_norm_charCoeff_M22op`, `val_charCoeff_M22op` —
  Thm 2.12 (L3.6) applied to the `N`-operator (hypotheses: L5.3 divisibility re-based at
  rows, L5.4 minors), then L5.6:
  `‖cₘ(M₂,₂)‖² = ‖ω(2ω+1)‖^{2m}·‖cₘ(M′)‖² = ‖3‖^m · ‖3‖^{2·choose 2 m} = ‖3‖^{m²}` ✓
  (`m + m(m−1) = m²`).  Attacks: [arith] `2·C(m,2)+m = m²` ✓; [edge] m = 0: `c₀ = 1`,
  `‖1‖² = ‖3‖⁰` ✓; [drift] thesis Cor 2.16 says "n-th slope is n − 1/2" — vertex heights
  `∑_{k<m}(k+1/2) = m²/2` ✓ statements agree.

---

## API gaps / follow-on tranches (recorded, NO tickets on this board yet)

- **AG-NP — the slope reading (Newton-polygon step).**  USER-FLAGGED EXPLICIT
  (2026-08-04): the valuation identities of Thm 2.12 / Cor 2.16 (`v₃(cₘ) = m(m−1)/2`,
  resp. `m²/2`) give the *points* of the Newton polygon, **not the slopes** — it
  remains to show that the Newton polygon defined by these valuation sequences (lower
  convex hull) has the wanted slope sequences (`0,1,2,…` resp. `1/2,3/2,5/2,…`; the
  standard argument: points on a strictly convex parabola are all vertices, slopes =
  successive differences).  Agreed separate and workable independently later.  Carrier:
  `ForMathlib.NumberTheory.NewtonPolygon` (`newtonPolygon₀OfPowerSeries`, heights,
  slopes) — API owned by and recently repaired on the parallel NewtonPolygon board (see
  B2 log; their project completed 2026-08-04, so the seam should now be stable —
  coordinate before writing).  The milestone's `val`-form is the agreed input
  (`PseudoUniformizer.val` is "the shape NewtonPolygon consumes" per TateFredholm's
  docs).  Notices placed above the relevant lemmas in `SlopeTheorem.lean` (done) and
  queued for `Slopes.lean`'s Cor 2.16 pair (after worker J lands).
- **AG-W — the `W` operator and the eigenspace splitting** ([Jac pp. 31–34]: Lemma 2.9,
  the δ-matrices, `W³ = 1`, bases `b_r^{(τ)}`, `B`, Lemma 2.10 `B⁻¹AB` block-diagonal).
  Needs: the 3-block model `c(ℕ × Fin 3, K)`, the block-diagonal
  `charPowerSeries`-product lemma ([Jac Lemma 1.15] = [Ser62 Lemme 2]; TateFredholm has
  `charPowerSeries_extendZero` but not the two-block product — a genuine small
  TateFredholm-side gap), and the scalar κ-checks (`κ(−1/2)²κ(4) = 1` via `unitPow_mul`).
  Workable NOW (no adelic deps) but sequenced after Tranche A: its consumer is the
  statement "`M₂,₂` is the `ω²-eigenblock of U₃`", which only matters once `U₃` exists
  (AG-B).  All six `h`'s and Lemma 2.11 are already in the skeleton for it.
- **AG-EXT — §2.2 extensions** ([Jac pp. 39–40]): the discs `κ(4) = 4^{t+λ}`,
  `λ ∈ {1,2}` ("All that differs … is the evaluation of `(cx+d)^{t+λ}` which we regard
  as `(cx+d)^λ exp₃(t log₃(cx+d))`") and the block `M₃,₃` ("A similar analysis … will
  prove that the n-th slope of M₃,₃ is also n − 1/2").  Design note: parametrise
  `kappaSeries₂` by an extra `λ : ℕ` polynomial factor; the J018 machinery should be
  written with reuse in mind.
- **AG-B — the adelic tranche** ([Jac pp. 13–28]: §§1.4–1.6, Thm 2.1, Lemmas 2.2–2.5,
  the `ε`-derivation and Prop 2.6's action form).  Carrier: `PhD/QMF/` (built this week,
  sorry-free: `QMF.Space`, `heckeOperator`, `bijective_space_evalAtReps`).  Sub-tree:
  - AG-B.1 concrete `D = (−1,−1)_ℚ` (`QuaternionAlgebra ℚ (-1) (-1)`), the maximal order
    `ℤ[i,j,(1+i+j+k)/2]`, the `θ_q` rigidifications ([Jac p. 14]; Hensel `ν_q, ξ_q`) —
    instantiates `QMF.RigidificationAt`.
  - AG-B.2 **class number one** ([Jac Lemma 1.22]: `D^×_f = D^× U₀(1)`).  The thesis
    proves this by Jacquet–Langlands ("The shortest way is to use the Jacquet-Langlands
    correspondence") — NOT formalisable at sane cost.  Fallback-chain cross-reference:
    the classical route (Hurwitz 1896; [Vig80, Vignéras, *Arithmétique des Algèbres de
    Quaternions*] — the thesis's own reference for `𝒪_D^×`): the Hurwitz order is
    (norm-)Euclidean ⇒ one-sided ideal class number 1 ⇒ the adelic statement.  Needs the
    local-global ideal ↔ adelic-coset dictionary — genuine new infrastructure, its own
    /develop pass.
  - AG-B.3 the coset computations (Thm 2.1's three orbits on `(ℤ/9)²`, Lemma 2.2
    `Γᵢ = 1`, Lemma 2.3's local `Uη₃U`-decomposition, Lemmas 2.4/2.5's nine
    factorisations `cᵢv_t⁻¹ = d·c(i,t)·u(i,t)` [§B.1's PARI output, transcribable]) —
    finite/decidable checks over `ℤ/9` and the 24-unit group once AG-B.1 exists.
  - AG-B.4 the identification `matrix of [Uη₃U] on L(U₁(9), A₃) = the ε-blocks`
    (pp. 25–28 + Prop 2.6's action derivation; the `A₃ ≅ c(ℕ, ℂ₃)` seam).
  - **BLOCKED on QMF board work** (per user instruction, note to come back):
    constructing `η₃, μ, cᵢ ∈ D^×_f` with prescribed component at 3 and `1` elsewhere
    needs the `D ⊗ 𝔸 ≅ ∏′ (D ⊗ F_v)` + `mulSingle` API — exactly QMF **T017**'s recorded
    blocker (tensor-restricted-product port chain, part of the T015/T016 closure).
    QMF **T016** (Fujisaki port) is NOT needed here — the class set is computed
    explicitly (AG-B.2/B.3) — but its port drags in the same tensor infrastructure, so
    whichever lands first unblocks AG-B.  **Check the QMF board's T016/T017 status
    before opening the AG-B tranche.**

## Confidence-gate summary
1. Every Tranche-A leaf: mathlib-discharged (cited), project-discharged
   (TateFredholm/PadicAnalytic-internal, cited by file), or inside the explicitly
   sub-decomposed crux J018.  2. Skeleton compiles (0 errors / 59 sorries, 2026-08-03).
3. Verbatim quotes: above, per result.  4. Attacks recorded per leaf; three source
   errata found and resolved (findings 1–3).  5. B2 log consulted — no matches;
   milestone phrased to avoid the flagged API.  6. Tree mirrors [Jac]'s own proof
   chain §2.1; LOC expectations anchored to source page-lengths (J018 ≈ 3 source pages
   → largest ticket; L4.2 ≈ 4 source lines but honest expansion is chunky — flagged).
7. All skeleton conclusions single-conclusion (Lemma 2.11 split into 4 declarations;
   Thm 2.12 norm/val forms separate; Cor 2.16 squared-norm/val forms separate).


---

# AG-NP tranche (opened 2026-08-04): the slope reading

## Skeleton
`PhD/Jacobs/SlopeReading.lean` (13 sorries, `lake build PhD.Jacobs.SlopeReading` green —
verified 2026-08-04).  Imports `PhD.Jacobs.Slopes` + `PhD.NewtonPolygons.SpecConstruction`
(that board completed 2026-08-04; its API is now a stable dependency — coordination note:
if a new NP-side lemma is needed (see N005), prefer stating it in OUR file).

## Sources
- [Jac pp. 34–35], end of proof of Thm 2.12 (verbatim):
  > "and since these all lie on the parabola ½x(x−1) they are on the lower boundary of a
  > convex polygon. Hence these are the vertices of the Newton polygon. The sequence of
  > gradients is 0, 1, 2, 3, 4, 5 . . .. I.e. the slopes are 0, 1, 2, 3, 4, 5 . . .."
  This "hence" IS the tranche: points-with-convex-increments ⇒ polygon ⇒ slopes.
- [Kob84 Ch. IV §3] classical Newton polygon (thesis's own reference).
- `PhD/NewtonPolygons/Spec.lean` (blueprint Definition 1): `IsNewtonPolygonOf v P` =
  start_le + start_mem + height_le + isGreatest; uniqueness `height_eq`; existence
  `isNewtonPolygonOf_newtonPolygon₀OfSeq (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v)` and the
  PowerSeries packaging `isNewtonPolygonOf_powerSeries` (SpecConstruction.lean:757/764 —
  read this session); `isAdmissible_of_affine_bound`; `IsBelow` is INTEGER-sampled
  (`isBelow_iff_height : ∀ x : ℤ, …`).

## Plain-English proof (Step 1)
Let `s : ℕ → ℝ` be monotone and `v m = y₀ + ∑_{i<m} s i`.  Build the explicit polygon
`ofSlopes s`: start `(0, y₀)`, every segment of length 1, slope `s j` on segment `j`
(convex since `s` is monotone).  (i) Its vertices sit at `x = n` (`vertexX = n`: sum of
unit lengths), its unit slopes are the `s j` (`unitSlope_eq_slopes` with the unit-interval
bracketing), and its height at integer `k` is exactly `v k` (`heightFun` = partial sums;
`height = heightFun` on the not-`⊤` region — for this polygon the height is never `⊤`
right of the anchor, by induction along the walk).  (ii) The spec: `start_le` is vacuous
(no naturals left of 0); `start_mem` at `k = 0`; `height_le` holds with EQUALITY by (i);
`isGreatest`: a competitor `Q` anchored at 0 lying under the points satisfies, at every
integer `x ≥ 0`, `Q.height x ≤ pointHeight v x = P.height x`, and at `x < 0` both heights
are `⊥` (`height_eq_bot_iff`) — since `IsBelow` samples only integers, this closes.
(iii) Transport: `v` is admissible (affine bound through `(0, y₀)` with slope `s 0`:
`v k − (y₀ + s 0·k) = ∑_{i<k}(s i − s 0) ≥ 0` by monotonicity), so the constructed
`newtonPolygon₀OfSeq v` satisfies the spec too, and uniqueness (`height_eq`) makes its
heights agree with `ofSlopes s` everywhere.  (iv) Slopes of the constructed polygon: its
unit slope on `[j, j+1]` has `toReal` equal to the height increment `s j`
(`height_eq_heightFun` + `heightFun_succ`), and the junk values are excluded: `⊤` by
`unitSlope_ne_top_of_height_ne_top`; `⊥` because a `⊥` unit slope forces `slopes 0 = ⊥`
(Height.lean:609) — the unbounded-below packaging — contradicting admissibility/
`IsNewtonPolygonOf.bddBelow` (SpecConstruction.lean:69).  Both target cases are instances:
case A `s j = j`, `v m = m(m−1)/2` (= `val_charCoeff_of_unit_minors`); case B
`s j = j + 1/2`, `v m = m²/2` (= `val_charCoeff_M22op`).

## Approach comparison (user requested — decided: Approach 1; APPROVED 2026-08-04)
USER'S RATIONALE (recorded verbatim in spirit): Approach 1 is the more canonical: it
shows that *what we think the Newton polygon is, is the correct one* — the spec-level
`IsNewtonPolygonOf v (ofSlopes s)` certifies the intended polygon against the geometric
definition, independent of any algorithm; whereas the induction approach would only say
the algorithm constructs what we want.  The algorithm statements (N004/N005 transports)
are therefore corollaries, not the primary claim.
- **Approach 1 (planned): explicit witness against the spec.**  No induction anywhere:
  the integer-sampled `IsBelow` makes `isGreatest` collapse to `height_le`-equality; all
  convexity content is already inside the completed Spec/Construction development.  Cost:
  the walk-layer lemmas (N001–N002), one spec assembly (N003), transports (N004–N005).
  Fully general in `s` (monotone), both cases are instances.
- **Approach 2 (user's candidate): slope-by-slope induction.**  First slope by minimality
  (the spec's `unitSlope_zero_mul_le` already gives "points on/above the first-slope
  line"; attainment at `k = 1` pins it), then peel the first segment and recurse on the
  shifted sequence.  Honest costing against this API: needs a tail/peel operation on
  `NewtonPolygon₀` plus spec-transport under peeling — genuinely NEW machinery (est. the
  size of half of Spec.lean), for no gain on closed-form partial-sum sequences.  Where it
  would win: sequences whose values are only known one slope at a time (no closed form),
  or per-slope statements without a global witness.  Not needed here; the first-slope
  half is already available (`unitSlope_zero_mul_le`) should a future tranche want it.

## Leaves (skeleton decl per leaf; file = PhD/Jacobs/SlopeReading.lean)
- **N1** `NewtonPolygon₀.ofSlopes` fields (6 field sorries) + `vertexX_ofSlopes` +
  `unitSlope_ofSlopes` + `heightFun_ofSlopes`.  Discharge: support = ⊤ makes all
  junk/final fields vacuous (`⊤ ≤ (n : WithTop ℕ)` false; `(n:WithTop ℕ)+1 = ⊤` false);
  increasing = coe-mono of `hs`; vertexX = sum of `n` ones (`Finset.sum_const` +
  `WithTop.map`); unitSlope via `unitSlope_eq_slopes` (Height.lean:276) with the
  bracketing `n ≤ j < n+1` at `n := j`; heightFun by `Finset.sum_congr` over
  `unitSlope_ofSlopes` + `NewtonPolygon.toReal`-coe.
  Attacks: [junk-rep/prior-B2] the b2-logged `unitSlope_cases`/`lengths_final` degeneracy
  (support = 1 phantom) cannot occur: support = ⊤, all lengths 1, all slopes real —
  addressed by design ✓; [edge] `s` constant (collinear segments): allowed,
  `slopes_increasing` is non-strict ✓; [hyp] Monotone (not StrictMono) suffices for the
  whole tranche — strictness never used ✓.
- **N2** `height_ofSlopes`.  The one walk-layer lemma with content: `height (k:ℤ) ≠ ⊤`
  along the region (induction via `height_eq_heightFun`/`height_eq_top_mono`
  contrapositive — anchor height is the starting value; each step adds a real slope),
  then `height_eq_heightFun` + N1.  Attacks: [⊤-risk] `height_eq_top_mono` shows ⊤ CAN
  occur for other polygons — here excluded by all-real slopes + ⊤ support; the ticket
  carries the induction route; [left-edge] k = 0: height = starting height ✓ heightFun_zero.
- **N3** `isNewtonPolygonOf_ofSlopes` (assembly): four fields per the prose ((ii));
  `height_eq_bot_iff` (Height.lean:533) for the x < 0 branch of isGreatest;
  `pointHeight_coe` + `algebraMap ℝ ℝ = id` (`Algebra.id.map_eq_id`/`algebraMap_self`).
  Attacks: [too-cheap check] verified `IsBelow` is genuinely integer-sampled
  (Basic.lean isBelow_iff_height) — the collapse is real, and it is the completed
  board's blueprint-backed design, not our shortcut ✓; [competitor-left-of-anchor]
  excluded by the spec's own anchoring hypothesis ✓ (Spec.lean docstring records why).
- **N4** `isAdmissible_of_partial_sums` + `height_newtonPolygon₀OfSeq_ofSlopes`.
  Discharge: `isAdmissible_of_affine_bound (m := s 0) (b := y₀)` with
  `∑_{i<k}(s i − s 0) ≥ 0` (`Finset.sum_nonneg`, `hs (Nat.zero_le _)`); transport =
  `(isNewtonPolygonOf_newtonPolygon₀OfSeq _ ⟨0, …⟩ h2).height_eq (N3) x` (arg order to
  check).  Attacks: [h1] `∃ i, v i ≠ ⊤`: i = 0, coe ≠ ⊤ ✓; [affine-bound shape] the
  bound's hypothesis quantifies over points `v k = a` — ours are all finite ✓.
- **N5** `unitSlope_newtonPolygon₀OfSeq_ofSlopes` — THE RISK LEAF (flagged).
  Route (a): toReal-increment pin (`height_eq_heightFun` twice + `heightFun_succ`) gives
  `toReal (unitSlope j) = s j`; exclude `⊤` via `unitSlope_ne_top_of_height_ne_top`
  (Height.lean:577); exclude `⊥` via Height.lean:609 (`unitSlope = ⊥ ⇒ slopes 0 = ⊥`)
  + the constructed polygon's first slope is real (from admissibility/
  `IsNewtonPolygonOf.bddBelow`, SpecConstruction.lean:69 — an inf of a nonempty
  bddBelow set; a small bridging lemma MAY be needed: "newtonPolygon₀OfSeq of an
  admissible sequence with ≥ 2 finite points has real slopes 0" — if absent, state it
  in OUR file against the spec, not in the NP files).  Route (b) fallback: for `s j ≠ 0`
  the toReal-pin alone excludes junk (toReal ⊥ = toReal ⊤ = 0 ≠ s j); only case A's
  `j = 0` (slope 0) needs route (a)'s ⊥-exclusion — worst case, case A's transport at
  `j = 0` is carried by the first-slope analysis only.  Attacks: [toReal-collapse]
  identified up front (toReal kills ⊥/⊤ to 0 — this is WHY the leaf is nontrivial);
  [structure-nonuniqueness] slopes-as-structure-fields are not unique (collinear splits)
  but unitSlope is height-determined — we transport unitSlope, never `.slopes` ✓.
- **N6** case A pair (`isNewtonPolygonOf_val_charCoeff`,
  `unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries`) — PoC per user.  Discharge:
  N3/N5 at `s = Nat.cast`, `y₀ = 0` + `val_charCoeff_of_unit_minors` (Jacobs, proved) +
  the sum bridge `(∑ i ∈ range m, (i:ℝ)) = (m.choose 2 : ℝ)` (cast of
  `Finset.sum_range_id_mul_two` + `Nat.choose_two_right`, or `Gauss`-sum lemma —
  verify name at pickup) + PowerSeries seam `coeffSeq (ϖ₃ h3).val (charPowerSeries u) m =
  (ϖ₃ h3).val (charCoeff u m)` (`charPowerSeries_coeff` @[simp], TateFredholm).  (Spelling
  updated by the `ϖ₃` refactor — see the API CHANGE banner at the top of `tickets.md`.)
  Attacks: [WithTop-coe] val lands in WithTop ℝ, hv wants a coe of a real — our val
  identity gives exactly `= ((m.choose 2 : ℝ) : WithTop ℝ)`-shaped (check the coercion
  path used in SlopeTheorem's val lemma) ✓; [Γ-instances] Γ = ℝ needs
  `[CommSemiring ℝ] [Algebra ℝ ℝ]` ✓ mathlib instances.
- **N7** case B pair — same shape at `s j = j + 1/2`; sum bridge
  `∑_{i<m} ((i:ℝ) + 1/2) = m²/2` (`Finset.sum_add_distrib` + N6's bridge + `ring`-cast
  arith: m(m−1)/2 + m/2 = m²/2).  Attacks: [statement-hyps] carries hν2/hω/ht/hνc exactly
  as `val_charCoeff_M22op` requires ✓ (skeleton compiled against it).

## Prior-B2 log: consulted (4 entries incl. the NP unitSlope_cases saga + 2 Jacobs
statement fixes).  The NP degeneracy entries are ADDRESSED BY DESIGN in N1 (support = ⊤
rep); no name/shape match otherwise.

## Confidence gate: leaves N1–N7 all discharge from the completed NP API + Jacobs
theorems + mathlib names cited above (verified by reading Spec/SpecConstruction/Height
this session); skeleton compiles (13 sorries); N5 carries the one flagged risk with two
routes and a contained fallback.  Sizing anchors: the thesis spends 3 lines on the
"hence" step — the Lean cost is concentrated in the walk layer (N1–N2, est. ~120 LOC)
and N5 (~60 LOC), consistent with the completed board's Height.lean scale.


---

# AG-W tranche (opened 2026-08-04): the diamond operator and the eigenspace splitting

## Skeleton (`lake build PhD.Jacobs.DiamondW` green, 40 sorries — verified 2026-08-04)
- `PhD/Jacobs/BlockOp.lean` — general (TateFredholm-generality: NormedCommRing +
  ultrametric + complete + NormOneClass, any DecidableEq index) block machinery +
  Serre's partition lemma.  Upstreaming candidates.
- `PhD/Jacobs/DiamondW.lean` — the Jacobs instantiation: remaining Lemma 2.7
  integrality, the six ε-operators, `U3MatrixOp`, `W`, `W³ = 1`, `B`/`B⁻¹`,
  Lemma 2.10, and the milestone product.

## Sources ([Jac §2.1 pp. 31–34, §1.2 p. 11 Lemma 1.15, §2.2 p. 40])
- Lemma 1.15 (verbatim, = [Ser62] Lemme 2 — the mathematical engine):
  > "Let I = I′ ∪ I″ be a partition of I. Assume that u is a compact endomorphism of
  > E = c(I) sending E′ = c(I′) to itself. Let u′ be the restriction of u to E′, and let
  > u″ be the endomorphism of E″ = c(I″) defined by passing to the quotient by u. Then
  > u′ and u″ are compact and det(1 − tu) = det(1 − tu′) det(1 − tu″)."
- Remark 2.8.2 (verbatim): "W³ is the identity map on A₃³."
- p. 33 (verbatim): "and moreover, B is invertible. We find that, 3B⁻¹ = …" [display].
- Lemma 2.10 (verbatim, statement): "B⁻¹AB = [the diagonal display (2.1.14)]" with proof
  note: "The proof of Lemma 2.1.14 relies heavily on a large amount of cancellation in
  calculation of B⁻¹AB; since U₃ and W commute, we can easily verify the following
  equalities [Lemma 2.11] from which all the cancellation is evident."
- §2.2 p. 40 (verbatim): "Let M₃,₃ = (1/16)ωκ(4)D(7/4)ε₀,₂ + (1/4)ω²κ(−2)D(7/10)ε₁,₂."

## Adversarial findings on the source (continued numbering)
6. **[Jac p. 32] δ-label scramble.**  The list names δ₀,₁ twice ("δ0,1 = 4κ(−1/2)D(2/5);
   δ2,0 = 4κ(−1/2)D(10/7); δ0,1 = (1/16)κ(4)D(7/4)"); the explicit matrix display below
   it (authoritative, matches the (Wϕ)(cᵣ) computations) gives δ₀,₁ = 4κ(−1/2)D(2/5),
   δ₁,₂ = 4κ(−1/2)D(10/7), δ₂,₀ = (1/16)κ(4)D(7/4).  We transcribe the matrix display.
   Cross-check: the δ's derive from ‖κ of the §B.2 diagonal factorisations via Prop 2.6
   at c = 0, b = 0: H = κ(d)/(d(d − axy)) = (κ(d)/d)·D(a/d) — e.g. (a,d) = (−1/5,−1/2)
   gives 4κ(−1/2)D(2/5) ✓ (hand-verified this session).
7. **[Jac p. 32] "W has minimal polynomial X² + X + 1".**  Contradicts the nonzero basis
   b_r^{(0)} exhibited for K₀ = ker(W − I) immediately after (min-poly X²+X+1 would force
   K₀ = 0).  Correct: X³ − 1.  Harmless — only W³ = 1 is used, which we prove.

## Plain-English proof (mirrors the source)
(i) [pp. 31–32] The remaining ε's are integral (Lemma 2.7 uniformly — our
`rowInt_weightGenFun` covers all six; only the entry-valuation checks for the six other
matrices are new).  The matrix A of U₃ is the 3×3 block operator with blocks ε_{i,j},
zero diagonal; each block compactoid ⇒ A compactoid.  (ii) [p. 32] W is block-cyclic
with the δ's; W³ = 1 because the scalar product is κ(−1/2)²κ(4) = κ((−1/2)(−1/2)4) =
κ(1) = 1 (via `unitPow_mul`, all arguments 1-units) and D(2/5)D(10/7)D(7/4) = D(1).
(iii) [p. 33] B and B⁻¹ are explicit block matrices of scalars·D(α); B⁻¹B = 1 uses
1 + ω + ω² = 0 and the reciprocal pairs κ(1/4)κ(4) = κ(−1/2)κ(−2) = 1.  (iv) [pp. 33–34]
Lemma 2.10: B⁻¹AB is block-diagonal with blocks M₁,₁, M₂,₂, M₃,₃ — the computation is
`blockOp_comp` bookkeeping whose off-diagonal cancellation is EXACTLY the four proved
Lemma 2.11 identities (the thesis says so verbatim, quote above).  (v) [Lemma 1.15]
det(1 − tA) = det(1 − t·B⁻¹AB) by the trace property (the J020 pattern: u := B⁻¹A
compactoid, v := B; uv = B⁻¹AB, vu = A), and the block-diagonal determinant factors as
the product of the three block determinants — Serre's partition lemma iterated.

## Leaves (skeleton decl per leaf)
- **W1** (BlockOp) `cSpace.inclSubtype/projSubtype` + spec + `restrictOp` + spec +
  `isCompactoid_restrictOp`; `reindexOp` + spec + `isCompactoid_reindexOp`.  Discharge:
  cSpace = C₀ on discrete index — extension-by-zero and restriction are standard C₀
  constructions (`ZeroAtInfty`-API / build like GenFun.ofCoeffs but index-generic;
  TateFredholm's `charPowerSeries_extendZero` (Fredholm.lean:979) already handles
  related extension machinery — READ it first, reuse its constructions if exposed).
  Attacks: [edge] p ≡ False: empty subtype, restrictOp = 0 ✓ statements degenerate
  gracefully; [convention] matrixCoeff on subtypes: the spec lemmas pin it ✓.
- **W2** (BlockOp) `blockOp`/`blockCorner` + specs + `blockCorner_blockOp` +
  `isCompactoid_blockOp` + `blockOp_comp`.  Discharge: assembly via finite sums of
  incl/proj-conjugates (Σ_{a,b} incl_a ∘ T a b ∘ proj_b) or a direct coordinatewise
  construction; `blockOp_comp` from proj∘incl orthogonality (`proj_b ∘ incl_{b'} = δ_{bb'}`).
  Attacks: [rowNorm] compactoid of blockOp: row (a,j) sup = max over b of block-row sups
  → 0 since finitely many b ✓ (Fintype σ needed — carried); [comp] the Σ-formula checked
  by hand on 2×2 ✓.
- **W3** (BlockOp) `charPowerSeries_reindexOp`.  Minors correspond under the Finset-image
  bijection; tsum reindex (`Equiv.tsum_eq`-family + `Finset.map`-image bijection on the
  summation index; `Matrix.det_reindex`-shaped mathlib lemma — verify name).
- **W4** (BlockOp, LARGE — the TateFredholm-side content) `charPowerSeries_partition`.
  Source: Serre's Lemme 2 (quote above); our proof is the matrix-level one: for
  block-triangular matrices every principal minor factors as det(p-part)·det(¬p-part)
  (a triangular block determinant — mathlib `Matrix.det_fromBlocks_zero₂₁`-family,
  verify name/orientation), so c_n(u) = Σ_{S} det(minor S) = Σ_{n₁+n₂=n}
  (Σ_{S₁ ⊆ p-part, |S₁|=n₁} det)(Σ_{S₂}) = coefficient of the product
  (`PowerSeries.coeff_mul` convolution + tsum splitting along the bijection
  S ↦ (S ∩ p, S ∩ ¬p) — `Finset` partition bijection + `Summable.tsum_prod`-style
  rearrangement licensed by `summable_minor`).  Sizing: comparable to Fredholm.lean's
  `charCoeff_eq_det_coeff` block (≈150 LOC).  Attacks: [junk] S mixing blocks: the
  triangular hypothesis kills cross-entries so `det_fromBlocks_zero₂₁` applies to the
  reordered minor — reordering a minor's index set is `Matrix.det_reindex` ✓; [analysis]
  all rearrangements are of norm-summable families (Hadamard bound in `summable_minor`) ✓;
  [Serre-drift] Serre proves compactness of u′/u″ too — ours is W1's
  `isCompactoid_restrictOp` (separate leaf, single-conclusion split ✓).
- **W5** (BlockOp) `charPowerSeries_blockDiag`.  Iterate W4 over σ (Fintype induction /
  `Finset.prod` induction via a two-set split p := (· = a)); reindex `{x // x.1 = a} ≃ I`
  (mathlib `Equiv.prodSubtypeFstEquivProdSubtype`-search or build) + W3 to land on
  `blockCorner`.  Attacks: [σ empty] u on c(∅ × I) — charPS = 1, empty ∏ ✓; [σ = 1] ✓.
- **W6** (DiamondW) remaining integrality ×4 (`rowInt_weightGenFun` + entry checks:
  new units 2ν+2 = 2(ν+1) ✓ norm_nu_add_one, 6ν+4 = 2(3ν+2) ✓ norm_three_mul_nu_add_two,
  −2ν ✓ norm_nu; a-entries: −5(ν−1), 3ν/10-class ✓ table) + the six ε-op holes +
  `isCompactoid_U3MatrixOp` (W2's criterion + `isCompactoid_of_row_decay`).
- **W7** (DiamondW) δ-holes (‖2/5‖ = ‖10/7‖ = ‖7/4‖ = 1 via numeral lemmas) +
  `Wop_cube`: `blockOp_comp` twice; cyclic structure ⇒ diagonal with entries
  δ-products in the three cyclic orders; scalars via `unitPow_mul` (disc checks:
  ‖−1/2 − 1‖ = ‖3‖, ‖4 − 1‖ = ‖3‖ ✓); diagOp products telescope
  ((2/5)(10/7)(7/4) = 1, `field_simp`); assemble blockOp-of-identity = id (needs a
  `blockOp_id`-helper: blockOp (diagonal id) = id — add as private lemma via
  matrixCoeff-ext... NOTE: ext_matrixCoeff is ℕ-specific (Slopes.lean) — W2 should
  provide the generic-index ext or W7 transports; flag for the worker).
- **W8** (DiamondW) B/Binv diagOp-holes + `Binvop_comp_Bop`: blockOp_comp; entries:
  (1/3)Σ_b (3B⁻¹)_{ab}∘B_{bc}: diagonal a = c: (1/3)(1+1+1)·(κ-reciprocal·D(α)D(α⁻¹)) =
  id (κ(1/4)κ(4) = κ(1) = 1, κ(−2)κ(−1/2) = 1 via unitPow_mul; D-telescopes);
  off-diagonal: scalar factor (1 + ω + ω²)·(…) = 0 (from hω).  Attacks: [ω-powers]
  the nine products checked by hand: entry (a,c) carries ω^{(a-1)(c-1)}-pattern sums —
  verified the (1,2) case: (1/16)κ(4)·16ωκ(1/4)·D(7/4)D(4/7) + (1/4)κ(−2)·4ω²κ(−1/2)·
  D(7/10)D(10/7) + 1·1: ω + ω² + 1 = 0 ✓.
- **W9** (DiamondW, LARGE) `lemma210`.  blockOp_comp twice; entry (a,c) of B⁻¹AB =
  (1/3)Σ_{b,b'} Binv_{ab}∘ε_{b,b'}∘B_{b'c}; the proved Lemma 2.11 identities equate the
  six off-diagonal-feeding combinations (D(α)∘ε∘D(β) ↔ diagRescale of h via
  `matrixCoeff_diagOp_comp` + `coeff_diagRescale` — the operator-level restatement of
  the h-identities); collect with ω-arithmetic.  The thesis's own proof note (quote
  above) says 2.11 makes "all the cancellation evident" — expect heavy but mechanical
  bookkeeping (source displays: 1 page).  If an entry refuses: FIRST re-check the B/δ
  transcription against findings 6–7, then the ω-bookkeeping.
- **W10** (DiamondW) M11op/M33op holes (integrality — same bound as
  `norm_coeff_M22genFun_le` with the ω-scalars ≤ 1 resp. absent).
- **W11** (DiamondW, MILESTONE) `charPowerSeries_U3MatrixOp`: trace property
  (`charPowerSeries_comm`, u := Binvop ∘ U3MatrixOp [compactoid: comp_left of W6],
  v := Bop; uv = B⁻¹AB ✓ vu = A needs Bop∘(Binvop∘A) = A i.e. `Bop_comp_Binvop = id`
  TOO — either prove both inverse compositions in W8 (add the second as a lemma there —
  single-conclusion: two separate lemmas) or derive right-inverse from left in the
  block-matrix ring; then `lemma210` rewrites, `charPowerSeries_blockDiag` (W5) +
  `blockCorner_blockOp` (W2) finish.  NOTE W8 must deliver BOTH `Binvop_comp_Bop` and
  `Bop_comp_Binvop` — the second added to the skeleton at ticket time if absent
  (currently only the first is stated — W8's ticket carries the addition as an
  explicitly-authorised skeleton amendment, logged here).

## Prior-B2 log: consulted (7 entries).  The M22half/norm_coeff_M22genFun_le defect
family (defs/statements with ω or hypotheses only in proof-holes) was ADDRESSED AT
SKELETON TIME: every AG-W def carries its hypotheses as explicit `_`-named arguments
(epsOp*, delta*, M11op/M33op, Bop/Binvop) — no junk-guard retrofits should be needed.
No other name/shape matches.

## Confidence-gate note
All leaves discharge from: TateFredholm (charPowerSeries_comm, summable_minor, minor
API), mathlib block-determinant lemmas (`Matrix.det_fromBlocks_zero₂₁`-family,
`Matrix.det_reindex` — names to verify at pickup, flagged in tickets), our proved
Lemma 2.11 + rescale calculus + `rowInt_weightGenFun` + ν-table + `unitPow_mul`, and
the W1/W2 constructions (standard C₀/discrete-index work).  Sizing anchors: source
pp. 31–34 ≈ 3 pages + Lemma 1.15's proof deferred to [Ser62] (our W4 carries it,
≈ `charCoeff_eq_det_coeff`-scale).  Known risk concentrations: W4 (tsum rearrangement)
and W9 (ω-bookkeeping) — both flagged LARGE with fallback notes.
