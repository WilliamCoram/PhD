# Decomposition — class number one for the Hurwitz order (`hClassNumberOne`)

Board: `.mathlib-quality/hurwitz-cn1/` (this is a parallel-boards repo — always name this
board).  Code: **contained subfolder `PhD/JacobsSlash/CN1/`** (user instruction
2026-08-10), flat namespace `JacobsSlash`, digit-prefix file naming.

**Trigger**: user decision 2026-08-10 — Kevin Buzzard wants the Hurwitz material removed
from FLT, so the 2026-08-05 deferral of `hClassNumberOne` to FLT's `completed_units`
(`FLT/Data/HurwitzRatHat.lean:96`, itself a `sorry` — verified 2026-08-10, nothing to
port) is CANCELLED.  The in-repo route recorded as R-CN1
(`.mathlib-quality/qmf/decomposition.md:404-431`, tickets B06/B18) is now developed for
real.  R-CN1 was exempted from the verbatim-quote gate by the deferral; this document
completes that work.

## Skeleton location (Step 2.5 — verified)

All lemmas stated `:= by sorry`; `lake build PhD.JacobsSlash.U3.«9_EigenvaluesU3»
PhD.JacobsSlash.U3.«7_DiamondHecke» PhD.JacobsSlash.CN1.«4_Dictionary»` **passes
(3581 jobs, sorries only, no type errors)** — verified 2026-08-10.

- `PhD/JacobsSlash/CN1/2_Euclidean.lean` (3 sorries)
- `PhD/JacobsSlash/CN1/3_LocalApprox.lean` (5 sorries)
- `PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean` (5 sorries)
- `PhD/JacobsSlash/CN1/4_Dictionary.lean` (7 sorries; houses the final `hClassNumberOne`)
- Surgery already applied at skeleton time: `U3/2_Level.lean` no longer declares the
  theorem (interface note points here; `def HClassNumberOne` stays there);
  `U3/6_Matrix.lean` imports `CN1.«4_Dictionary»` (its `eval_classRep_injective'` at
  line ~293 is the single term-level consumer — reverified by grep).

## Sources (all verified locally 2026-08-10; page numbers = print pages)

- [V] Voight, *Quaternion algebras*, GTM 288 (`Desktop/Papers/Voight - Quaternion
  Algebras.pdf`): 11.3.1, Lemma 11.3.2, Prop. 11.3.4 (p. 169); Lemma 9.4.6 (p. 144),
  Thm. 9.4.9 (p. 145), Lemma 9.5.3 (pp. 145-146); 27.6.1/27.6.3 (pp. 468-469), Lemma
  27.6.8 (p. 469); Lemma 28.2.4 (p. 479).  Text extractions with PDF page numbers in
  the session scratchpad (`voight-ch11.txt`, `voight-27-6b.txt`, `voight-9-45.txt`);
  quotes below are from those extractions with OCR ligatures/spacing normalised.
- [J] Jacobs, *Slopes of compact Hecke operators* (`Desktop/Papers/Jacobs - Slopes of
  Compact Hecke Operators.pdf`): Def. 1.20 (p. 15), Lemma 1.22 + (1.4.4)-(1.4.7)
  (pp. 16-17; PDF pages 14-15).

## The headline result

**R**: `JacobsSlash.hClassNumberOne : HClassNumberOne`, where (`U3/2_Level.lean:645`)
`HClassNumberOne : Prop := ∀ g : Dfx ℚ D, ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U0, g = d * u`.

Source claim (verbatim, [J] Lemma 1.22, p. 16):
> "1.22 Lemma (cf. Theorem 2, Section 3, [Buzc]).  D×_f = D×U₀(1). (1.4.4)
> Proof. The shortest way is to use the Jacquet-Langlands correspondence: we know that
> there are no cusp forms of weight 2, and hence there are no 2-new cusp forms of
> weight 2. […] Since the former space is zero, we obtain one coset."

Lean ↔ source match: `Dfx ℚ D = (D ⊗[ℚ] 𝔸_f^∞)ˣ`, `globalUnits = range of D^×`,
`U0` = the identification-free `U₀(1)` of [J] Def. 1.20 (adelic units integral with
integral inverse at every finite place — the B07 design, audited then).  `g = d·u`
quantified over all `g` is exactly `D×_f = D×·U₀(1)`.

**Source-replacement record**: the thesis's own proof is Jacquet–Langlands and is out
of scope (recorded decision, R-CN1/L1.1).  The formalised proof follows [V]
(11.3.2 → 11.3.4 → 27.6.8), the *classical* proof of the same statement; [V] Lemma
28.2.4 (`GL₂(ℚ̂) = GL₂(ℚ)GL₂(Ẑ)`, proved by the identical lattice argument in the
split case) is the structural template.  This replacement is the ONE deliberate
deviation from the thesis's proof line, inherited from the 2026-08-05 planning and
re-affirmed here.

### Plain-English proof (Step 1; mirrors [V]'s argument)

Let `g ∈ D×_f`.  (0) *Clearing denominators* [V 27.6.1's restricted product]: some
nonzero `N ∈ ℤ` makes `N·g` integral at every place; since `N ∈ D^×` is global, it
suffices to factor everywhere-integral `g`.  (1) *The denominator ideal* [V 27.6.8's
`α̂𝓞̂ ∩ B`]: `I = {y ∈ 𝓞 : g⁻¹y integral at every place}` is a right ideal of `𝓞`; it
contains any common denominator `N₁` of `g⁻¹`, hence `I ≠ 0`.  (2) *Principality*
[V 11.3.4, via the right Euclidean algorithm 11.3.2, via the covering bound 11.3.1]:
`I = x𝓞` with `x ≠ 0`.  (3) *Local recovery* [V 9.4.6/9.5.3, the elementary
approximation]: at each place `w`, every `ξ ∈ g·𝓞_w ∩ 𝓞_w`-side local point is
congruent mod `N₁𝓞_w` to a global element of `I` (approximate the `1,i,j,ω`-coordinates
of `ξ` by integers that are near the coordinates at `w` and valuation-small at the
finitely many other bad places); since `N₁𝓞 ⊆ I = x𝓞`, this gives
`g·𝓞_w ⊆ x·𝓞_w`, i.e. `x⁻¹g` integral at `w`; `g⁻¹x` is integral by `x ∈ I`.  (4)
*Assembly*: `u := x⁻¹g ∈ U₀(1)` and `g = x·u` with `x ∈ D^×` global. ∎

Pointers into the source ([V] p. 169 for (2), p. 469 for (1)+(4), pp. 144-146 for (3),
p. 479 for the split-case template of (0)-(4)): given per-leaf below.

---

## N1 — Euclidean division and principality (`CN1/2_Euclidean.lean`)

Internal node.  Source's own chain [V p. 169]: 11.3.1 (covering bound) → Lemma 11.3.2
(division) → Prop. 11.3.4 (principality).  Composition attack: children proved below
compose exactly as in [V]; the one failure mode (sidedness mismatch) is the L2 catch,
resolved by fixing the statement, see L2.

### L1 `exists_normSq_sub_le_half` — leaf (elementary + mathlib)
- Lean: `CN1/2_Euclidean.lean:43`:
  `∀ γ : ℍ[ℚ], ∃ μ ∈ hurwitzOrder, normSq (γ - μ) ≤ 1/2`
- Source [V 11.3.1, p. 169] (verbatim):
  > "In the Lipschitz order, we see by rounding coordinates that for all γ ∈ B there
  > exists μ ∈ ℤ⟨i, j⟩ such that nrd(γ − μ) ≤ 4·(1/2)² = 1 — a farthest point occurs
  > at the center (1/2, 1/2, 1/2, 1/2) of a unit cube.  But this is precisely the point
  > where the Hurwitz quaternions occur, and it follows that for all γ ∈ B, there
  > exists μ ∈ O such that nrd(γ − μ) < 1.  (In fact, we can take nrd(γ − μ) ≤ 1/2;
  > see Exercise 11.7.)"
- Lean ↔ source: we formalise the Exercise-11.7 strengthening `≤ 1/2` directly (the
  descent needs only `< 1` after scaling, but `≤ 1/2 < 1` is what the two-lattice
  rounding proves in one pass).  `nrd = normSq` on `ℍ[ℚ]` (identical quadratic form).
- Discharge: elementary.  `round : ℚ → ℤ` + `abs_sub_round : |x - round x| ≤ 1/2`
  (verified: `Mathlib/Algebra/Order/Round.lean:193`).  Candidates `μ₁` = coordinatewise
  round into `ℤ⁴` (Hurwitz via `IsHurwitz` all-even parities), `μ₂` = the same for
  `γ - (½,½,½,½)` shifted back (all-odd parities).  With `fᵢ := |γᵢ - round γᵢ| ≤ ½`:
  `normSq(γ-μ₁) = Σfᵢ²`, `normSq(γ-μ₂) = Σ(½-fᵢ)²` (after choosing the half-lattice
  representative on the correct side), and `Σfᵢ² + Σ(½-fᵢ)² = 2Σfᵢ² - Σfᵢ + 1 ≤ 1`
  since `fᵢ ≤ ½ ⟹ fᵢ² ≤ fᵢ/2`; so `min ≤ ½`.  `nlinarith`-friendly.
- Attacks attempted:
  - [2 edge] `γ ∈ 𝓞` already: `μ = γ`, `normSq 0 = 0 ≤ ½` ✓.  `γ = (½,½,½,½)` (deep
    hole of `ℤ⁴`): `μ₂ = γ` itself, distance 0 ✓ — the half-lattice is what saves it;
    with `ℤ⁴` alone the bound is exactly 1 and the strict descent FAILS.  This is the
    R-CN1 "attack-verified strictness check", re-verified: the statement is about `𝓞`,
    not the Lipschitz order, so no flaw.
  - [3 hypothesis] No hypotheses to weaken; over `ℍ[ℚ]` (not `ℍ[ℝ]`) since `round` on
    the coordinate field is all that is used — could generalise to any
    `LinearOrderedField` with `FloorRing`, noted as a generality option, not needed.
  - [4 source-drift] Re-read p. 169: source's `≤ 1/2` is the parenthetical Exercise
    11.7 claim; our statement matches it exactly (non-strict ≤).  The *strict* `< 1`
    used by 11.3.2 follows from `≤ ½ < 1`.  No drift.
  - [5 discharge] `abs_sub_round` verified at expected type in the project's mathlib
    checkout.  `normSq_def'` present (used in `1_Hurwitz.lean:131`).
  - Verdict: SURVIVED.
- Prior-B2: no name/shape match (6 entries checked).

### L2 `exists_div_rem` — leaf (from L1)
- Lean: `CN1/2_Euclidean.lean:49`:
  `∀ a b : hurwitzOrder, b ≠ 0 → ∃ q r, a = b * q + r ∧ hnorm r < hnorm b`
- Source [V Lemma 11.3.2, p. 169] (verbatim):
  > "Lemma 11.3.2. (Hurwitz order is right norm Euclidean). For all α, β ∈ O with
  > β ≠ 0, there exists μ, ρ ∈ O such that α = βμ + ρ (11.3.3) and nrd(ρ) < nrd(β).
  > Proof. If nrd(α) < nrd(β), we may take μ = 0 and ρ = α, so suppose
  > nrd(α) ≥ nrd(β) > 0.  Let γ = β⁻¹α ∈ B.  Then by 11.3.1, there exists μ ∈ O such
  > that nrd(γ − μ) < 1.  Let ρ = α − βμ.  Then by multiplicativity of the norm,
  > nrd(ρ) = nrd(α − βμ) < nrd(β)."
- Lean ↔ source: `a = b * q + r` IS `α = βμ + ρ` (quotient right of the divisor);
  `hnorm r < hnorm b ↔ nrd ρ < nrd β` via `hnorm_coe` + `Nat.cast_lt`.
- Discharge: L1 at `γ := (↑b)⁻¹ * ↑a` (inverse in the division ring `ℍ[ℚ]`,
  `Quaternion.instDivisionRing` verified at `Mathlib/Algebra/Quaternion.lean:1217`);
  `r := a - b*q`; `normSq` multiplicative (`map_mul normSq`, used in
  `1_Hurwitz.lean:161`); `↑(a - b*q) = ↑b * (γ - ↑q)` by `mul_sub`/field_simp;
  `normSq(b(γ-q)) = normSq b · normSq(γ-q) ≤ normSq b / 2 < normSq b` (needs
  `normSq b > 0` from `b ≠ 0`, `hnorm_eq_zero_iff`).
- Attacks attempted:
  - [1 counterexample/composition — **REAL CATCH, fixed at planning time**] The legacy
    skeleton `PhD/Jacobs/U3/ClassNumberOneFallback.lean:32` stated `a = q * b + r`
    (quotient LEFT of divisor).  Attack on the composition with L3: for a RIGHT ideal
    `I` and `a, b ∈ I`, the remainder must be `r = a - b*q` (b right-multiplied,
    staying in `I`); with `a = q*b + r` the term `q*b` need not lie in a right ideal,
    and the descent fails.  [V]'s own Prop. 11.3.4 proof text prints "α = μβ + ρ" but
    then "ρ = α − βμ ∈ I" — internally inconsistent as printed (book/extraction
    typo); the mathematics forces `α = βμ + ρ`, which is what Lemma 11.3.2 states and
    what the skeleton now says.  RESOLUTION: statement corrected to `a = b * q + r`;
    recorded in the file's module docstring.
  - [2 edge] `a = 0`: `q = 0, r = 0`, `hnorm 0 = 0 < hnorm b` needs `b ≠ 0` ✓ (hb).
    `hnorm a < hnorm b` already: `q = 0, r = a` ✓ (the source's first case).
  - [3 hypothesis] `b ≠ 0` necessary (`b = 0` makes `hnorm r < 0` impossible).  Not
    over-determined: no other hypotheses.
  - [4 source-drift] Statement matches (11.3.3) verbatim modulo naming.  Strictness `<`
    preserved.
  - [5 discharge] `hnorm_coe`, `hnorm_eq_zero_iff`, `hnorm_mul` all exist sorry-free in
    `U3/1_Hurwitz.lean` (lines 153, 165, 158) — verified by read.
  - Verdict: SURVIVED (after the sidedness fix).
- Prior-B2: no match.

### L3 `right_ideal_principal` — leaf (from L2 + mathlib)
- Lean: `CN1/2_Euclidean.lean:55`:
  `∀ I : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder, ∃ x, I = Submodule.span _ {x}`
- Source [V Prop. 11.3.4, p. 169] (verbatim):
  > "Proposition 11.3.4. Every right ideal I ⊆ O is right principal, i.e., there exists
  > β ∈ I such that I = βO.
  > Proof. Let I ⊆ O be a right ideal.  If I = {0}, we are done.  Otherwise, there
  > exists an element 0 ≠ β ∈ I with minimal reduced norm nrd(β) ∈ ℤ>0.  We claim that
  > I = βO.  For all α ∈ I, by the […] Euclidean algorithm in Lemma 11.3.2, there
  > exists μ ∈ O such that α = […] with nrd(ρ) < nrd(β); but ρ = α − βμ ∈ I, so by
  > minimality, nrd(ρ) = 0 and ρ = 0, hence α = βμ ∈ βO as claimed."
  (Ellipses: the printed sidedness typo discussed in L2.)
- Lean ↔ source: right ideals = `Submodule 𝓞ᵐᵒᵖ 𝓞` (`Semiring.toOppositeModule`,
  `op s • y = y * s` — verified `Mathlib/Algebra/Module/Opposite.lean:29`);
  `βO = Submodule.span 𝓞ᵐᵒᵖ {β}` via `Submodule.mem_span_singleton`
  (verified `Mathlib/LinearAlgebra/Span/Defs.lean:449`: `∃ a, a • y = x`, i.e.
  `x = y * unop a`).
- Discharge: `I = ⊥` case: `x = 0`, `Submodule.span_zero_singleton`.  Else the set
  `{n | ∃ y ∈ I, y ≠ 0 ∧ hnorm y = n}` is a nonempty set of naturals; take
  `Nat.sInf_mem` (verified in use, e.g. `Mathlib/Dynamics/PeriodicPts/Lemmas.lean:152`)
  for a minimal-norm witness `x`; antisymm: `span ≤ I` by `x ∈ I` + `smul_mem`; `I ≤
  span` by L2-descent (divide `a` by `x`; `r = a - x*q ∈ I` via `sub_mem` +
  `I.smul_mem (op q) hx`; minimality forces `hnorm r = 0`, `hnorm_eq_zero_iff` gives
  `r = 0`).
- Attacks attempted:
  - [2 edge] `I = ⊥` ✓ handled (source's "If I = {0}").  `I = ⊤`: `x` = any unit,
    e.g. minimal norm 1 element — the descent produces it, no special case needed ✓.
  - [1 counterexample] The Lipschitz order analogue is FALSE ([V] Example 11.3.8,
    p. 170: `I = 2O` is not principal over `ℤ⟨i,j⟩`) — confirms the statement is
    genuinely about the Hurwitz order; our `hurwitzOrder` includes `ω`
    (`qomega_mem`, `2_Level.lean:350`) ✓.
  - [3 hypothesis] None to weaken; two-sidedness NOT assumed (right submodule only) —
    matches source.
  - [5 discharge] `Nat.sInf_mem`, `Submodule.mem_span_singleton`,
    `Semiring.toOppositeModule` all verified above; the `ᵐᵒᵖ`-smul direction
    (`op a • b = b * a`) checked against the mathlib source.
  - Verdict: SURVIVED.
- Prior-B2: no match.

---

## N2 — adele integrality (`CN1/3_AdeleIntegrality.lean`)

Internal node.  Source [V 27.6.1, p. 468] (verbatim):
> "The adele ring of B is the restricted direct product of the topological rings Bv
> with respect to Ov: B := ∏′_v Bv = {(αv)v ∈ ∏_v Bv : αv ∈ Ov for all but finitely
> many v}"
and [V 27.6.3] the same for `B̂×` w.r.t. `O×_v`.  In mathlib the scalar case is
literal: `FiniteAdeleRing R K = Πʳ v, [K_v, 𝓞_v]` with element structure
`a.2 : ∀ᶠ v in cofinite, a v ∈ 𝓞_v` (verified,
`Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean:94-105,161`).  Our `D ⊗ 𝔸_f` is
not itself presented as a restricted product (the packaged FLTstuff equivalence
`lTensorEquivLeft` assumes `CommRing M` — discharge-attack finding, see Attacks), so
the two facts N4 needs are proved directly by `TensorProduct` induction.  Composition
attack: an element of `D ⊗ 𝔸_f` is a FINITE sum of pure tensors (`TensorProduct`
induction principle), each pure tensor is a.a.-integral and integer-clearable, and both
properties pass through finite sums (cofinite filter ∩, product of the `N`s) — no gap.

### L4 `exists_intCast_smul_mem_hurwitzOrder` — leaf (elementary)
- Lean: `CN1/3_AdeleIntegrality.lean:43`: `∀ d : D, ∃ M : ℤ, M ≠ 0 ∧ (M:ℚ) • d ∈ hurwitzOrder`
- Source: [V Prop. 11.3.7's "By clearing denominators, there exists nonzero a ∈ ℤ such
  that aO′ ⊆ O" (p. 169-170) — the standard clearing step; arithmetic folklore the
  source uses without proof].
- Lean ↔ source: specialised to a single quaternion.
- Discharge: `M := 2 * (d.re.den * d.imI.den * d.imJ.den * d.imK.den)`; each coordinate
  of `(M:ℚ)•d` is an even integer (`Rat.den_dvd`-style arithmetic; the parity condition
  of `IsHurwitz` holds with all-even `A B C D`).  `Rat.mul_den_eq_num`-adjacent API or
  `Rat.num_div_den` + `push_cast`.
- Attacks: [2 edge] `d = 0`: any `M`, `0 ∈ 𝓞` ✓; `d` already Hurwitz with odd parities
  (e.g. `ω`): `2·1·…` doubles it into all-even ✓ (no claim of minimality).
  [3 hypothesis] `M ≠ 0` in the conclusion is required by N4's use (else `latticeOf`
  sandwich degenerates) — present ✓.  [4 drift] n/a (folklore step, cited as such).
  [5 discharge] `Rat.num_div_den` exists (std).  Verdict: SURVIVED.
- Prior-B2: no match; the `norm_coeff_M22genFun_le` lesson (bare parameter, missing
  hypothesis) checked: `M` is existential, not a bare parameter ✓.

### L5 `exists_intCast_mul_mem_adicCompletionIntegers` — leaf (mathlib valuation API)
- Lean: `CN1/3_AdeleIntegrality.lean:49`:
  `∀ x : v.adicCompletion ℚ, ∃ n : ℤ, n ≠ 0 ∧ (n:K_v) * x ∈ 𝓞_v`
- Source: the standard local statement inside [V 27.6.1]'s restricted product ("αv ∈ Ov"
  after clearing); elementary valuation arithmetic the source leaves implicit.
- Discharge: `Valued.v x =: γ`.  If `γ ≤ 1` take `n = 1`.  Else pick `k` with
  `Multiplicative.ofAdd (-k) ≤ γ⁻¹`-shape; take `n := r^k` for `r ∈ v.asIdeal`
  nonzero (exists: `v.asIdeal ≠ ⊥`, `Ideal.exists_mem_ne_zero`-style;
  `v.intValuation r < 1` by `intValuation_lt_one_iff_mem`-family), then
  `v(n) ≤ (v r)^k → 0` beats `γ`; conclude by `mem_adicCompletionIntegers` +
  `valuedAdicCompletion_eq_valuation'` (both verified present; the latter used at
  `2_Level.lean:400`).  `𝓞_ℚ`-to-`ℤ` bridging via `Rat.ringOfIntegersEquiv` (used at
  `2_Level.lean:405`).
- Attacks: [2 edge] `x = 0`: `n = 1` ✓.  `x` a unit of enormous negative valuation:
  covered by arbitrary `k` ✓.  [3 hypothesis] none.  [5 discharge]
  `mem_adicCompletionIntegers` verified (`AdicValuation.lean:812`); the `ℤᵐ⁰`
  arithmetic is `WithZero` API precedented in the project (`γ₉_lt_one`, L7.4 of qmf).
  [1 counterexample] none possible: `K_v` is the completion of ℚ, every element has
  finite valuation, `v` multiplicative.  Verdict: SURVIVED.
- Prior-B2: no match.

### L6 `exists_intCast_mul_mem_adicCompletionIntegers_forall` — leaf (from L5 + adele structure)
- Lean: `CN1/3_AdeleIntegrality.lean:57`:
  `∀ a : 𝔸_f, ∃ N : ℤ, N ≠ 0 ∧ ∀ v, (N:K_v) * a v ∈ 𝓞_v`
- Source [V 27.6.1] as above (the finiteness of the bad set is the restricted-product
  definition); mirror of FLT's sorried `canonicalForm` (`HurwitzRatHat.lean:93`) in the
  live framework.
- Discharge: bad set `S := {v | a v ∉ 𝓞_v}` finite by `a.2` (mathlib element
  structure, verified).  `N := ∏_{v ∈ S} n_v` from L5.  At `v ∈ S`:
  `v(N·a v) = v(n_v · a v) · ∏_{u≠v} v(n_u) ≤ 1` (each `n_u ∈ ℤ` has `v(n_u) ≤ 1` —
  `intCast` integrality, project-precedented as `IsUltrametricDist.norm_intCast_le_one`
  used at `2_Level.lean:488`).  At `v ∉ S`: both factors integral.
- Attacks: [2 edge] `S = ∅`: `N = 1` ✓ (empty product).  [3 hypothesis] none;
  `N ≠ 0` from nonzero factors ✓.  [5 discharge] `Finset.prod` over
  `Set.Finite.toFinset S` — std API; `a.2` verified at
  `FiniteAdeleRing.lean:161` (used exactly this way in mathlib's own `isUnit_iff`).
  [1 composition] product of per-place clearings can only shrink valuations ✓
  (multiplicativity).  Verdict: SURVIVED.
- Prior-B2: no match.

### L7 `eventually_toLocal_mem_localOrder` — leaf (tensor induction)
- Lean: `CN1/3_AdeleIntegrality.lean:66`:
  `∀ x : D ⊗[ℚ] 𝔸_f, ∀ᶠ w in cofinite, toLocal ℚ D w x ∈ localOrder w`
- Source [V 27.6.1] (the quaternionic restricted product; quote above).  The
  formalisation proves the containment `D ⊗ 𝔸_f ⊆ ∏′_w (D ⊗ K_w)` w.r.t. `localOrder`
  directly rather than via the full equivalence.
- Discharge: `TensorProduct.induction_on x`.  Zero ✓ (`Subring.zero_mem`, cofinite
  trivially).  Pure tensor `d ⊗ a`: pick `M` for `d` (L4); the set
  `{w | a w ∉ 𝓞_w} ∪ {w | v_w(M) ≠ 1}` is finite (`a.2` + `Int.support` finiteness —
  finitely many primes divide `M`, dischargeable via `HeightOneSpectrum.Support.finite`
  applied to `(M:ℚ)⁻¹` or direct `intValuation` factorisation); away from it,
  `toLocal w (d ⊗ a) = d ⊗ (a w)` (`toLocal_tmul`, QMF — used at `2_Level.lean:503`)
  `= (M⁻¹ scalar) • ((M•d) ⊗ (a w))`, and `(M•d) ⊗ (a w) ∈ localOrder w` by
  `tmul_mem_localOrder` (public, `2_Level.lean:104`), with the `M⁻¹` scalar a `w`-unit
  absorbed by `includeRight_mem_localOrder` multiplication.  Sums: cofinite ∩ ✓.
- Attacks: [2 edge] `x = 0` ✓; `x` a pure tensor with `d ∉` any order ✓ (M handles).
  [5 discharge] `toLocal_tmul` name verified in use; `tmul_mem_localOrder` public ✓.
  [composition] finite sums only — `TensorProduct.induction_on` gives add case with
  two eventually-sets, intersect ✓.  [4 drift] the containment direction we prove is
  the ⊆ half of [V 27.6.1]'s equality — sufficient for all uses (ne_bot and bad-set
  finiteness) ✓.  Verdict: SURVIVED.
- Prior-B2: no match.

### L8 `exists_intCast_smul_toLocal_mem` — leaf (tensor induction, from L4+L6)
- Lean: `CN1/3_AdeleIntegrality.lean:75`:
  `∀ x : D ⊗[ℚ] 𝔸_f, ∃ N : ℤ, N ≠ 0 ∧ ∀ w, toLocal ℚ D w ((N:ℚ) • x) ∈ localOrder w`
- Source: as L6 (the `B̂ = ∪_N N⁻¹·𝓞̂` folklore inside [V 27.6.1]; FLT's
  `canonicalForm` statement, being dropped with the file).
- Discharge: `TensorProduct.induction_on`: zero ✓ (`N = 1`); `d ⊗ a`: `N := M · N_a`
  (L4 × L6), `((M·N_a : ℚ)) • (d ⊗ a) = ((M:ℚ)•d) ⊗ ((N_a:ℚ)•a)`-rearrangement
  (`TensorProduct.smul_tmul'`, `smul_tmul`), integral at every `w` by
  `tmul_mem_localOrder`; sums: `N := N₁·N₂`, distribute `smul_add`, each summand stays
  integral after the extra integer factor (integer × localOrder ⊆ localOrder via
  `includeRight` multiplication) ✓.
- Attacks: [2 edge] `x = 0` ✓.  [3 hypothesis] `N ≠ 0` maintained under products ✓.
  [5 discharge] `smul_tmul'` std; rest as L7.  [1 composition] multiplying by MORE
  integers never destroys integrality (needed for the sum case) — holds since
  `(k:K_w) ∈ 𝓞_w` ✓.  Verdict: SURVIVED.
- Prior-B2: no match.

---

## N3 — local coordinates and integer approximation (`CN1/3_LocalApprox.lean`)

Internal node.  Source: [V Lemma 9.5.3, pp. 145-146] — its proof is the source of the
approximation content (verbatim, the key sentences):
> "Letting (r) = pᵉ and taking (9.5.2) on each coordinate, we have an isomorphism
> φ: N/rN ≃ N_p/rN_p induced from the natural inclusion N ↪ N_p.  Now to show the
> inclusion, let y ∈ M_p.  Let x ∈ N ⊆ V be such that φ(x + rN) = y + rN_p; lifting to
> N_p, we find that there exists z ∈ rN_p ⊆ (M′)_p ⊆ M_p such that x = y + z ∈ M_p ∩ V,
> so y = x − z ∈ (M′)_p."
with (9.5.2) (verbatim): "R/pᵉ ≃ R_(p)/pᵉR_(p) ≃ R_p/pᵉR_p" — i.e. *integer
approximation on each coordinate of a free basis*.  Our N3 is exactly this content for
the basis `1, i, j, ω`, with the multi-place divisibility (needed because our global
lattice is cut out at ALL places, [V 9.4.6]) supplied by integer CRT.  [V Lemma 9.4.6,
p. 144] (verbatim, for the global-intersection step used in N4):
> "Lemma 9.4.6. Let M be an R-lattice in V.  Then M = ∩_p M_(p) = ∩_m M_(m) ⊆ V"

### L9 `hurwitzGen_mem` — leaf (project)
- Lean: `CN1/3_LocalApprox.lean:45`: `∀ i, hurwitzGen i ∈ hurwitzOrder`,
  `hurwitzGen = ![1, qi, qj, qomega]`.
- Source [V (11.1.3), p. 166] (verbatim): "O = ℤ + ℤi + ℤj + ℤω = ℤ⟨i, j⟩ + ℤ⟨i, j⟩ω";
  [J p. 22]: "our maximal order O_D is ℤ⟨i, j, ½(1+i+j+k)⟩".
- Discharge: `Subring.one_mem`, `qi_mem`/`qj_mem` (`2_Level.lean:94,97`), `qomega_mem`
  (`2_Level.lean:350`) — all public, sorry-free (read).
- Attacks: [5] all four names verified by read; [2] `Fin 4` exhaustive `fin_cases` ✓;
  [4] basis matches source's four generators exactly ✓.  Verdict: SURVIVED.

### L10 `mem_localOrder_iff_exists_coords` — leaf (project closure induction)
- Lean: `CN1/3_LocalApprox.lean:52`:
  `x ∈ localOrder w ↔ ∃ c : Fin 4 → 𝓞_w, x = ∑ i, hurwitzGen i ⊗ₜ (c i)`
- Source [V 9.4.5/9.5.3's "M ≃ Rⁿ free… choose a basis M = Rx₁ ⊕ ⋯ ⊕ Rxₙ.  Then
  M_p = M ⊗_R R_p ≃ R_p x₁ ⊕ ⋯ ⊕ R_p xₙ" (p. 145, verbatim)] — the local order is the
  `𝓞_w`-span of a `ℤ`-basis of `𝓞`.
- Lean ↔ source: `localOrder w` is `Subring.closure` (Hurwitz image ∪ local integers)
  (`2_Level.lean:70`); the source's free-module presentation becomes the explicit
  4-term sum.  `mem_hurwitzOrder_iff_coords` (`2_Level.lean:384`, public, sorry-free)
  is the `d = Σ nᵢ·basisᵢ` ingredient (coordinates `d.re−d.imK, d.imI−d.imK,
  d.imJ−d.imK, 2d.imK` against `1,i,j,ω` — integer-valued, no `/2`).
- Discharge: (⇐) `tmul_mem_localOrder` + `Subring.sum_mem`.  (⇒)
  `Subring.closure_induction`: generators — `d ⊗ 1` with `d` Hurwitz: coordinates via
  `mem_hurwitzOrder_iff_coords`, coefficients are integers ⊆ `𝓞_w`; `1 ⊗ z`:
  `c = (z,0,0,0)` on the `1`-slot.  Closure under `+`/`neg`: coefficientwise.  Under
  `*`: product of two 4-term sums; each `hurwitzGen i * hurwitzGen j ∈ hurwitzOrder`
  (order closed under `*`), re-expand by `mem_hurwitzOrder_iff_coords` — 16 structure
  terms with integer coefficient matrices; `𝓞_w`-bilinear collect.
- Attacks: [2 edge] `x = 0`: `c = 0` ✓; `x = 1 ⊗ z`: ✓ by construction.
  [1 counterexample-search] Could some `x ∈ localOrder w` need a `½`-coefficient?  No:
  the `1,i,j,ω` coordinates of a Hurwitz quaternion are INTEGERS (this is exactly
  `mem_hurwitzOrder_iff_coords`, proven) — the halves live inside `ω`.  Attack on the
  `(A−E)/2` form dissolved by that lemma.  [5 discharge] cited project lemmas read,
  public, sorry-free.  [3] no hypotheses.  Verdict: SURVIVED.
- Prior-B2: no match.

### L11 `exists_intCast_valued_sub_le` — leaf (mathlib density + integer arithmetic)
- Lean: `CN1/3_LocalApprox.lean:61`:
  `∀ c : 𝓞_w, M ≠ 0 → ∃ z : ℤ, v((c:K_w) − (z:K_w)) ≤ v((M:K_w))`
- Source [V (9.5.2), p. 145] (verbatim): "R/pᵉ ≃ R_(p)/pᵉR_(p) ≃ R_p/pᵉR_p" — the
  surjectivity `ℤ ↠ 𝓞_w/M𝓞_w`.
- Discharge: `HeightOneSpectrum.denseRange_algebraMap` (verified,
  `AdicValuation.lean:883`): get `q ∈ ℚ` with `v(c − q) ≤ v(M)` (`≤` from an open-ball
  choice; `v(M) ≠ 0` by `M ≠ 0`).  Then `v(q) ≤ max(v c, v(c−q)) ≤ 1`, so `q = a/b`
  with `b` a `w`-unit; pick `b' ∈ ℤ` with `b·b' ≡ 1` mod the relevant power
  (`Int.emod`/`Nat.Coprime` arithmetic; `b` coprime to the residue prime since
  `v(b) = 1`), set `z := a·b'`; then `v(q − z) = v(a)·v(1 − b b')/v(b) ≤ v(M)` and
  ultrametric combine.
- Attacks: [2 edge] `c = 0`: `z = 0` ✓; `M = ±1`: `v(M)=1`, any integer within the
  integers works, `z` from density ✓.  [3 hypothesis — B2-family check]
  `M ≠ 0` REQUIRED: at `M = 0` the target is `v(c − z) = 0`, i.e. exact hit —
  generally false.  Present ✓ (this is the `norm_coeff_M22genFun_le` B2 lesson
  applied at planning time).  [5 discharge] `denseRange_algebraMap` verified at exact
  name; `valuedAdicCompletion_eq_valuation'` bridges `v` on `K_w` to `w.valuation` on
  `ℚ` for the rational bookkeeping ✓.  [4 drift] (9.5.2) is stated for completions of
  DVRs — ours is the `w`-completion of ℚ, an instance ✓.  Verdict: SURVIVED.
- Prior-B2: shape lesson applied (above); no name match.

### L12 `exists_intCast_valued_eq_one_of_le` — leaf (integer CRT)
- Lean: `CN1/3_LocalApprox.lean:69`: for finite `T ∌ w`, `M ≠ 0`:
  `∃ m : ℤ, m ≠ 0 ∧ v_w(m) = 1 ∧ ∀ v ∈ T, v(m) ≤ v(M)`
- Source: [V 28.1.1, p. 477] (verbatim):
  > "The starting point is the Sun Zi theorem (CRT): given a finite, nonempty set S of
  > primes, and for each p ∈ S an exponent n_p ∈ ℤ≥1 and an element x_p ∈ ℤ/p^{n_p}ℤ,
  > there exists x ∈ ℤ such that x ≡ x_p (mod p^{n_p}) for all p ∈ S."
  (with `x_p = 0` at the primes of `T` and `x_{p_w} = 1` at the prime of `w`).
- Discharge: per-place: for `v ∈ T` pick `n_v` with `v(n_v) ≤ v(M)` (L5's mechanism on
  the element `M⁻¹`-scaled, or directly `n_v := r^k` powers); `m₀ := ∏ n_v` handles
  `T`; adjust to a `w`-unit: `m := m₀ + p_w^{big}·t`-style CRT, or cleaner: choose each
  `n_v` coprime to the residue prime of `w` from the start (`r ∈ v.asIdeal ∖
  w.asIdeal` exists: distinct maximal ideals are comaximal,
  `Ideal.exists_mem_ne_mem`-family / `Ideal.sup_eq_top`), then `v_w(n_v) = 1`
  multiplicatively.
- Attacks: [2 edge] `T = ∅`: `m = 1` ✓.  [3] `w ∉ T` necessary: with `w ∈ T` the
  conclusion `v_w(m) = 1 ∧ v_w(m) ≤ v_w(M) < 1` is contradictory for `v_w(M) < 1` —
  hypothesis present ✓.  [5 discharge] comaximality of distinct height-one primes:
  `HeightOneSpectrum` are maximal (Dedekind, dim 1) — `Ideal.IsMaximal` API +
  `sup_eq_top` std; `Nat.chineseRemainder`/`ZMod.chineseRemainder` available if the
  congruence route is taken.  Verdict: SURVIVED.
- Prior-B2: no match.

### L13 `exists_intCast_approx` — leaf (from L11+L12)
- Lean: `CN1/3_LocalApprox.lean:80`: for finite `T ∌ w`, `c : 𝓞_w`, `M ≠ 0`:
  `∃ z : ℤ, v_w(c − z) ≤ v_w(M) ∧ ∀ v ∈ T, v(z) ≤ v(M)`
- Source: [V Lemma 9.5.3 proof] (the coordinate approximation, quote at N3 head) +
  [V 28.1.1 CRT] for the multi-place condition; this is precisely the surjectivity
  `ℤ ↠ 𝓞_w/M ⊕ (divisibility at T)` that (9.5.2)-per-coordinate + CRT give.
- Discharge: `m` from L12 (with bound `v(m) ≤ v(M)` at `T`, `w`-unit).  `c/m ∈ 𝓞_w`
  (`m` a `w`-unit: `v_w(c/m) = v_w(c) ≤ 1`).  `t` from L11 approximating `c/m` to
  modulus `M`: `v_w(c/m − t) ≤ v_w(M)`.  `z := m·t`: `v_w(c − z) = v_w(m)·v_w(c/m − t)
  = v_w(c/m − t) ≤ v_w(M)` ✓; at `v ∈ T`: `v(z) = v(m)·v(t) ≤ v(M)·1` ✓ (`t ∈ ℤ`
  integral).
- Attacks:
  - [1 — **REAL CATCH on the first formulation, fixed at planning time**] The naive
    statement "`z ≡ c` at `w` AND `M ∣ z` in `ℤ`" is FALSE whenever `c ∉ M·𝓞_w`:
    integer divisibility by `M` forces `v_w(z) ≤ v_w(M)`, while `w`-closeness to `c`
    forces `v_w(z) = v_w(c)` when `v_w(c) > v_w(M)` — contradiction.  RESOLUTION: the
    divisibility side-condition is stated *valuation-locally at the places of `T`
    only* (which is all N4 consumes), and the `w`-part of the modulus is carried by
    the approximation clause.  This is the reason for the `m`-factorisation design.
  - [2 edge] `T = ∅`: reduces to L11 ✓.  `c = 0`: `z = 0` ✓.
  - [3] `w ∉ T` necessary (as L12).  `M ≠ 0` necessary (as L11).
  - [5] pure composition of L11+L12 with `ℤᵐ⁰` multiplicativity — no new names.
  - Verdict: SURVIVED (after the formulation fix).
- Prior-B2: no name match; this IS the "statement defect caught before work" pattern
  of the qmf log, applied preemptively.

---

## N4 — the dictionary (`CN1/4_Dictionary.lean`)

Internal node.  Source [V Lemma 27.6.8, p. 469] (verbatim):
> "Lemma 27.6.8.  The set of locally principal, right fractional O-ideals is in
> bijection with B̂×/Ô× via the map I ↦ α̂Ô×, where I_p = α_p O_p and α̂ = (α_p)_p;
> this map induces a bijection Cls_R O ↔ B×\B̂×/Ô×. […]
> Proof.  Let I be a locally principal right fractional O-ideal, so I_p = α_p O_p for
> all primes p of R, with α_p well-defined up to right multiplication by an element of
> O×_p, so to I we associate (α_p O×_p)_p = α̂Ô× ∈ B̂×/Ô×.  Conversely, given
> α̂ ∈ B̂×/Ô× we recover I = α̂Ô ∩ B from Lemmas 9.4.6 and 9.5.3."
Split-case template [V Lemma 28.2.4, p. 479] (verbatim, the proof we transpose):
> "Let α̂ ∈ GL₂(Q̂).  Consider the collection of lattices (L_p)_p with
> L_p = α_p ℤ_p² ⊆ ℚ_p².  Since α_p ∈ GL₂(ℤ_p) for all but finitely many p, we have
> L_p = ℤ_p² for all but finitely many p.  By the local-global dictionary for lattices
> (Theorem 9.4.9), there exists a unique lattice L ⊆ ℚ² whose completions are L_p. […]
> Choose a basis for L and put the columns in a matrix α, so L = αℤ².  Then
> ℒ̂ = αẐ² = α̂Ẑ², and there exists γ ∈ GL₂(Ẑ) such that α̂ = αγ̂."
Composition note: for us "choose a basis" becomes "choose a *generator* of the right
ideal" (L3 — this is where class number one enters, replacing freeness over the PID ℤ),
and the two [V 9.4.x] directions become L16 (approximation, ⊇) and the definitional ⊆.
Composition attack (children true, parent false?): the assembled chain was traced
element-by-element in the plain-English proof — each step is one child; the only
subtle point is that `x·localOrder w ⊇ N₁·localOrder w` needs `N₁ ∈ x𝓞` (i.e.
`hN₁mem` routed through `hx : latticeOf g = span {x}`), which L17's statement carries.
No gap found.

### L14 `latticeOf` (+ closure fields, `mem_latticeOf_iff`, `intCast_mem_latticeOf`) — leaf (project)
- Lean: `CN1/4_Dictionary.lean:50` (def; `Iff.rfl` simp lemma compiled without sorry),
  `:66` (`intCast_mem_latticeOf`).
- Source: [V 27.6.8 proof]'s "I = α̂Ô ∩ B" (quote above), integrally truncated: our
  carrier is `{y ∈ 𝓞 : ∀w, g⁻¹y ∈ localOrder w}` = `g𝓞̂ ∩ 𝓞` read through
  denominators (`y ∈ g_w𝓞_w ⟺ g_w⁻¹y ∈ 𝓞_w`).
- Lean ↔ source: the source's fractional `α̂Ô ∩ B` is replaced by the integral
  `∩ 𝓞`-version; the loss (elements of `g𝓞̂ ∩ D` with denominators) is immaterial
  because N4 only runs on everywhere-integral `g`, where `g𝓞̂ ∩ D ⊆ 𝓞̂ ∩ D = 𝓞`
  ([the (1.4.7) content, `mem_hurwitzOrder_of_forall_local`, proven]).
- Discharge: `add_mem'`: `mul_add` + `Subring.add_mem`.  `zero_mem'`: `mul_zero`-image
  + `zero_mem` (`TensorProduct.zero_tmul`).  `smul_mem'`: `op s • y = y * s`;
  `(y·s) ⊗ 1 = (y⊗1)·(s⊗1)` (`Algebra.TensorProduct.tmul_mul_tmul`), associate and
  use `(localOrder w).mul_mem _ (tmul_mem_localOrder s.2 1-form)`.
  `intCast_mem_latticeOf`: `((N₁:𝓞):D) ⊗ 1 = (N₁:ℚ) • (1 ⊗ 1)`-bridging
  (`Int.cast_smul_eq_nsmul`-family + `TensorProduct.smul_tmul`), then the hypothesis
  instance at `w` with `map_smul` of `toLocal`.
- Attacks: [2 edge] `g = 1`: `latticeOf 1 = ⊤` (every `y` works) ✓ sanity.
  [3] no hypotheses on `g` for the DEF (well-defined for all units) ✓; the B2
  bare-parameter lesson does not bite (no boundedness claim in the def).
  [5] `tmul_mul_tmul` std (used at `2_Level.lean:110`); `Iff.rfl` compiled — the
  membership unfold is definitional ✓ (build-verified).  [1] smul sidedness: `op s •
  y = y * s` puts `s` on the RIGHT — matches `g⁻¹y·s = (g⁻¹y)(s⊗1)` needing
  `localOrder`-multiplication on the right ✓ (a left-smul convention would break;
  checked against `Semiring.toOppositeModule`'s definition).  Verdict: SURVIVED.
- Prior-B2: no match.

### L15 `latticeOf_ne_bot` — leaf (from L8 + L14)
- Lean: `CN1/4_Dictionary.lean:73`.
- Source: [V 27.6.8]'s implicit "fractional ideal" nonzeroness; concretely [V Lemma
  9.3.5(b), p. 142] (verbatim): "for each i, there exist r_i ∈ R nonzero such that
  r_i y_i ∈ M hence r := ∏_i r_i ≠ 0 satisfies rJ ⊆ M" — the common-denominator
  sandwich `N₁𝓞 ⊆ I`.
- Discharge: L8 at `↑g⁻¹` gives `N₁ ≠ 0` with `N₁ • g⁻¹` everywhere integral;
  `intCast_mem_latticeOf` puts `(N₁ : 𝓞) ∈ latticeOf g`; `(N₁ : 𝓞) ≠ 0` by
  `Int.cast_injective`-through-`ℚ`-coordinates (`N₁ ≠ 0`, char-zero); `ne_bot` via
  `Submodule.ne_bot_iff`-shape (`∃ y ∈ I, y ≠ 0`).
- Attacks: [2] `g ∈ U0` already: `N₁ = 1` works ✓.  [5] `Submodule.ne_bot_iff` std;
  char-zero of `ℍ[ℚ]` coordinates elementary.  [3] none.  Verdict: SURVIVED.

### L16 `exists_mem_latticeOf_sub_smul` — leaf (THE approximation; from L7, L10, L13, L14)
- Lean: `CN1/4_Dictionary.lean:98`-ish (statement in file, hypotheses: `hg`
  everywhere-integral `g`, `N₁ ≠ 0`, `(N₁:𝓞) ∈ latticeOf g`, `ξ ∈ localOrder w`,
  `g⁻¹ξ ∈ localOrder w`; conclusion `∃ y ∈ latticeOf g, ∃ δ ∈ localOrder w,
  ξ − y⊗1 = (N₁:ℚ)•δ`).
- Source: [V Lemma 9.5.3 proof] (quote at N3 head) — "let x ∈ N be such that
  φ(x + rN) = y + rN_p" is exactly this: a global `x` congruent to the local point
  mod `r·(lattice)`; plus [V 9.4.6] (quote at N3 head) for cutting the global element
  at ALL places (our `y` must satisfy the `latticeOf` condition at every `v`, whence
  the `T`-divisibility).
- Discharge (numbered):
  1. `T` := bad places of `(↑g, ↑g⁻¹)` away from `w`: finite by L7 at both, minus `w`
     (`Set.Finite.toFinset`, `Finset.erase`).
  2. Expand `ξ = Σᵢ cᵢ (bᵢ⊗1)`-form by L10 (coefficients right-side tensor legs).
  3. For each `i`: `zᵢ` from L13 (`T`, `w ∉ T`, `cᵢ`, `M := N₁²` — the square gives
     slack for step 5's division).
  4. `y := Σᵢ zᵢ • hurwitzGen i`-as-`𝓞`-element (`Subring.sum_mem`, `zsmul_mem`,
     L9); `ξ − y⊗1 = Σᵢ (cᵢ − zᵢ)(bᵢ⊗1)` with `v_w(cᵢ − zᵢ) ≤ v_w(N₁²) ≤ v_w(N₁)`:
     coefficients in `N₁𝓞_w`, so the difference is `(N₁:ℚ) • δ`, `δ ∈ localOrder w`
     (L10 backward direction) ✓ second conjunct.
  5. `y ∈ latticeOf g` place by place: at `v ∉ T ∪ {w}`: `g⁻¹_v ∈ localOrder v` (T's
     definition) and `y⊗1 ∈ localOrder v` (`y ∈ 𝓞`), product ✓.  At `v ∈ T`:
     `g⁻¹y = (N₁ g⁻¹)·(y/N₁)`… routed integrally: `v(zᵢ) ≤ v(N₁²)` gives
     `y = N₁·y'`-shape at `v` valuationally; formally: `g⁻¹_v(y⊗1) = (g⁻¹_v(N₁⊗1))·
     ((y/N₁-as-coefficient combination)⊗1)` — implement by writing `zᵢ = N₁·tᵢ + sᵢ`…
     — NO: cleaner (and what the ticket prescribes): strengthen step 3's modulus at
     `T` to `v(zᵢ) ≤ v(N₁)·v(den)`-free form: `g⁻¹_v (y ⊗ 1) = Σᵢ zᵢ • (g⁻¹_v (bᵢ⊗1))`
     and `zᵢ • (g⁻¹_v(bᵢ⊗1)) = (zᵢ/N₁-scalar) • ((N₁g⁻¹)_v (bᵢ⊗1))` with
     `(N₁g⁻¹)_v(bᵢ⊗1) ∈ localOrder v` (hN₁mem-instance) and the scalar `zᵢ/N₁ ∈ 𝓞_v`
     by `v(zᵢ) ≤ v(N₁)` — scalar-multiplication by `𝓞_v` stays in `localOrder v`
     (`includeRight` mult).  ✓ first conjunct.  At `w`: `g⁻¹_w(y⊗1) = g⁻¹_wξ −
     g⁻¹_w(ξ − y⊗1)` = `hξg`-term − `(N₁ g⁻¹)_w • δ`-term, both in `localOrder w` ✓.
- Attacks:
  - [2 edge] `T = ∅` (g integral everywhere with integral inverse — `g ∈ U0`):
    steps degenerate gracefully, `y` from plain L11 approximations ✓.  `ξ = 0`:
    `y = 0, δ = 0` ✓.
  - [3 hypothesis] `hg` used only through `T`-finiteness of the `g`-side — could be
    dropped (L7 gives it) but is kept because N4's caller has it and it simplifies
    `T`'s definition; recorded as an acceptable redundancy, NOT a hidden assumption.
    `hN₁mem` is essential (step 5); `N₁ ≠ 0` essential (division by `N₁`).
  - [1 composition] the `M := N₁²` slack: step 5's `T`-case needs `v(zᵢ) ≤ v(N₁)` and
    step 4 needs `v_w(cᵢ − zᵢ) ≤ v_w(N₁)`; L13 delivers both at modulus `N₁²`
    (`v(N₁²) ≤ v(N₁)`) — single modulus suffices, no circularity.
  - [5 discharge] all consumed leaves are in this tree; scalar-into-localOrder
    multiplication is `includeRight_mem_localOrder` + `mul_mem` (public ✓).
  - Verdict: SURVIVED.
- Prior-B2: no match.

### L17 `exists_eq_generator_mul` — leaf (from L16, L3-shape, L15)
- Lean: `CN1/4_Dictionary.lean:112`-ish.
- Source: [V 28.2.4 proof]'s "Then ℒ̂ = αẐ² = α̂Ẑ², and there exists γ ∈ GL₂(Ẑ) such
  that α̂ = αγ̂" (quote at N4 head) — the generator's completions recover the idele's
  lattice; equivalently [V 27.6.8]'s `I_p = α_p O_p` in the direction global → local.
- Discharge: `ξ := toLocal w ↑g`: `ξ ∈ localOrder w` (hg), `g⁻¹ξ = 1 ∈ localOrder w`
  ✓ hypotheses of L16.  Get `y ∈ latticeOf g = span {x}` and `δ` with
  `ξ = y⊗1 + N₁•δ`.  `y = x·s` (`mem_span_singleton`, `unop`), `y⊗1 = (x⊗1)(s⊗1)`;
  `N₁•δ`: `N₁ ∈ latticeOf g = x𝓞` (L15's witness routed through `hx`) gives
  `N₁ = x·s₀`, so `N₁•δ = (x⊗1)(s₀⊗1)δ`.  Collect: `ξ = (x⊗1)·ζ`,
  `ζ := (s⊗1) + (s₀⊗1)δ ∈ localOrder w` ✓.
- Attacks: [2 edge] `g = 1`: `latticeOf 1 = ⊤ = span{x}` forces `x` a unit; `ζ =
  (x⁻¹⊗1)` — consistent ✓.  [1] does the argument need `x ≠ 0`?  NOT for this
  statement (if `x = 0` then `span{0} = ⊥` contradicts L15 via the caller; here no
  contradiction needed — the identity `ξ = 0·ζ` would force `ξ = 0`; callers supply
  `ne_bot`).  Recorded: the CALLER (L18) must derive `x ≠ 0` from L15 — it does.
  [3] `hg` essential (ξ's membership); `hx` essential.  [5] `mem_span_singleton`
  verified; `tmul_mul_tmul` std.  Verdict: SURVIVED.

### L18 `exists_factor_of_forall_mem` — leaf (assembly over L3, L15, L16, L17)
- Lean: `CN1/4_Dictionary.lean:131`-ish.
- Source: [V 27.6.8] + [V 28.2.4] assembled (quotes above); the `U₀`-membership pair
  is [J Def 1.20]'s `U₀(1)` in the identification-free form (project `U0`,
  `2_Level.lean:296`).
- Discharge: `x` from L3 on `latticeOf g`; `x ≠ 0` from L15 (`span{0} = ⊥`);
  `d := unitsIncl ℚ D (Units.mk0 (x:D) (coe-ne-zero))`; `u := d⁻¹ * g`;
  `g = d·u` trivial.  `u ∈ U0` componentwise: `toLocal w ↑u = (x⊗1)⁻¹·toLocal w ↑g =
  ζ ∈ localOrder w` (L17, cancel `(x⊗1)`); `toLocal w ↑u⁻¹ = g⁻¹_w·(x⊗1) ∈
  localOrder w` (x ∈ latticeOf g — `mem_latticeOf_iff`).  `d ∈ globalUnits` by
  `MonoidHom.mem_range` ✓.
- Attacks: [2] `g = 1`: `d` = unit generator, `u = d⁻¹` — in `U0` since global units
  of `𝓞` are (`unitsIncl_mem_U0_iff`, proven) — consistent ✓.  [1] cancellation
  `(x⊗1)⁻¹`: `x⊗1` is a unit in `D ⊗ K_w` because `x ∈ D^×` and `toLocal∘unitsIncl`
  is a monoid map (`toLocal_unitsIncl`, `2_Level.lean:498`, proven) — no division in
  a non-division ring ✓.  [3] `hg` essential.  [5] `toLocal_unitsIncl` read, public.
  [composition] Units-vs-element bookkeeping (`Units.val_mul`, `map_inv`) — std,
  precedented at `2_Level.lean:551`.  Verdict: SURVIVED.

### L19 `hClassNumberOne` — leaf (assembly over L18, L8)
- Lean: `CN1/4_Dictionary.lean` final theorem.
- Source: [J Lemma 1.22] (quote at R) via the [V]-replacement; the reduction step is
  [V 28.2.4]'s determinant-free analogue of "denominators can be handled globally"
  ([V 28.2.4's preamble] (verbatim): "we recall from 27.2.6 that Q̂× = Q×Ẑ×
  ('denominators can be handled globally')").
- Discharge: given `g`, L8 at `↑g` gives `N` with `N•g` everywhere integral.
  `n_D := Units.mk0 ((N:ℚ):D)`-unit (`N ≠ 0`); `unitsIncl n_D * g` has underlying
  element `N•↑g` (`toLocal_unitsIncl` + `Algebra.TensorProduct` scalar bookkeeping:
  `((N:D)⊗1)·↑g = (N:ℚ)•↑g` — centrality of rational scalars).  L18 on `g' :=
  unitsIncl n_D * g` gives `g' = d·u`; then `g = (unitsIncl n_D)⁻¹·d·u` with
  `(unitsIncl n_D)⁻¹·d ∈ globalUnits` (subgroup, `inv_mem`/`mul_mem` on the range) ✓.
- Attacks: [2] `g ∈ U0` already: chain still runs (`N = 1` allowed) ✓.  [1] scalar
  centrality: `(N:D) ⊗ 1` is central in `D ⊗ K_w`?  `(N:D) = algebraMap ℚ D N` is
  central in `D` (rational scalars commute with quaternions) and `⊗1` preserves it —
  needed for `((N:D)⊗1)·z = N•z`: this is `Algebra.TensorProduct.includeLeft`-of-
  algebraMap = `algebraMap ℚ (D⊗𝔸f)` composed — std `Algebra` lemmas
  (`Algebra.smul_def`) ✓.  [3] none.  [5] all cited project lemmas read.
  Verdict: SURVIVED.

---

## Discharge-attack record on the FLTstuff route (design decision)

`PhD/QMF/FLTstuff/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:261`
`lTensorEquivLeft` requires `[CommRing M]` — attack verified by reading the signature:
it does NOT apply to noncommutative `M = D` or `M = hurwitzOrder` off the shelf.  The
module-level pieces (`lTensorLeft`, `lTensorLeft_bijective`, variables at lines 24-28
allow plain `[Module R M]`) could be adapted, and remain the RECORDED FALLBACK if the
direct `TensorProduct` induction of N2 resists (fallback note in
`3_AdeleIntegrality.lean`'s docstring).  Primary route stays elementary and contained
per the user's containment instruction.

## Prior-B2 consultation (Step 4.6 — summary)

Logs read 2026-08-10: `.mathlib-quality/qmf/b2_log.jsonl` (4 entries),
`.mathlib-quality/b2_log.jsonl` (2 entries); `.mathlib-quality/jacobs/b2_log.jsonl`
absent.  No name matches against L1-L19.  Shape lessons applied:
- "bare parameter missing its hypothesis" (`norm_coeff_M22genFun_le`, `M22half`) →
  every CN1 statement carries `≠ 0` / membership hypotheses; audited per leaf.
- "degenerate representation" (`NewtonPolygon₀.unitSlope_cases`) → edge attacks `I =
  ⊥`, `T = ∅`, `g = 1`, `x = 0` run per leaf above.
- "scalar-normalisation drift" (`charCoeff_M22op_eq`) → no scalars normalised here.

## Confidence gate (Step 5)

1. Every leaf discharged from mathlib (cited + grep-verified in the project's mathlib
   checkout) or from sorry-free project code (cited by file:line, read) — ✓ (no API
   gaps: the one candidate gap, the restricted-product tensor equivalence, was
   AVOIDED by design, with the elementary route's leaves all discharged).
2. Skeleton compiles — ✓ (3581 jobs, sorries only; 2026-08-10).
3. Verbatim quotes per leaf — ✓ (above; internal nodes cite their children or carry
   structural quotes).
4. Adversarial pass — ✓ (per-leaf blocks above; two real catches: L2 sidedness, L13
   formulation — both fixed in the skeleton, not worked around).
5. Prior-B2 checked — ✓ (no matches; lessons applied).
6. Tree mirrors the source — ✓ (N1 = [V] p. 169's own three-step chain; N3 = [V]
   9.5.3's proof structure; N4 = [V] 27.6.8/28.2.4's proof structure; N2 = the
   restricted-product definitions [V] 27.6.1/27.6.3.  LOC estimates in tickets cite
   source proof lengths).
7. Single-conclusion — ✓ (every leaf one conclusion; L14 is a def-plus-API ticket per
   the def-ticket rule; no ∧-bundles except hypothesis-conjunction inside ∃, which is
   shared-witness existential — the `∃ q r, a = b*q+r ∧ hnorm r < hnorm b` and
   `∃ z, approx ∧ small` forms are single-witness specs per
   `references/statement-splitting.md`).

GATE PASSES.  Tickets created 2026-08-10 (see `tickets.md`).
