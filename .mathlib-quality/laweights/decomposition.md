# Decomposition — laweights (locally analytic weight characters for QMF)

**BOARD: `.mathlib-quality/laweights/`.**  Source: [Jacobs, *Slopes of Compact Hecke
Operators*, PhD thesis, Imperial College London, 2003] — local PDF
`~/Desktop/Papers/Jacobs - Slopes of Compact Hecke Operators.pdf` (all page numbers are
the thesis's own).  Secondary source for the abstract layer: the fork's own honest
formalisation of Def 1.27's "easy check", `PhD/JacobsSlash/U3/4_KappaSlash.lean`
(1569 lines, sorry-free) — the thesis defers the action laws ("It is an easy check…"),
and the fork's proof IS the expansion of that check; the generalisation ports it with
the five character-specific inputs abstracted into structure fields.

**Prior-B2 consultation** (`.mathlib-quality/b2_log.jsonl`, 2 entries, both
`NewtonPolygon₀.*`): no name or shape match with any leaf below.  Verdict: clean.

## Skeleton location (Step 2.5 COMPLETE — statements canonical in the `.lean` files)

`lake build` passes across the full chain — **3788 jobs, zero errors** (fork endpoints
`U3.«9_EigenvaluesU3»`, `«5_Instance»`, `U3.«8_HeckeSlopes»`, `U3.«7_DiamondHecke»`,
`QMF.Quaternionic`, `QMF.Slash.Quaternionic`, `QMF.FiniteDimensional` all green) —
verified 2026-08-11.  74 sorries across the six new files; the three moved files are
sorry-free.

- `PhD/TateFredholm/GenFun.lean` — MOVED from `JacobsSlash/1_GenFun.lean` (namespace →
  `TateFredholm`; its redundant `ext_matrixCoeff` deleted — superseded by the more
  general one in `TateFredholm/Matrix.lean`).  Sorry-free.
- `PhD/TateFredholm/Compose.lean` — MOVED from `JacobsSlash/U3/1_Compose.lean`
  (namespace `PowerSeries`, unchanged).  Sorry-free.
- `PhD/TateFredholm/WeightGenFun.lean` — NEW home of `linSeries`, `quadSeries`, their
  `_eq`/`constantCoeff_` lemmas, `fin2_eq_zero` (carved out of `2_U3Data.lean`) +
  `RowIntAt ρ` (the level-`ρ` decay predicate).  Sorry-free.
- `PhD/QMF/Weight/Series.lean` (11 sorries), `SlashAction.lean` (22), `Forms.lean` (3),
  `Algebraic.lean` (18), `Char.lean` (10)
- `PhD/JacobsSlash/U3/5_KappaWeight.lean` (10)

## Design refinements fixed at skeleton time (supersede the draft shapes above)

1. **`WeightSeries` is parametrised by the acting submonoid `S`** (not only by ρ):
   `QMF.WeightSeries (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ)`, with the
   norm bounds packaged as `QMF.LevelBounds S ρ` (a `Prop` field `bounds`).  Reason
   (adversarial finding): the Jacobs character's estimates need `d` a `1`-unit — a
   condition of its domain monoid `Σ₁(3)`, NOT of Def 1.27's `Σ_α` — so the acting
   monoid must be a parameter, with `SigmaNorm K ρ hρ` (Def 1.27's `Σ_α` verbatim in
   norm form) the archetype instance.  This matches Def 1.27's own α-dependence.
2. **`Forms` is stated over an abstract group `G` with a component homomorphism
   `θ : G →* M₂(K)`** (Def 1.28's exact mechanism: "the projection `U_p` is contained
   in `Σ_α`" = `U ⊆ θ⁻¹(S) = levelMonoidOf θ S`).  Reason (adversarial finding): a
   general `v.adicCompletion F` does not carry the normed-field instances compatibly
   as typeclass variables (two `Field`/`UniformSpace` structures = defeq hell); the
   quaternionic instantiation happens where the instances are constructed from the
   valuation (`K₃` now, general completions later).
3. **Tier 2's κ is `Kˣ →* Kˣ` with an `ExpansionData` bundle**, not a
   `ContinuousMonoidHom`: Def 1.27's continuity is what makes the expansion exist;
   the formalisation takes the expansion as the datum (exactly the thesis's "by
   κ(cz + d) we mean the power series expansion"), and multiplicativity is the only
   property the cocycle derivation consumes.
4. `RowInt` stays in the fork (its `‖3‖`-based form untouched); the general layer's
   decay is the `rowDecay` field / `RowIntAt`.

## Canonical statement pointers (skeleton, file:line)

| Leaf | Declaration | Location |
|---|---|---|
| L1.1 | `SigmaNorm`, `mem_sigmaNorm_iff`, `levelBounds_sigmaNorm` | `Series.lean:53,59,73` |
| L1.2 | `LevelBounds` (+`mono`, `d_ne_zero`) | `Series.lean:67,76,80` |
| L1.3 | `genFun`, `norm_coeff_genFun_le_one`, `_le_shift`, `tendsto_coeff_genFun` | `Series.lean:144,151,158,164` |
| — | `WeightSeries` (the structure; cocycle field = the κ-cocycle) | `Series.lean:106` |
| — | `yExtend` (+3 lemmas) | `Series.lean:129–140` |
| L1.4 | `kappaSlash`, `matrixCoeff_kappaSlash` [Prop 2.6] | `SlashAction.lean:71,78` |
| L1.5 | `yCoeff`, `coeff_yCoeff`, `autFactor`, `yCoeff_genFun`, `kappaSlash_apply` | `SlashAction.lean:53,56,65,84,89` |
| L1.6 | `linX_mul`, `numX_mul`, `mobius_mul`, `coeffLeOne_mobius`, `absSummable_mobius`, `compAn_mobius_mobius` | `SlashAction.lean:94–118` |
| L1.7 | `kappaSlash_one` | `SlashAction.lean:124` |
| L1.8 | `kappaSlash_mul`, `kappaSlashAction`, `smulSlashClass` | `SlashAction.lean:129,135,150` |
| L1.9 | `RightSlashAction.comap`, `RightSlashAction.twist` (+`_slash` simp) | `SlashAction.lean:162,179` |
| L1.10 | `Sigma0'.levelBounds` (valuation↔norm dictionary) | `SlashAction.lean:207` |
| L2.1 | `levelMonoidOf`, `levelMonoidOfToS`, `kappaLevelSlashAction`, `kappaLevelSMulSlashClass` | `Forms.lean:55,58,67,72` |
| L2.2 | `Forms` [Def 1.30], `heckeOperator` [Def 1.32] | `Forms.lean:79,88` |
| L3.1 | `jacobsWeightSeries`, `levelBounds_sigma1₃`, `qmfMobius_eq` | `5_KappaWeight.lean:55,45,48` |
| L3.2 | `yExtend_jacobsCol`, `genFun_jacobsWeightSeries`, `kappaSlash_eq_general` | `5_KappaWeight.lean:66,72,78` |
| L3.4 | `hasSum_jacobsCol_unitPow` | `5_KappaWeight.lean:84` |
| L4.1 | `algWeightSeries` (+`_col` simp) | `Algebraic.lean:54,62` |
| L4.2 | `polyEmbed`, `polyEmbed_apply`, `polyEmbed_injective`; `detTwist` | `Algebraic.lean:83,91,96,75` |
| L4.3 | `polyEmbed_slash` (THE bridge) | `Algebraic.lean:103` |
| L4.4 | `mapCoeff` (+`_apply`), `mapCoeff_slash`, `mapCoeff_mem_levelSubmoduleSlash`, `mapCoeff_mem_slashFixedPointsOfLE`, `heckeOperatorSlash_mapCoeff` | `Algebraic.lean:120–178` |
| L5.1 | `evalAt`, `hasSum_evalAt`, `evalAt_one`, `evalAt_mul` | `Char.lean:50–60` |
| L5.2 | `eq_zero_of_forall_evalAt_eq_zero`, `evalAt_injOn` | `Char.lean:67,71` |
| L5.3 | `evalAt_compAn` | `Char.lean:76` |
| L5.4 | `ExpansionData.lin_eval_cocycle` | `Char.lean:105` |
| L5.5 | `ExpansionData` (+`absSummable_col`), `toWeightSeries` | `Char.lean:85,100,113` |

L4.5 (`classicalToOverconvergent`, the quaternionic endpoint) is deliberately NOT in
the skeleton: it composes L4.3 + L4.4 + L2 at the `K₃` instantiation and its statement
form (which `hU`s, twisted level space) is fixed by ticket T-M1 once L4.3/L4.4 are
proven — see tickets.md.  Same for the R0.3-completion note: the fork's `2_U3Data`
now imports the moved files; all cross-references were rewritten
(`JacobsSlash.<moved-name>` → `TateFredholm.<name>`, verified by exhaustive
decl-name-set grep, and by the full green build).

---

## R0 — infrastructure re-homing (refactor, no new mathematics) — **DONE 2026-08-11**

Executed during the skeleton pass (build-gated, zero new sorries, full fork chain
green at 3582 jobs before the skeletons, 3788 with them).  Two deviations from the
draft below, both recorded in the refinements section above: the generic `2_U3Data`
layer went to `PhD/TateFredholm/WeightGenFun.lean` (single re-homing target) rather
than a QMF file, and `RowInt` stayed in the fork (`RowIntAt ρ` is the general form).
`3_BaseChange.lean` needed `open TateFredholm` added (its `namespace JacobsSlash`
section references the moved names bare).

The QMF general layer cannot import `PhD/JacobsSlash/` (layering).  The consumed
infrastructure is already general-`K` (verified by reading the files):

- **R0.1** `1_GenFun.lean` → `PhD/TateFredholm/GenFun.lean`; namespace `JacobsSlash` →
  `TateFredholm`.  Fork files `open TateFredholm JacobsSlash`, so bare references keep
  resolving; explicit `JacobsSlash.ofGenFun`-style references are sed-fixed (grep-driven).
  Recorded in `.mathlib-quality/renames.jsonl`.
- **R0.2** `U3/1_Compose.lean` → `PhD/TateFredholm/Compose.lean`; namespace `PowerSeries`
  unchanged (pure move — the file imports only Mathlib).
- **R0.3** The generic weight-shape layer of `2_U3Data.lean` — `linSeries`, `quadSeries`,
  `RowInt` + its closure algebra (`rowInt_monomial/add/neg/sub/mul/inv`,
  `rowInt_linSeries`, `rowInt_quadSeries`, `constantCoeff_linSeries/quadSeries`,
  `linSeries_eq`, `quadSeries_eq`, `fin2_eq_zero`, the `diagRescale_linSeries/quadSeries`
  and `linSeries_smul`/`quadSeries_smul` rescaling lemmas) — moves to
  `PhD/QMF/Weight/GenFun.lean` (general `K`; `2_U3Data` imports it and keeps only the
  thesis data: ε-matrices, `kappaSeries₂`, `weightGenFun`, the `h`'s, ν-valuation table).
  RowInt's decay base generalises from `‖(3:K)‖` to a parameter `ρ` (`RowIntAt ρ φ`),
  with `RowInt = RowIntAt ‖3‖` as an abbreviation kept for the fork.
- Acceptance for R0: `lake build PhD.JacobsSlash.U3.«9_EigenvaluesU3»` (the deepest
  endpoint) green; zero new sorries; renames recorded.

These are Step-2.5-gated refactor tickets, not decomposition leaves; the adversarial
content is the build gate.

---

## R1 — the general weight-κ action (Def 1.27 for an abstract weight datum)

### Plain-English proof (Step 1)

Source statement, **Def 1.27 (p. 19), verbatim**:

> "Let κ : ℤ×_p → 𝒪×_p be a locally analytic character, i.e. a continuous group
> homomorphism.  Given α ∈ ℕ, let Σ_α = {γ = (a b; c d) ∈ M₂(ℤ_p) : p^α | c, p ∤ d,
> det(γ) ≠ 0}.  The weight κ action of γ = (a b; c d) ∈ Σ_α on A_p is given by the
> continuous ℂ_p-linear extension of the map sending
> z^k ↦ κ(cz + d)/(cz + d)² ((az + b)/(cz + d))^k   (1.5.13)
> and given f(z) ∈ A_p, we write (f‖_κ γ)(z) for this action.  Note, that by κ(cz + d)
> we mean the power series expansion of κ(cz + d) at zero.
> It is an easy check that Σ_α is a monoid and that ‖_κ is a right-action of Σ_α on A_p."

The thesis's proof of the action laws is the deferred "easy check".  Its expansion is
the fork's `4_KappaSlash.lean`, whose structure is (all already formalised at the
Jacobs weight; the generalisation abstracts the κ-inputs):

1. The operator of γ is `ofGenFun` of `κcol(c,d)·(cx+d)⁻¹·(cx+d−axy−by)⁻¹`
   (well-defined by coefficient integrality + column decay).  [Prop 2.6 p. 29 becomes
   the *definition*; the display (2.1.3) is recovered as `yCoeff_weightGenFun`:
   column r = j_γ·w_γ^r.]
2. `‖_κ 1 = id`: at γ = 1 the generating function collapses to `1/(1−xy)` (diagonal),
   using κcol(0,1) = 1.
3. `‖_κ (γδ) = ‖_κ δ ∘ ‖_κ γ` (right action): via columns, reduces to
   (a) Möbius composition `w_{δγ} = w_δ ∘ w_γ` — formal, character-free
   (`mobius_mul`, `compAn_mobius_mobius`), and
   (b) the κ-cocycle `κcol(lin(γδ)) = κcol(lin γ)·(κcol(lin δ) ∘ w_γ)` — the ONLY
   character-specific analytic fact, which the general structure takes as a FIELD
   (each instance proves it its own way: Jacobs by ODE+binomial [already proved,
   `kappaCol_cocycle`], algebraic weights by polynomial algebra, honest characters by
   evaluation injectivity [R5]).
4. Integrality of the generating function on the level monoid (κcol row-decay field +
   the `CoeffInt`/`ShiftInt` closure algebra) gives well-definedness and, later,
   compactness of η-composed operators [Lemma 2.7 pattern].

### The abstract datum (design; canonical form fixed in the skeleton)

```
structure QMF.WeightSeries (K) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (ρ : ℝ) where
  col          : K → K → PowerSeries K          -- the expansion of κ(c·x + d)
  col_zero_one : col 0 1 = 1
  rowDecay     : ∀ {c d}, ‖c‖ ≤ ρ * ‖d‖ → ‖d‖ = 1 → <domain hyps> →
                   ∀ m, ‖PowerSeries.coeff m (col c d)‖ ≤ ρ ^ m
  absSummable  : <same hyps> → AbsSummable (col c d)
  cocycle      : <level hyps on γ, δ> →
                   col (lin (γ*δ)) = col (lin γ) * compAn (col (lin δ)) (mobius γ)
```

(the exact hypothesis bundle mirrors the fork's `norm_sigma1_*` extraction lemmas; the
acting monoid `SigmaLevel K ρ` = {γ : ∀ i j, ‖γ i j‖ ≤ 1, ‖γ 1 1‖ = 1, ‖γ 1 0‖ ≤ ρ,
det γ ≠ 0} is the norm-form of Σ_α: `p^α | c` ↦ `‖c‖ ≤ ρ`, `p ∤ d` ↦ `‖d‖ = 1`,
entries in M₂(ℤ_p) ↦ closed unit ball.  The fork's `Σ₁(3)` will be shown ≤ it.)

### Leaves (Step 2; the source's own sub-structure = the fork's proof layout)

- **L1.1** (leaf, port): `SigmaLevel` is a monoid — closure of the three norm conditions
  under multiplication + `1 ∈`.
  - Source: Def 1.27 p. 19: "It is an easy check that Σ_α is a monoid" (quote above);
    expansion = ultrametric norm arithmetic; the fork's `Sigma1`/`Sigma1₃`
    submonoid proofs (`U3/1_Setting.lean:sigma1_of_mul_eq_one`, `mem_sigma1₃_iff`
    closure) are the formalised template at valuation level.
  - Discharge: `IsUltrametricDist.norm_add_le_max`, `norm_mul`, `Matrix.mul_apply`,
    `Fin.sum_univ_two` (mathlib) — same composition the fork uses.
- **L1.2** (leaf, port): `CoeffInt`/`ShiftInt` closure algebra at decay base ρ —
  `_monomial/_add/_neg/_sub/_mul/_inv` for both.
  - Source: fork `4_KappaSlash.lean:111–285` (proofs verbatim generic: only
    `norm_three_lt_one` specialises the base; replace by `hρ : ρ < 1`).
- **L1.3** (leaf, port): `coeffInt_genFun` / `shiftInt_genFun` / `tendsto_coeff_genFun`
  for `W.genFun γ := (W.col (lin γ)).to2var * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹`,
  γ ∈ SigmaLevel ρ.
  - Source: fork `coeffInt_weightGenFun`/`shiftInt_weightGenFun`/
    `tendsto_coeff_weightGenFun` (`4_KappaSlash.lean:287–393`) with
    `rowInt_kappaSeries₂` replaced by the `rowDecay` field.
  - `to2var`: the y-degree-0 embedding `PowerSeries K → MvPowerSeries (Fin 2) K`
    (new small def + `coeff_to2var`, `yCoeff_to2var_zero`, ydeg-0 lemma).
- **L1.4** (leaf, def + by-construction): `Weight.kappaSlash W γ := ofGenFun (W.genFun γ) _ _`;
  `matrixCoeff_kappaSlash` = **[Prop 2.6]** by construction.
  - Source claim (verbatim, p. 29, Prop 2.6): "The generating function of the operator
    ‖_κ (a b; c d) is given by κ(cx + d)/((cx + d)(cx + d − axy − by))."
  - Lean ↔ source: identical to the fork's design (`matrixCoeff_kappaSlash =
    matrixCoeff_ofGenFun`); the derivation direction (action ⇒ genfun) is recovered by
    L1.5's column identity, exactly as in the fork.
- **L1.5** (leaf, port): `yCoeff` calculus + `yCoeff_genFun : yCoeff (W.genFun γ) r
  = autFactor W γ * (mobius γ)^r` + `kappaSlash_apply`.
  - Source: (2.1.3) p. 29: "κ(cz + d)/(cz + d)² ((az + b)/(cz + d))^r = Σ a_m^{(r)} z^m";
    fork `yCoeff_weightGenFun` (`4_KappaSlash.lean:718–770`) — proof read in full;
    only the ydeg-0 concentration of the κ-series enters (structural for `to2var`).
- **L1.6** (leaf, port): Möbius layer — `linX_mul`, `numX_mul`, `linX_mul_eq`,
  `numX_mul_eq`, `mobius_mul`, `compAn_linX/numX`, `coeffLeOne_mobius`,
  `compAn_mobius`, `compAn_mobius_mobius` at `SigmaLevel` hypotheses.
  - Source: fork `4_KappaSlash.lean:828–1029`; character-free.
- **L1.7** (leaf, port): `kappaSlash_one`.
  - Source: fork `kappaSlash_one` (`:1494`): γ = 1 collapse via `quadSeries_one`,
    `linSeries_one`, and the field `col_zero_one` (fork's private
    `kappaSeries₂_zero_one`).
- **L1.8** (leaf, port): `kappaSlash_mul` + `kappaSlashAction : RightSlashAction
  (SigmaLevel K ρ) c(ℕ, K)`.
  - Source: Def 1.27 p. 19 "‖_κ is a right-action" (quote above); expansion = fork
    `yCoeff_weightGenFun_mul` + `kappaSlash_mul` (`:1400–1460`), consuming the
    `cocycle` FIELD where the fork invokes `kappaCol_cocycle`/`autFactor_cocycle`.
- **L1.9** (leaf, new small): the twist layer — for a monoid hom `χ : S →* Kˣ` and a
  right action, `f ∣ₛ' γ := χ γ • (f ∣ₛ γ)` is again a right action
  (`RightSlashAction.twist`); `kappaSlashTwisted W χ`.
  - Source: none needed (elementary; χ multiplicative ⇒ the cocycle of scalars
    composes).  This is the vessel for the classical determinant character in R4;
    Def 1.27 is χ = 1.  One-paragraph proof: (f∣'γδ) = χ(γδ)•(f∣γδ) =
    χ(δ)χ(γ)•((f∣γ)∣δ) = ((f∣'γ)∣'δ) using scalar-commuting slash
    (`SMulSlashClass`).

### Attacks (Step 4.5 summary; per-leaf logs in the ticket bodies)

- L1.1: edge case ρ = 0 (Σ becomes upper-triangular-with-unit-corner: still a monoid ✓);
  ρ ≥ 1 would break `‖d_g d_h‖` dominance — hypothesis `ρ < 1` included.  Hypothesis
  test: `det ≠ 0` unused by closure (kept for Def-1.27 faithfulness; recorded).
- L1.2–L1.8: the ports were attacked at their original certification (fork board,
  sorry-free, std axioms); the abstraction attack is "does any proof use a property of
  `kappaSeries₂` beyond the five fields?" — verified by reading `4_KappaSlash.lean` in
  full: the only κ-specific inputs are `rowInt_kappaSeries₂`, `absSummable_kappaCol`,
  `kappaCol_cocycle`, `kappaSeries₂_zero_one`, and ydeg-0 concentration.  Each is a
  field or structural.  (`autFactor_cocycle` is derived from `kappaCol_cocycle` in the
  fork — remains a derived lemma generally.)
- L1.9: counterexample search for the twist law with non-commutative scalar target —
  excluded: χ lands in `Kˣ`, central.  Edge χ = 1 recovers the untwisted action
  definitionally.

---

## R2 — the overconvergent forms space at abstract weight (Def 1.30)

### Source (verbatim, p. 19)

> "Fix α ∈ ℕ and κ as in Definition 1.27.  Let U be an open, compact subgroup of D×_f
> of wild level ≥ p^α.  Let A be **any right Σ_α-module**.  The level U, weight κ space
> of automorphic forms is the space L(U, A) = {φ : D×_f → A : φ(dgu) = φ(g)‖_κ u_p
> ∀ d ∈ D×, g ∈ D×_f, u ∈ U}."

and Lemma 1.31: "L(U, A) ≅ ⊕_{i∈I} A^{Γ_i}".

The existing QMF slash layer implements exactly this for **arbitrary** coefficient
right-modules (Def 1.30's "any right Σ_α-module" is the existing design) — so R2 is
*instantiation*, not new mathematics: plug `A = c(ℕ,K)` with the R1 action into
`levelSubmoduleSlash` / `heckeOperatorSlash`.

Leaves (names to be pinned to the QMF inventory in the skeleton):

- **L2.1** (leaf, thin def): `Weight.kappaForms W U := levelSubmoduleSlash …` at the
  adelic pullback of `SigmaLevel`; `SMulSlashClass` instance (scalars commute with
  `ofGenFun` operators — coefficientwise, port of the fork's
  `kappaLevelSMulSlashClass`).
- **L2.2** (leaf, thin): Hecke operators on `kappaForms` — direct application of the
  existing `heckeOperatorSlash`; no new proof (the fork's `heckeU3` pattern at
  abstract weight).

Attack: the only failure mode is a typeclass/parametrisation mismatch between
`SigmaLevel` and the existing adelic level plumbing — this is exactly what the
compiled skeleton (Step 2.5) tests physically.

---

## R3 — the Jacobs instance (no recertification)

### Plain-English (Step 1)

p. 29 (verbatim): "In all cases of (a b; c d) that we will calculate with, c ≡ 0 mod 9
and d ≡ 1 mod 9. … Write cx + d = 4^ρ … Then κ(cx + d) = κ(4^ρ) = κ(4)^ρ = 4^{tρ} =
(4^ρ)^t = (cx + d)^t.  Lastly, we write (cx + d)^t = exp₃(t log(cx + d))."

The fork already formalises this weight completely.  R3 exhibits it as a `WeightSeries`:

- **L3.1** (leaf, project-discharge): `jacobsWeightSeries (t) (ht : ‖t‖ < 1) :
  QMF.WeightSeries K₃ ‖3‖-level` with
  - `col c d := yCoeff (kappaSeries₂ t c d) 0` (the fork's 1-variable κ-column),
  - `col_zero_one` ← fork's `kappaSeries₂_zero_one` (`4_KappaSlash.lean:1476`,
    currently `private` — the fork edit makes it public; one-line consequence),
  - `rowDecay` ← `rowInt_kappaSeries₂` (`2_U3Data`),
  - `absSummable` ← `absSummable_kappaCol` (`4_KappaSlash.lean:1307`),
  - `cocycle` ← `kappaCol_cocycle` (`4_KappaSlash.lean:1251`).
  All five discharges are existing sorry-free fork theorems — **zero new analysis**.
- **L3.2** (leaf, small): the identification
  `JacobsSlash.kappaSlash t ht g = QMF.Weight.kappaSlash (jacobsWeightSeries t ht) g`
  for `g ∈ Σ₁(3) ≤ SigmaLevel`.  Route: both sides are `ofGenFun` of the same
  `MvPowerSeries`; the series equality is `to2var (yCoeff (kappaSeries₂ …) 0) =
  kappaSeries₂ …` (ydeg-0 concentration, `coeff_kappaSeries₂`); `ofGenFun` is
  proof-irrelevant in its hypothesis arguments.
- **L3.3** (leaf, small): `Σ₁(3) ≤ SigmaLevel K₃ ρ₃` — the fork's
  `norm_sigma1_entry_le_one`, `norm_sigma1_lower_right`, `norm_sigma1_lower_left_le`
  read as membership.
- **L3.4** (leaf, small): the honest-character statement: for `‖z‖ ≤ 1`,
  `HasSum (fun m => coeff m (col c d) * z^m) (unitPow t (c*z + d))` — i.e. the fork's
  weight IS the expansion of `u ↦ u^t`.
  - Source: p. 29 (quote above — the thesis's own `κ(cx+d) = (cx+d)^t` identification).
  - Discharge: `tsum_binomialCoeff_eq_unitPow` (`3_BinomialTheorem.lean:252`) +
    `unitPow_mul` (`1_PadicAnalytic.lean`) + geometric algebra: κcol = unitPow t d ·
    binomial series in (c/d)x; at z: unitPow t d · unitPow t (1 + (c/d)z) =
    unitPow t (cz + d).

Attack log highlights: L3.2's "definitional-after-rewrite" claim was attacked by
checking that `ofGenFun` takes its bounds as *proofs* (irrelevant) and its series as
*data* (must match on the nose): it does — `kappaSlash := ofGenFun (weightGenFun t g.1)`
and `weightGenFun = kappaSeries₂ · (lin)⁻¹ · (quad)⁻¹`, so the match reduces to the
to2var lemma.  L3.4 was attacked at the boundary `‖z‖ = 1`: `tsum_binomialCoeff_eq_unitPow`
needs `‖(c/d)z‖` inside the binomial domain — supplied by `‖c/d‖ ≤ ‖3‖`-level bounds,
not by `‖z‖ < 1`; holds on the closed ball. ✓

---

## R4 — the classical/algebraic instance and the bridge (the "application")

### Plain-English (Step 1)

For κ the algebraic character `u ↦ u^{n+2}`, (1.5.13) reads
`z^k ↦ (cz+d)^{n+2}(cz+d)^{-2}((az+b)/(cz+d))^k = (cz+d)^{n-k}(az+b)^k` — for k ≤ n a
polynomial of degree ≤ n.  So the span of `e_0, …, e_n` in the Tate algebra is stable,
and on it the action is the dehomogenisation of Buzzard's right action on `L_{n,ν}`
(`P(X,Y) ↦ ν·P(aX+bY, cX+dY)`, i.e. `p(z) ↦ ν·(cz+d)^n p((az+b)/(cz+d))` at
`p(z) = P(z,1)`), with the determinant character ν as the scalar twist χ of L1.9.
The thesis states this compatibility only implicitly (its Def 1.30 allows any A; the
classical spaces are the polynomial-module instances, cf. [Buzzard, *On p-adic families
of automorphic forms*, §3, cited as [Buzc] in the thesis]); the equational content is
elementary polynomial algebra, expanded by us below (each leaf carries its own
self-contained proof route; no source gap).

Leaves:

- **L4.1** (leaf): `algWeightSeries (n : ℕ) : WeightSeries K ρ` with
  `col c d := (C d + C c * X)^(n+2)` (a polynomial).
  - `col_zero_one`: `(1 + 0)^{n+2} = 1` ✓.
  - `rowDecay`: `coeff m = choose(n+2, m) c^m d^{n+2−m}`; `‖·‖ ≤ ρ^m` from `‖c‖ ≤ ρ`,
    `‖d‖ = 1`, `‖choose‖ ≤ 1` (ultrametric ℤ-integrality).
  - `absSummable`: finitely many nonzero coefficients.
  - `cocycle`: `linX (γδ) = C δ₁₀ · numX γ + C δ₁₁ · linX γ` (= the ported `linX_mul`)
    gives `col(lin(γδ)) = (compAn-form)^{n+2}` via `compAn_linX`, `compAn_pow`,
    `compAn_mul` — polynomial algebra, no ODE.
- **L4.2** (leaf): `polyEmbed : WeightModule K n ν →ₗ[K] c(ℕ, K)` — dehomogenisation
  `P ↦ (coeff of z^k in P(z,1))_k`, i.e. `P ↦ fun k => MvPolynomial.coeff (X^k Y^{n−k}) P`;
  linear, injective on the degree-n homogeneous component; image ⊆ span of `e_0…e_n`.
  - Discharge: `MvPolynomial` coefficient API + `homogeneousSubmodule` membership
    (mathlib); finite support ⇒ `c(ℕ,K)` membership trivially.
- **L4.3** (leaf, THE bridge): for `δ` in (the classical monoid ∩ `SigmaLevel`),
  `polyEmbed (P ∣ₛ δ) = kappaSlashTwisted (algWeightSeries n) χν δ (polyEmbed P)`,
  where `χν := ν ∘ Sigma0'.adj` (multiplicative since `adj` is an anti-hom and `Kˣ`
  is commutative).
  - Route (self-contained): linearity reduces to `P = X^k Y^{n−k}`.  LHS =
    ν(adj δ) · dehom(matrixSubstR δ (X^k Y^{n−k})) = ν(adj δ)·(az+b)^k (cz+d)^{n−k}
    coefficientwise [fork `Slash/WeightModule.lean`: `slash_coe`, `matrixSubstR_X`].
    RHS = χν(δ) · (column-k of the general action) = ν(adj δ) · coefficients of
    `autFactor·mobius^k` [L1.5]; and `autFactor (algW n) δ · (mobius δ)^k =
    (linX δ)^{n−k}·(numX δ)^k` as formal series (`(linX)^{n+2}·(linX)⁻²·(numX/linX)^k`,
    cancellation valid since `constantCoeff (linX δ) = d ≠ 0`).  Conclude by
    `Polynomial`/`PowerSeries` coefficient comparison — both sides are the same
    polynomial `(az+b)^k(cz+d)^{n−k}`.
  - This is the board's one genuinely new computation; it is finite-degree algebra.
- **L4.4** (leaf, general functoriality): an equivariant continuous-linear map of
  coefficient modules induces a Hecke-equivariant map `L(U, A) → L(U, B)` of form
  spaces.
  - Source: Def 1.30/1.32 (verbatim above/p. 20): `L(U,A)` is a transformation-law
    subspace and `[UvU]φ = Σ_t φ|_κ v_t`; a map commuting with every `|_κ u` preserves
    the law and commutes with the finite sum.  Two-line proof from the definitions;
    stated generally in `QMF/Slash/` (module-level, weight-agnostic).
- **L4.5** (endpoint): `classicalToOverconvergent : L(U, WeightModule K n ν) →
  kappaForms (algWeightSeries n) U` Hecke-equivariantly — L4.4 applied to L4.2/L4.3.
  **This is the "algebraic weights survive as an application" deliverable.**

Attacks: L4.3 was attacked at the seam orientation (jTwist / which dehomogenisation):
the fork's right slash uses `matrixSubstR` (untransposed substitution) and the column
formula gives `(cz+d)^{n−k}(az+b)^k` — matching `P(z,1)` dehomogenisation with
`X ↦ az+b`-numerator; the mismatch mode (`P(1,z)`, transposed) was checked and
excluded by computing both on `P = X` at `γ = (a b; c d)`: `matrixSubstR γ X = aX+bY`
→ dehom `az+b` = column-1 numerator ✓.  Determinant-twist attack: with χ = ν∘adj and
`ν = detChar w`, `χ δ = det(adj δ)^w = (det δ)^w` — the classical det-twist on the
nose (`det∘adj = det` for 2×2, as the fork's `Slash/WeightModule` docstring records).

---

## R5 — Tier 2: honest locally analytic characters (severable)

### Plain-English (Step 1)

Def 1.27's κ is a continuous character; the *series* datum of R1 is "the power series
expansion of κ(cz + d) at zero" (p. 19, quote above).  Tier 2 supplies the constructor:
given κ and expansion data (the series + the fact that it evaluates to κ(cz+d) on the
closed unit ball), the `cocycle` and `col_zero_one` fields are THEOREMS:

both sides of the cocycle are restricted series on the closed ball; evaluating at
`z` with `‖z‖ ≤ 1`: `κ(lin(γδ)(z)) = κ(lin γ (z) · lin δ (w_γ(z)))` — the classical
automorphy-factor identity `j(γδ, z) = j(γ, z)·j(δ, γz)` (2×2 matrix algebra) — and κ
is multiplicative (its defining property).  Two restricted series agreeing on the
closed unit ball are equal (Strassman-type uniqueness).  [The thesis performs exactly
this move pointwise at p. 29 — "κ(cx+d) = κ(4^ρ) = κ(4)^ρ" is evaluation-wise — so
tier 2 is the honest general form of the thesis's own argument.]

Leaves:

- **L5.1** (leaf): evaluation of a restricted series at `‖z‖ ≤ 1` (`PowerSeries.evalAt`
  as a tsum; HasSum from `AbsSummable`/coefficient decay) + algebra homomorphism
  properties on restricted series (`evalAt_mul`, `evalAt_one`, …).
  - Discharge: ultrametric summability API (mathlib `IsUltrametricDist` +
    `Summable.tsum_mul_tsum`-style; the fork's `1_Compose` summability toolkit).
- **L5.2** (leaf): **evaluation injectivity** — a radius-1-restricted series vanishing
  on the closed unit ball of `K` is 0.
  - Source: [Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Ch. IV
    (Strassman); local PDF in ~/Desktop/Papers].  Elementary route (our expansion,
    avoiding the Weierstrass machinery): if `f ≠ 0`, take n₀ minimal with
    `coeff n₀ f ≠ 0`; then `f = x^{n₀}·f₁`, and for `0 < ‖z‖ < ‖coeff n₀ f‖ / sup‖coeff‖`
    the ultrametric estimate forces `‖f₁(z)‖ = ‖coeff n₀ f‖ ≠ 0`; such z exist
    (nontrivially normed field: some `0 < ‖x₀‖ < 1`, take powers), contradiction.
- **L5.3** (leaf): `evalAt (compAn F w) z = evalAt F (evalAt w z)` for the relevant
  convergence classes (CoeffLeOne w, AbsSummable F, ‖z‖ ≤ 1).
  - Genuinely new tsum-rearrangement lemma (double sum over `coeff_compAn`'s tsum);
    ultrametric absolute convergence justifies Fubini
    (`Summable.tsum_comm`-family).  **Risk leaf of tier 2** — if it grows, tier 2
    stops behind it without affecting R1–R4.
- **L5.4** (leaf): the pointwise automorphy cocycle `lin(γδ)(z) = lin γ(z) · lin δ(w_γ(z))`
  and `w_{γδ}(z) = w_δ(w_γ(z))` for `‖z‖ ≤ 1`, `γ, δ ∈ SigmaLevel` — 2×2 algebra +
  `evalAt` of the L1.6 formal identities.
- **L5.5** (endpoint): `WeightSeries.ofChar (κ : ContinuousMonoidHom …) (E : ExpansionData κ ρ) :
  WeightSeries K ρ` — fields derived: `cocycle` via L5.1–L5.4 + κ.map_mul;
  `col_zero_one` via evaluation at z (κ(1) = 1) + L5.2.
  - `ExpansionData κ ρ`: the series family + `evalAt (col c d) z = κ (unit (c*z+d))`
    + the ρ-decay.  (Def 1.27's "by κ(cz + d) we mean the power series expansion" —
    the datum IS the thesis's phrase made explicit.)

Attack highlights: L5.2 edge case — residue field infinite vs finite: the proof never
counts residue classes (it uses powers of one small element), so finiteness of the
residue field is irrelevant ✓.  L5.5 hypothesis test: is `norm_eq_one` of κ's values
needed?  Only ρ-decay of the expansion is used; κ landing in 𝒪× is implied at z-values
by the expansion's integrality — recorded as a consequence lemma, not a field.

---

## R6 — the subspace uniformisation (USER-DIRECTED tranche, added 2026-08-11)

### Decision record

The user asked whether the classical layer should instead be **rebased** onto the
Tate algebra (classical module := the polynomial subspace of `c(ℕ,K)`, classical
results re-derived there).  Assessed and rejected on merits, independently of the
recertification cost: (1) `WeightModule R n ν` is defined over an arbitrary
`K`-algebra `R` with no analytic hypotheses — integral structures and the FLT-facing
interface need that generality, and no subspace of `c(ℕ,K)` can provide it; (2) the
bridge theorem ("restricted analytic action = polynomial substitution") is
architecture-invariant — a rebase would move it into the critical path of every
classical computation instead of leaving it at the edge; (3) the literature's own
shape (Buzzard *Eigenvarieties* §9; the thesis) keeps `L_{n,ν}` primary and exhibits
the classical subspace inside the Banach module.  **The adopted uniformisation**: keep
both modules; make "classical = polynomial-valued overconvergent" definition-level
*inside* the overconvergent world via a stable submodule + slash-equivariant
isomorphism.  This tranche is gated on the bridge (T010) and the milestone (T-M1),
whose proven forms fix the statements.

### Plain-English proof

The subspace `P_n := {f ∈ c(ℕ,K) : f m = 0 for m > n}` (the span of `e₀, …, e_n`) is
stable under the algebraic-weight action: by the column identity (L1.5), the image of
`e_k` has coefficient sequence that of `j_γ·w_γ^k = (cx+d)^{n−k}(ax+b)^k` (the
cancellation in L4.3's route), a polynomial of degree ≤ n, so coefficients above `n`
vanish; a general `f ∈ P_n` is a finite combination of `e₀…e_n`, and the operator's
value on it is the corresponding finite sum (the defining tsum truncates).
`polyEmbed` corestricts to a `K`-linear isomorphism `WeightModule K n ν ≃ P_n`
(injectivity is L4.2; surjectivity: a sequence supported in `[0, n]` homogenises to a
degree-`n` homogeneous polynomial with exactly those coefficients), intertwining the
classical slash with the (ν-twisted) restricted action — a restatement of L4.3.  At
the forms level, combining with L4.4/L4.5: a form lies in the image of the classical
space iff it is an overconvergent form (twisted action) whose values all lie in
`P_n`.  [Sources: Buzzard, *Eigenvarieties*, §9 (the classical subspace of the
Banach module); the polynomial-degree computation is L4.3's, already
quote-and-attack-logged under R4 — this tranche adds no new analytic content.]

### Leaves (statements to be skeletonised at tranche start; drafts in tickets.md)

- **L6.1** (leaf): `polySubmodule K n : Submodule K c(ℕ, K)` — carrier
  `{f | ∀ m, n < m → f m = 0}` — with membership API, `single_mem` (k ≤ n), and
  **`polySubmodule_stable`**: invariance under `(algWeightSeries hb n).kappaSlash g`.
  Discharge: `kappaSlash_apply` (L1.5) + the degree bound on
  `autFactor·mobius^k` extracted from L4.3's cancellation step (factor that step as a
  public lemma `coeff_autFactor_mul_mobius_pow_eq_zero_of_lt` when proving T010, so
  L6.1 consumes it rather than re-deriving).
- **L6.2** (leaf): `polyEmbedEquiv n ν : WeightModule K n ν ≃ₗ[K] polySubmodule K n`
  (+ `range_polyEmbed : range (polyEmbed n ν) = polySubmodule K n`), and the
  equivariance restatement of L4.3 through the equivalence.  Discharge: L4.2 +
  homogenisation inverse (`MvPolynomial` monomial assembly; degree bookkeeping via
  `mem_homogeneousSubmodule`).
- **L6.3** (endpoint): the forms-level characterisation — at the T-M1 instantiation,
  `ψ ∈ range (classicalToOverconvergent) ↔ ψ ∈ (twisted) Weight.Forms ∧ ∀ g, ψ g ∈
  polySubmodule K n`.  Forward: T-M1.  Backward: pull back pointwise through
  `polyEmbedEquiv.symm`, check the classical transformation law from the
  overconvergent one via the equivariance (L6.2) — the direction that makes
  "classical = polynomial-valued overconvergent" a two-sided statement.  Statement
  authored against T-M1's proven form.

Attack notes: L6.1 was attacked at the tsum-truncation step (does `kappaSlash g f`
really reduce to a finite sum on `P_n`? — yes: `kappaSlash_apply`'s tsum is over the
support of `f`, `tsum_eq_sum` on finite support); L6.2's surjectivity at `ν`-phantom
(the type `WeightModule K n ν` does not depend on ν — the equivalence is per-ν only
through the ACTION statements, the underlying linear iso is ν-uniform ✓); L6.3's
backward direction was attacked at level-compatibility (the pulled-back function must
be `Γ`-left-invariant and `U`-equivariant for the CLASSICAL action — both transport
through the pointwise iso by equivariance; no gap found).

## API gaps

None outstanding: every leaf above is discharged from mathlib, from existing project
code (fork/QMF/TateFredholm/NewtonPolygons), or is an explicit port with the source
proof already formalised at the Jacobs instance.  The two *new-mathematics* leaves are
L4.3 (finite polynomial computation) and L5.3 (tsum Fubini for compAn evaluation);
both have self-contained routes above and L5.3 is severable with all of tier 2.

## Milestones

- **M1** = L4.5: classical quaternionic forms embed Hecke-equivariantly in the
  overconvergent space at the algebraic weight (no recertification of `WeightModule`).
- **M2** = L3.2 + L3.4: the thesis's `U₃`-action is the general action at the Jacobs
  weight, and that weight is the expansion of `u ↦ u^t`.
- **M3** (tier 2) = L5.5: `WeightSeries.ofChar` — overconvergent forms defined for
  every locally analytic character with an expansion datum at the level, Def 1.27
  verbatim.


---

## §R7 — one-unit characters (USER-DIRECTED 2026-08-12)

**Goal.** Weaken `ExpansionData`'s character from `κ : Kˣ →* Kˣ` to a character on a
subgroup `U ≤ Kˣ`, so the thesis character `unitPow t` — multiplicative ONLY on
1-units (`unitPow_mul`, `1_PadicAnalytic.lean:793`, carries `‖u−1‖ ≤ ‖3‖`,
`‖v−1‖ ≤ ‖3‖`) — instantiates it, making `jacobsWeightSeries` a genuine instance of
`ExpansionData.toWeightSeries` rather than a parallel constructor.

**Source-faithfulness.** [Jacobs, Def 1.27, p. 15]: "Let κ : ℤ×_p → 𝒪×_p be a locally
analytic character".  The formalised character's honest domain is the principal-unit
subgroup: every κ-evaluation the thesis performs is at `cx + d` with `c ≡ 0`,
`d ≡ 1 (mod 9)` ([Jacobs, p. 29]: "In all cases of (a b; c d) that we will calculate
with, c ≡ 0 mod 9 and d ≡ 1 mod 9. … κ(cx + d) = κ(4^ρ) = …", quoted in §R3), i.e. at
1-units.  Abstracting the domain to `U : Subgroup Kˣ` with a level-compatibility field
is Def 1.27 with its evaluation domain made explicit.

**Design decision (recorded).**
1. Generalise `ExpansionData` **in place** (no parallel structure).  Blast radius:
   ZERO — verified 2026-08-12, no file imports `PhD.QMF.Weight.Char` (the only grep
   hit is a docstring in Series.lean).  T012–T015's artifacts are amended; their
   ticket Statements stay canonical for the OLD form, the amendment is recorded here
   and in T021's ticket (T006 CommSemiring precedent).
2. The abstract structure does NOT hard-code the 1-unit ball.  New parameters
   `(U : Subgroup Kˣ) (κ : U →* Kˣ)` + ONE new Prop field
   `mem_level : ∀ {g}, g ∈ S → ∀ z : K, ‖z‖ ≤ 1 → ∀ hu : IsUnit (g 1 0 * z + g 1 1),
   hu.unit ∈ U`, and `eval` returns `κ ⟨hu.unit, mem_level hg z hz hu⟩` (dependent
   field order: `mem_level` before `eval`).  The old behaviour is `U = ⊤`.
3. The concrete 1-unit ball `oneUnits r` lives beside it as reusable API and is used
   only by instantiations (norm-criterion lemma discharges `mem_level`).

**Leaves.**
- L7.1 `oneUnits (r) (hr0 : 0 ≤ r) (hr1 : r < 1) : Subgroup Kˣ`, carrier
  `{u | ‖(u:K) − 1‖ ≤ r}`.  Closure: members have `‖u‖ = 1` (isosceles from
  `‖u−1‖ ≤ r < 1 = ‖1‖`); `mul_mem`: `uv − 1 = u(v−1) + (u−1)`, ultrametric max;
  `inv_mem`: `‖u⁻¹−1‖ = ‖u⁻¹‖·‖1−u‖ = ‖u−1‖` (norm multiplicative on units).
  Criterion lemma: `‖c‖ ≤ r → ‖d−1‖ ≤ r → ‖z‖ ≤ 1 → (unit of c·z+d) ∈ oneUnits r`
  via `cz + d − 1 = cz + (d−1)`, max-bound.
- L7.2 `ExpansionData` amendment + proof adaptation.  `absSummable_col`,
  `lin_eval_cocycle`: untouched (κ-free).  `col_zero_one'`: value at `g = 1` is `1`;
  the subgroup element `⟨hu.unit, mem_level …⟩ = 1` by `Subtype.ext (Units.ext …)`,
  then `map_one`.  `cocycle'`: the three memberships come from `mem_level` at
  `(γ, z)`, `(δ, z′)` (z′ := evalAt (mobius γ) z is on the ball — `mem_level`
  quantifies over the whole ball, attack A1 ✓), `(δγ, z)`; the unit identification
  becomes two-layer `Subtype.ext (Units.ext (lin_eval_cocycle …))`; `map_mul κ` now
  multiplies in `U` (subgroup coe commutes ✓).
- L7.3 `WeightSeries.ext` (Series.lean): two `WeightSeries S ρ` with equal `col` are
  equal — `bounds : LevelBounds S ρ` is a Prop-structure (Series.lean:89 ✓) and the
  remaining fields are Props; `cases`+`subst`+proof-irrelevance.
- L7.4 Jacobs instantiation (5_KappaWeight.lean):
  `jacobsChar t ht : oneUnits ‖(3:K₃)‖ _ _ →* K₃ˣ`, `u ↦ unitPow t u` — unit-ness
  from `norm_unitPow_sub_one_le` (`‖unitPow t u − 1‖ ≤ ‖t‖‖3‖ < 1` ⇒ norm 1 ⇒ ≠ 0);
  `map_one' := unitPow_one`; `map_mul' := unitPow_mul h3lt ht.le u.2 v.2` — THE
  point of the whole tranche: the memberships are exactly `unitPow_mul`'s hypotheses.
  `jacobsExpansionData t ht`: bounds/col/rowDecay as in `jacobsWeightSeries`;
  `mem_level` via L7.1's criterion + `norm_sigma1_lower_left_le` (≤ ‖3‖² ≤ ‖3‖) +
  `norm_sigma1_lower_right_sub_one_le`; `eval := (hasSum_jacobsCol_unitPow …).tsum_eq`
  (hypotheses from `norm_sigma1_ratio_le`; `evalAt` is definitionally that tsum).
  Endpoint: `jacobsWeightSeries_eq_toWeightSeries : jacobsWeightSeries t ht =
  (jacobsExpansionData t ht).toWeightSeries` — both `col`s are the same `mk`-series
  definitionally, close by `WeightSeries.ext rfl`; corollary: `kappaSlash_eq_general`
  re-read through the equality.

**Attacks attempted (all survived).**
- A1 (z′ off the ball?): `mem_level` is ∀-quantified over the closed ball; `z′` has
  `‖z′‖ ≤ 1` by `norm_evalAt_le_one` — no gap.
- A2 (`hu.unit` well-defined across proofs?): `IsUnit` is a Prop; proof irrelevance
  makes `hu.unit` a function of the value — `mem_level`'s ∀ hu form is sound.
- A3 (Jacobs `mem_level` discharge): `‖cz + d − 1‖ ≤ max(‖c‖, ‖d−1‖) ≤ ‖3‖` from the
  two `norm_sigma1_*` lemmas — both exist, sorry-free.
- A4 (unit-ness of `unitPow t u`): via `norm_unitPow_sub_one_le` (1_PadicAnalytic:816,
  verified 2026-08-12) — no Teichmüller extension needed anywhere.
- A5 (`WeightSeries.ext` sound?): `LevelBounds : Prop` verified (Series.lean:89).
- A6 (definitional col match): `jacobsWeightSeries.col = PowerSeries.mk (binomial)`
  by `jacobsWeightSeries_col` rfl-simp; `toWeightSeries.col = E.col` rfl — same term.
- A7 (does the amendment break `toWeightSeries_col`?): no, `col` unchanged.
- A8 (blast radius): no importer of Weight.Char — verified by grep 2026-08-12.
