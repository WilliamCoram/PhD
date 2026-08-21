# Development Plan: laweights — locally analytic weight characters for QMF

**BOARD PATH: `.mathlib-quality/laweights/`** — all artifacts here.  Parallel boards
(`.mathlib-quality/` = NewtonPolygons, `qmf/`, `jacobs/`, `jacobs-endgame/`,
`tatefredholm-eigen/`, `slashRefactor/`, `hurwitz-cn1/`) are other projects' property.
Every `/beastmode` invocation for this project must be told this path explicitly.

**STATUS 2026-08-11: planning COMPLETE.**  R0 (re-homing) executed and green; the
Lean skeleton (six files, 74 sorries, canonical statements) builds across the full
chain (3788 jobs).  `decomposition.md` has the final design (S-parametrised
`WeightSeries` with `LevelBounds`; `Forms` over abstract `(G, θ)`; tier-2 κ as
`Kˣ →* Kˣ` + `ExpansionData`) and the per-leaf statement pointers.  `tickets.md` is
the board.  The file-plan table below is superseded by decomposition.md's skeleton
section (the generic `2_U3Data` layer went to `PhD/TateFredholm/WeightGenFun.lean`,
not `QMF/Weight/GenFun.lean`).

## Goal

Generalise the QMF weight framework so that the abstract definition of overconvergent
quaternionic modular forms allows **weights as general as the thesis's Definition 1.27**
— locally analytic characters κ : ℤ_p^× → 𝒪_p^× — rather than only (a) the classical
algebraic weights `WeightModule R n ν` and (b) the Jacobs fork's hard-coded
`κ(u) = exp₃(t·log₃ u)`, `‖t‖ < 1`.

Source: [Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College
2003] — local PDF `~/Desktop/Papers/Jacobs - Slopes of Compact Hecke Operators.pdf`.
The relevant statements (all read in full):

- **Def 1.26** (p. 18): the Tate algebra `A_p = ℂ_p⟨z⟩`, sup-norm Banach space.
- **Def 1.27** (p. 19): κ "a locally analytic character, i.e. a continuous group
  homomorphism"; `Σ_α = {γ ∈ M₂(ℤ_p) : p^α | c, p ∤ d, det(γ) ≠ 0}`; the weight-κ
  action `z^k ↦ κ(cz+d)/(cz+d)² · ((az+b)/(cz+d))^k` (1.5.13), κ(cz+d) meaning "the
  power series expansion of κ(cz + d) at zero"; "It is an easy check that Σ_α is a
  monoid and that ∥_κ is a right-action of Σ_α on A_p."
- **Def 1.28/1.30, Lemma 1.31** (pp. 19): wild level ≥ p^α; `L(U, A)` for **A any right
  Σ_α-module**; `L(U,A) ≅ ⊕ᵢ A^{Γᵢ}`.
- **Prop 2.6** (p. 29): the generating function `κ(cx+d)/((cx+d)(cx+d−axy−by))`.
- **Lemma 2.7** (p. 30): compactness from `𝒪₃[[x,y]]`-integrality.

## Deliverable split (user-directed)

- **General layer**: `PhD/QMF/Weight/` (new files; additive).  Weight-κ action on the
  Tate-algebra model for an *abstract weight datum*, the resulting overconvergent-forms
  space, Hecke operators (free from the existing slash layer), and the two instances.
- **Convention-neutral analytic substrate**: `1_GenFun` (`ofGenFun` calculus) and
  `U3/1_Compose` (`PowerSeries.compAn`) are already general-`K`; they move (git mv +
  namespace fix) from `PhD/JacobsSlash/` to `PhD/TateFredholm/` so the QMF layer can
  import them without a layering inversion.  `linSeries`/`quadSeries`/`RowInt` (the
  generic parts of `2_U3Data`) move with them.  Recorded in
  `.mathlib-quality/renames.jsonl`.
- **Jacobs consequences**: `PhD/JacobsSlash/` only — the fork's `kappaSlash` exhibited
  as an instance of the general action (`jacobsWeightSeries t ht`), every field
  discharged by *existing fork theorems* (κ-cocycle, RowInt, absSummable, normalisation)
  — **zero re-certification**; plus the honest-character statement that the fork's
  weight is the expansion of `u ↦ u^t`.
- **Classical weights as application**: bridge `WeightModule K n ν ↪ c(ℕ, K)`
  intertwining the existing right slash with the general κ-action at the algebraic
  weight series (κ = pow (n+2), determinant twist as a scalar cocycle twist) — the
  existing `WeightModule` results are consumed, never re-proved.

## Architecture (the abstraction seam)

Audit of `PhD/JacobsSlash/U3/4_KappaSlash.lean` (1570 lines, read in full): every
t-specific input to the development is one of **five facts** about the series
`kappaSeries₂ t c d` (the expansion of κ(cx+d)):

1. normalisation `kappaSeries₂ t 0 1 = 1` (used by `kappaSlash_one`);
2. the κ-cocycle `kappaCol_cocycle`: `κcol(lin (γδ)) = κcol(lin γ) · compAn (κcol(lin δ)) (mobius γ)`
   (used by `kappaSlash_mul`; proved there via ODE + p-adic binomial theorem — the only
   genuinely character-specific analysis);
3. integrality `rowInt_kappaSeries₂` (feeds `coeffInt_/shiftInt_weightGenFun` → the
   `ofGenFun` boundedness/decay pair);
4. summability `absSummable_kappaCol` (feeds the `compAn` manipulations);
5. y-degree-0 concentration (structural, by definition of the expansion).

Everything else in the file — `linSeries/quadSeries/mobius/autFactor` calculus, the
`yCoeff` grading lemmas, `mobius_mul`, `compAn_mobius_mobius`, `CoeffInt/ShiftInt`
algebra, the assembly of `kappaSlash_one/_mul`, the `DistribMulAction` — is κ-generic
and consumes only 1–5.

Hence the general API:

```
structure QMF.WeightSeries (K) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (γlvl : ℝ) : Type _ where    -- exact level parametrisation TBD
  col       : K → K → PowerSeries K                 -- expansion of κ(c·x + d)
  col_zero_one : col 0 1 = 1
  cocycle   : ∀ {γ δ}, <level hyps> → col (lin (γ*δ)) = col (lin γ) * compAn (col (lin δ)) (mobius γ)
  rowInt    : <level hyps> → RowInt-type bound on col
  absSummable : <level hyps> → AbsSummable (col c d)
  ydeg0     : (structural — col is one-variable)
```

with, on top:

- `QMF.Weight.kappaSlash (W : WeightSeries …) : Σ → (c(ℕ,K) →L[K] c(ℕ,K))`, defined as
  `ofGenFun (W.genFun γ)` where `W.genFun γ = W.col₂ γ * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹`
  — **Prop 2.6 holds by construction** (same design as the fork);
- `kappaSlash_one`, `kappaSlash_mul`, `RightSlashAction`/`DistribMulAction` instance —
  ports of the fork's proofs with fields 1–5 replacing the t-specific lemmas;
- the **twisted variant** `kappaSlashTwisted W χ g := χ (det g) • kappaSlash W g` for a
  monoid character χ (general one-line right-action twist lemma) — the vessel for the
  classical determinant twist ν; Def 1.27 is χ = 1;
- `QMF.Weight.kappaForms` — `L(U, A_κ)` via the existing `levelSubmoduleSlash` /
  `heckeOperatorSlash` machinery, which is already weight-agnostic (Def 1.30's "A any
  right Σ_α-module" is exactly the existing design);
- **Tier 2 (honest characters)**: `WeightChar := ContinuousMonoidHom 𝒪ˣ Kˣ` (Def 1.27's
  κ verbatim; mathlib has `ContinuousMonoidHom`, nothing locally-analytic — verified) and
  a constructor `WeightSeries.ofChar` taking κ + an expansion datum (series + pointwise
  evaluation on the closed ball) and **deriving** the cocycle from multiplicativity of κ
  via evaluation injectivity of Tate series (Strassman-type finiteness —
  `PhD/NewtonPolygons/PowerSeriesZeros.lean` §5.14).  Tier 2 is severable: if the
  eval-injectivity discharge grows, tier 1 + both bridges stand alone.

## Instances

- **Jacobs**: `jacobsWeightSeries (t) (ht : ‖t‖ < 1) : WeightSeries K₃ <level 3>` — all
  five fields are existing fork theorems (`kappaSeries₂_zero_one`, `kappaCol_cocycle`,
  `rowInt_kappaSeries₂`, `absSummable_kappaCol`, `coeff_kappaSeries₂`); identification
  `kappaSlash t ht g = QMF.Weight.kappaSlash (jacobsWeightSeries t ht) g` is
  definitional-after-rewrite (both sides are `ofGenFun` of the same series).
- **Classical/algebraic**: `algWeightSeries (n : ℕ) : WeightSeries K <trivial level>` with
  `col c d = (C d + C c·X)^(n+2)` (a polynomial!); cocycle is polynomial algebra (no
  ODE); bridge `polyEmbed : WeightModule K n ν →ₗ[K] c(ℕ,K)` (dehomogenise, finitely
  supported coefficients) with the intertwining
  `polyEmbed (P ∣ₛ δ) = kappaSlashTwisted (algWeightSeries n) (νdet) δ (polyEmbed P)`
  proved columnwise from `yCoeff_weightGenFun` (`column k = j_γ · w_γ^k =
  (cx+d)^{n−k}(ax+b)^k`, a polynomial identity).

## R6 addendum (user-directed 2026-08-11)

The board gained the **subspace-uniformisation tranche** (tickets T018–T020): after
the bridge and milestone are proven, `polySubmodule K n ≤ c(ℕ,K)` is exhibited as
stable under the algebraic-weight action, `polyEmbed` upgrades to a slash-equivariant
isomorphism onto it, and "classical space = polynomial-valued subspace of the
overconvergent space" becomes a two-sided theorem.  The alternative (rebasing the
classical library onto the Tate algebra) was assessed and rejected on merits —
`WeightModule`'s arbitrary-`R`-algebra generality, the architecture-invariance of the
bridge content, and the literature's own presentation — decision record in
decomposition.md §R6.

## Weight-coverage ground truth (verified against the thesis PDF 2026-08-11)

The thesis's *proven* slope theorem carries `t ∈ m₃` (p. 38) — identical to the fork's
`ht : ‖t‖ < 1`; §2.2's ε ∈ {1,2} shifted discs are claimed-but-sketched.  This board
does NOT re-scope the slope results: it generalises the *definition/action layer* (Def
1.26–1.31), where the thesis is genuinely general, and leaves every slope theorem
untouched at its honest hypothesis.

## Mathlib Inventory (verified)

| Concept | Mathlib status | Action |
|---|---|---|
| Tate algebra ℂ_p⟨z⟩ | absent | USE project model `c(ℕ, K)` (TateFredholm) |
| locally analytic character | absent | `WeightChar := ContinuousMonoidHom …` (tier 2) |
| `ContinuousMonoidHom` | `Mathlib.Topology.Algebra.ContinuousMonoidHom` | USE |
| Strassman zero-count | absent in mathlib | USE `PhD/NewtonPolygons/PowerSeriesZeros` §5.14 |
| restricted power series / `ofGenFun` | absent | USE project `1_GenFun` (moves to TateFredholm) |
| analytic substitution `compAn` | absent | USE project `U3/1_Compose` (moves to TateFredholm) |

## File plan (pending explorer confirmation of exact signatures)

| File | Contents | Kind |
|---|---|---|
| `PhD/TateFredholm/GenFun.lean` | move of `JacobsSlash/1_GenFun` (namespace → TateFredholm) + generic `linSeries/quadSeries/RowInt` from `2_U3Data` | MOVE/refactor |
| `PhD/TateFredholm/Compose.lean` | move of `JacobsSlash/U3/1_Compose` (namespace `PowerSeries`, unchanged) | MOVE |
| `PhD/QMF/Weight/Series.lean` | `WeightSeries` structure + constructor API + `genFun` + integrality closure | NEW |
| `PhD/QMF/Weight/SlashAction.lean` | `kappaSlash`, Prop 2.6 by construction, `_one/_mul`, action instances, `kappaSlashTwisted` | NEW (port-shaped) |
| `PhD/QMF/Weight/Forms.lean` | `kappaForms` = `L(U, A_κ)`, Hecke operators via existing slash layer | NEW (thin) |
| `PhD/QMF/Weight/Algebraic.lean` | `algWeightSeries`, `polyEmbed`, the intertwining bridge | NEW |
| `PhD/QMF/Weight/Char.lean` | tier 2: `WeightChar`, expansion data, `WeightSeries.ofChar` via eval-injectivity | NEW |
| `PhD/JacobsSlash/U3/5_KappaWeight.lean` (prefix TBD by import rule) | `jacobsWeightSeries`, `kappaSlash_eq_general`, `IsExpansionOf (u ↦ uᵗ)` | NEW (fork) |

## Generality decisions

- Base field: `K` with `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`
  — the generality `1_GenFun`/`1_Compose` already have; no `CharZero` in the core
  (only Jacobs's binomial instance needs it).
- Level: parametrised (the fork's `Σ₁(3)` vs `Σ₁(9)` distinction shows the acting
  monoid and the estimate threshold must be separate parameters); exact form fixed at
  skeleton time against `Sigma0'`'s parametrisation.
- Determinant twist as a separate scalar character χ (not baked into `col`): Def 1.27
  is χ = 1 (source-faithful); the classical ν lives in χ; the twist lemma is general.
- The cocycle is a **field** of `WeightSeries` (tier 1), a **theorem** for honest
  characters (tier 2 `ofChar`) — this keeps the hard analysis where the source puts it
  (per-character) while the action laws are proven once.
