# Development Plan — `lwx-degrees` (the degrees at every classical weight, and [LWX, Cor 1.4])

**BOARD PATH: `.mathlib-quality/lwx-degrees/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  A parallel run owns `.mathlib-quality/qmf/`
and its `beastmode_active` sentinel — never touch that either (cat before rm; delete only
`.mathlib-quality/lwx-degrees/beastmode_active` and the root sentinel when it names this board).
Every `/beastmode` run must name this board path explicitly.  Planned 2026-09-11.

## STATUS: EXECUTED (`/beastmode`, 2026-09-11) — all 21 proof tickets proved (plus the cleanup helper D22), all 10 cleanups done inline, no `sorry`; gate record (build, `#print axioms`, lint) in `tickets.md` Summary

Skeleton: one new module `PhD/LWX/DegreePeriodicity.lean`, `sorry` only, registered in `PhD.lean`
(see "File structure"); build record in `tickets.md` ("Skeleton build record").  31 tickets
(21 proof + 10 cleanup) in `tickets.md`; milestones **D15** (`degXint_pos_of_atkinLehnerFamily`:
[LWX, Thm 1.3]'s degree statements complete at every weight, granted the family of data) and
**D21** (`degXint_add_period`, with D20: [LWX, Cor 1.4]).

## Goal

[LWX, Theorem 1.3] evaluates the degrees of the components of the spectral curve over the
boundary weight disc `W^{>1/p}_ω` at a neat tame level (`lwx.txt:148–160`):

> `deg X_{n,ω} = r_ord(ω)` if `n = 0`, `= r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n})` if `n ≥ 1`;
> `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` for all `n ≥ 0`, and
> "in particular `deg X_{(n,n+1),ω} > 0` for all `n ≥ 0`".

[LWX, Corollary 1.4] (`lwx.txt:164–169`) reads off from these formulas the shift symmetry
`deg X_{I,ω} = deg X_{I+1,ωω₀²}` for `I = (0,1), 1, (1,2), 2, …` and hence the periodicity of
`deg X_{I,ω}` modulo `ϕ(q)/2` in `I`.  The source gives no proof of the corollary; it is the
substitution `(n, ω) ↦ (n+1, ωω₀²)` in the two formulas, iterated with `ω₀^{ϕ(q)} = 1`
(`lwx.txt:2361`).

At the coefficient level (`degX`, `degXint`, `ordDim` of `StepThree.lean` / `Degrees.lean`; the
Newton-polygon reading of the degrees, see `blueprint/src/chapter/LWXSlopes.tex` §"Degrees") the
project has, **one weight at a time**:

* `degX_zero : degX D ω 0 = ordDim D ω` (unconditional);
* `degX_succ_of_atkinLehnerData : degX D ω (k+1) = ordDim D (partnerChar p ω k) + ordDim D
  (targetChar p ω k)`, granted the Atkin–Lehner data `AtkinLehnerData … (nebCharK ψ ω k ζ)` at the
  weight `(ω, k)` (`lwx-h1`, JL-free);
* `degXint_zero : degXint D ω 0 = p·t − ordDim D ω' − ordDim D ω`, granted H1 at `k = 0`;
* the two gap lemmas `touchX_sub_leftIndex_eq_ordDim` (`n_{k+1} − n⁻_{k+1} = r_ord(ω')`) and
  `rightIndex_sub_touchX_eq_ordDim` (`n⁺_{k+1} − n_{k+1} = r_ord(ω₁)`, granted H2, which
  `isThetaExact_classicalData` supplies at the classical points);

and, from `lwx-conductor`, the **family** `AtkinLehnerFamily θG ψ U Γ ζ` (one section `ιp`, a Hecke
character `χ ω k` at every classical weight `(ω, k)` of conductor `p²`) with
`AtkinLehnerFamily.toData θG ψ U F ω k : AtkinLehnerData …` and `vRepD (toData …) = vRepF F` by
`rfl`, so that one `UpDatum` serves every weight; the unit band at every vertex and disc
(`hasUnitBand_of_atkinLehnerFamily`); and the character arithmetic `partnerChar`, `targetChar`,
`teichChar_pow_sub_one`.

This board proves, granted the family `F` and the neatness data (class set `c`, trivial
stabilisers, the certificates' shape and determinant), in `PhD/LWX/DegreePeriodicity.lean`:

* **the degrees at every weight** — `degX_succ_of_atkinLehnerFamily` (`n ≥ 1`),
  `degXint_of_atkinLehnerFamily` (`deg X_{(n,n+1),ω}` for every `n ≥ 0`, through the two gaps at
  consecutive vertices: `n⁻_{n+1} − n⁺_n = (n_{n+1} − n_n) − (n_{n+1} − n⁻_{n+1}) − (n⁺_n − n_n)`,
  `lwx.txt:2089–2097`), and **positivity** `degXint_pos_of_atkinLehnerFamily` (**M1**);
* **[LWX, Cor 1.4]** — the shift `degX_succ_mul_teichChar_sq`, `degXint_mul_teichChar_sq`, its
  iterates, and the periodicity `degX_succ_add_period`, `degXint_add_period` (**M2**).

No Jacquet–Langlands input anywhere (`.mathlib-quality/lwx-stepone/JL-AUDIT.md`): every ingredient
is the JL-free H1/H2 discharge of `lwx-h1` / `lwx-theta-h2`, and the family of `lwx-conductor`.

**Out of scope** (user decisions of 2026-09-11, recorded in `lwx-stepone/FINDINGS.md`): the
rigid-analytic packaging (`X_{I,ω}` as rigid spaces; the degrees here are the coefficient-level
`degX`/`degXint`), `p = 2`, Step III at level `h`, and the instantiation of `AtkinLehnerFamily`
for `Dfx ℚ D`.

## References

- [LWX] `.mathlib-quality/tate-riesz/references/lwx.txt` (Liu–Wan–Xiao, arXiv:1412.2584v4):
  Thm 1.3's degree display `148–160`; Cor 1.4 `164–169`; the definitions of `t` and `r_ord`
  `123–127`; `n⁻_0`, `n⁺_0` `1923–1927`; §3.23 Step III `2014–2098` (the two gaps `2025–2047`,
  `2048–2078`; the final degree computation `2079–2097`); "since `ω₀^{ϕ(q)} = 1`" `2361`.
- Project code (all sorry-free, standard axioms): `PhD/LWX/StepThree.lean` (`degX`, `degXint`,
  `degX_zero`, `degX_succ`, `degXint_zero`, the gap lemmas, `rightIndex_zero_eq_ordDim`),
  `PhD/LWX/DegreeFormula.lean`, `PhD/LWX/AtkinLehnerIdentity.lean` (`degX_succ_of_atkinLehnerData`,
  `atkinLehnerHypothesis_of_atkinLehnerData`), `PhD/LWX/ThetaExact.lean`
  (`isThetaExact_classicalData`), `PhD/LWX/TargetPoint.lean` (`teichChar`, `targetChar`,
  `targetData_classicalPoint`), `PhD/LWX/NebChar.lean` (`partnerChar`), `PhD/LWX/ClassicalPoint.lean`
  (`classicalData`), `PhD/LWX/Vertices.lean` (`leftIndex`, `rightIndex`, `HasUnitBand`,
  `leftIndex_mem`, `rightIndex_mem`, `rightIndex_le_leftIndex_succ`), `PhD/LWX/Degrees.lean`
  (`ordDim`, `le_card_of_isUnit_charCoeff`, `isUnit_charCoeff_ordDim`),
  `PhD/LWX/AtkinLehnerFamily.lean`, `PhD/LWX/ConductorSlopes.lean`
  (`hasUnitBand_of_atkinLehnerFamily`, and the proofs of `slopeRatio_mul_teichChar_pow` /
  `slopeRatio_add_period` as templates for D18–D21).
- Blueprint: `blueprint/src/chapter/LWXSlopes.tex` §"What Theorem 1.5 says" (Cor 1.4 "likewise not
  formalised") and §"Degrees" — both to be updated when this board completes (CLEANUP-FINAL).

## Mathlib inventory

| Concept | Status | Action |
|---|---|---|
| `(ZMod p)ˣ →* ℤ_[p]ˣ` is a `CommGroup` (`MonoidHom.commGroup`) | mathlib | USE — but prove character identities **pointwise** (`MonoidHom.ext` + `MonoidHom.mul_apply`/`pow_apply`/`inv_apply`/`one_apply` + algebra in `ℤ_[p]ˣ`): `rw [mul_assoc]`/`mul_one` on products of homs fails on an instance-path mismatch (trap recorded on `lwx-conductor`) |
| `mul_inv`, `inv_mul_cancel_left`, `mul_inv_cancel_left`, `pow_add`, `pow_zero`, `inv_one`, `mul_one` (in `ℤ_[p]ˣ`, a `CommGroup`) | mathlib | USE (verified by `#check`) |
| `Nat.Prime.odd_of_ne_two`, `Nat.mul_le_mul_right`, `Fintype.card_pos`, `Nat.mul_succ` | mathlib | USE (verified) |
| `2 * (k + 1) = 2 * k + 2`, `k + 2 = k + 1 + 1` | `rfl` (verified) | USE via `show`/`rw [show … from rfl]` |
| `r_ord(ω) ≤ t` | project: `le_card_of_isUnit_charCoeff` at `isUnit_charCoeff_ordDim` | one API lemma `ordDim_le_card` (D8; natural home `Degrees.lean`, kept in the new file so that this board edits no completed file) |
| everything else | project (see References) | USE |

Nothing new is defined.  The seven character lemmas (D1–D7) are API for `teichChar`, `partnerChar`,
`targetChar`; their natural home is the "partner characters" section of `AtkinLehnerFamily.lean`
(or `TargetPoint.lean`) — kept in the new file for the same reason as D8 (a cleanup may move them
later, with the user's agreement).

## File structure

- `PhD/LWX/DegreePeriodicity.lean` (new; imports `PhD.LWX.ConductorSlopes`):
  1. the character identities under the shift `(I, ω) ↦ (I+1, ωω₀²)` (D1–D7), and
     `mul_teichChar_pow_two_mul_sub_one_div_two` (D22, added at cleanup for D20/D21);
  2. `ordDim_le_card` (D8);
  3. section `Family` — the two gaps, `degX`, `degXint` at every weight, positivity (D9–D15);
  4. [LWX, Cor 1.4]: the shift, its iterates, the periodicity (D16–D21).
- `PhD.lean`: import added with the comment "Board `lwx-degrees` … skeleton, `sorry` only"; the
  comment became "complete, sorry-free" at CLEANUP-FINAL (2026-09-11).

## Dependency graph

```
D1 mul_teichChar_pow_zero ─┐
D2 mul_teichChar_pow_succ ─┼──────────────────────────────► D18, D19 (iterates)
D3 mul_inv_teichChar_pow_zero ──► D14
D4 targetChar_eq_mul_inv_teichChar_pow ──► D14
D5 partnerChar_mul_teichChar_sq_succ ──► D16, D17
D6 targetChar_mul_teichChar_sq_succ ──► D16
D7 mul_teichChar_sq_mul_inv_teichChar_pow_succ ──► D17
D8 ordDim_le_card ──► D15
D9  touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily ─┐
D10 rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily ┼► D13 degXint_succ_… ─┐
D11 degX_succ_of_atkinLehnerFamily ──► D16 ──► D18 ──► D20                        │
D12 degXint_zero_of_atkinLehnerFamily ─────────────────────────────────────────┼► D14 degXint_… ► D15 [M1]
                                                                                └──────────────────► D17 ► D19 ► D21 [M2]
```
(D9–D12 use `classicalData`, `targetData_classicalPoint`, `atkinLehnerHypothesis_of_atkinLehnerData`
at `AtkinLehnerFamily.toData θG ψ U F ω k`, and the level-`1` gap/degree lemmas; D13 also uses
`hasUnitBand_of_atkinLehnerFamily`, `leftIndex_mem`, `rightIndex_mem`,
`rightIndex_le_leftIndex_succ`.)

## Generality decisions

1. **Granted the family, not an instance.**  Every statement of section `Family` takes
   `F : AtkinLehnerFamily θG ψ U Γ ζ` with `hζ : IsPrimitiveRoot ζ p` and the neatness data
   `hfin hv hvinj c hc hstab d hd hfact hshape hdet` as section variables, exactly as
   `ConductorSlopes.lean`'s `section Family` (whose `include` lists are the template; the
   `lwx-conductor` B2 "the `include` list omitted the family" is the trap to avoid — here every
   proof-only hypothesis is in `include hfin hv hvinj c hc hstab d hd hfact hdet in`).
2. **The `UpDatum` is `UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
   hshape`** throughout — the same datum for every weight (`vRepD_toData` is `rfl`), which is what
   makes "every weight at once" a statement about one polygon family.
3. **The character spellings mirror the source's formulas**: `deg X_{n,ω}` at `n = k+1` uses
   `partnerChar p ω k = ω⁻¹ω₀^{2k}` and `targetChar p ω k = ωω₀^{−2k−2}` (as
   `degX_succ_of_atkinLehnerData`); `deg X_{(n,n+1),ω}` uses `partnerChar p ω n = ω⁻¹ω₀^{2n}` and the
   explicit `ω * (teichChar p ^ (2 * n))⁻¹ = ωω₀^{−2n}` (no new definition: at `n = k+1` it is
   `targetChar p ω k`, D4; at `n = 0` it is `ω`, D3).  The shift is `ω * teichChar p ^ 2`, as in
   `slopeRatio_mul_teichChar_sq`; the period is `(p - 1) / 2`, as in `slopeRatio_add_period`.
4. **`ℕ`-subtraction in `degXint_…`** matches the existing `degXint_zero` and the source display
   `qt − r_ord − r_ord`; the proofs establish the additive identity
   `degXint + r + r' = p·t` (via `rightIndex_le_leftIndex_succ`) and `omega` closes.
5. **Cor 1.4 at the integers starts at `n = 1`** (`degX … (k + 1) = degX … (ω * teichChar p ^ 2)
   (k + 2)`): the source's list `I = (0,1), 1, (1,2), 2, …` excludes `I = 0`, and the identity is
   false there in general (`deg X_{0,ω} = r_ord(ω)` vs `deg X_{1,ωω₀²} = r_ord(ω⁻¹ω₀^{−2}) +
   r_ord(ω)`).  On the open intervals it holds from `n = 0`.
6. `[Nonempty ι] [IsAlgClosed K]` and `hp2 : p ≠ 2` as in the level-`1` degree lemmas; positivity
   uses `p ≥ 3` (from `hp2`), `t ≥ 1` (`Nonempty ι`) and `r_ord ≤ t` (D8).

## Engineering notes (for the worker)

- Argument orders (verified by `#check` at planning time):
  `degX_succ_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ D hfin hv hvinj c hc hstab idx uu d hd hfact hshape hdet`;
  `degXint_zero idx hp2 hψ hshape hdet c c' d d' hAL`;
  `touchX_sub_leftIndex_eq_ordDim idx hp2 hψ hshape hdet c c' d d' hAL`;
  `rightIndex_sub_touchX_eq_ordDim idx hp2 hψ hshape hdet c c' d hAL hH2`;
  `isThetaExact_classicalData idx hshape hdet c d`;
  `hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hp2 hψ hζ ω n`;
  `classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k`;
  `targetData_classicalPoint ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k`;
  `atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ hpK D hfin hv hvinj c hc hstab idx uu d hd hfact`;
  `partnerChar_apply ω k r`, `targetChar_apply ω k r`, `MonoidHom.mul_apply f g x`,
  `MonoidHom.pow_apply f n x`, `MonoidHom.inv_apply f x`, `MonoidHom.one_apply x`.
- `exact` accepts data stated for `vRepD θG ψ U (AtkinLehnerFamily.toData θG ψ U F ω k)` where
  `vRepF θG ψ U F` is expected (definitional; proof irrelevance for `vRepF_mem_levelM1` vs
  `vRepD_mem_levelM1`) — the pattern of `hasUnitBand_of_atkinLehnerData` / R13.
- Never `set` the `UpDatum`; if an abbreviation is wanted, `generalize hD : UpDatum.ofCerts … = D at
  h₁ h₂ ⊢` **after** the lemma instances have been obtained.  `omega` treats `p * Fintype.card ι` as
  an atom only after `generalize p * Fintype.card ι = N at …`; keep `touchX …` folded (an atom) in
  the linear bookkeeping and prove `touchX (k+2) = touchX (k+1) + p·t` separately by
  `rw [touchX, touchX]; ring`.
- `omega` not `lia`; no `timeout` binary; `lake exe runLinter PhD.LWX.DegreePeriodicity` is the
  cleanup gate (its findings list every module of the closure — grep for the file name).
