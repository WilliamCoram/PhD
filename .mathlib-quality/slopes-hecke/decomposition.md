# Decomposition — slopes-hecke (`.mathlib-quality/slopes-hecke/`)

## Skeleton location (builds green, sorries only — 2026-08-20)
`PhD/TateFredholm/Slopes.lean` (5), `PhD/QMF/Weight/Slopes.lean` (3),
`PhD/QMF/Weight/HeckeAlgebra.lean` (3), `PhD/QMF/Weight/AdicLevel.lean` (5),
`PhD/QMF/Level.lean` (2).  Verified: `lake build PhD.TateFredholm.Slopes PhD.QMF.Weight.Slopes
PhD.QMF.Weight.HeckeAlgebra PhD.QMF.Weight.AdicLevel PhD.QMF.Level`.
Prior-B2 log (`.mathlib-quality/b2_log.jsonl`): consulted, no name or shape match.

---

## R-A: the slope bound

### Plain-English proof (Serre §5; Jacobs Thm 2.12, pp. 34–35)
`cₙ(u) = ±∑_{|S| = n} det(minor u S)`.  Each `n × n` principal minor is a determinant whose
`j`-th row consists of entries `u_{j i}` with `‖u_{j i}‖ ≤ σ^{w j}`; the ultrametric Leibniz
bound gives `‖det‖ ≤ ∏_{j ∈ S} σ^{w j} = σ^{∑_{j∈S} w j}`.  Since every `n`-element index set
has weight sum at least `f n`, and the ultrametric bounds a (convergent) sum by the max of its
terms, `‖cₙ(u)‖ ≤ σ^{f n}`.  For `I = ℕ`, `w = id` the least sum is `0+1+⋯+(n−1) = n(n−1)/2`
(Jacobs's parabola); for the block model `I = ι × ℕ`, `w = Prod.snd` each value `m` occurs
`|ι|` times so the least sum is `∑_{k<n} ⌊k/|ι|⌋`.  Finally the Newton polygon is the greatest
polygon lying below the points `(n, v(cₙ))`, so any polygon below them — in particular the one
with unit slopes `⌊k/|ι|⌋·v(σ)` — lies below it (`IsNewtonPolygonOf.isGreatest`).

### Leaves
- **A-L1** (leaf, project+mathlib): `norm_det_le_pow_of_row_bound` — `TateFredholm/Slopes.lean`.
  Source [Jac03, proof of Thm 2.12, p. 34]: > "each term of the Leibniz expansion is a product
  of one entry from each row, so its norm is at most `∏_j |3|^{w_j}`; the ultrametric inequality
  bounds the sum by the maximum." Lean ↔ source: identical with `σ` for `‖3‖` and a general row
  weight.  Discharged by: `Matrix.det_apply`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
  `norm_prod`, `Finset.prod_le_prod` — the fork's `norm_det_le_of_row_bound`
  (`1_SlopeTheorem.lean:67`, sorry-free) is this proof at `σ = ‖3‖`.
  Attacks: [1] no contradicting lemma (`norm_det` bounds in mathlib are all upper bounds of this
  shape); [2] `n = 0`: `det = 1`, `σ^0 = 1` ✓ — needs `σ ≤ 1` nowhere at `n = 0`, and for `n ≥ 1`
  the bound is monotone in each row; [3] hypothesis `σ ≤ 1` is needed for `∏ ≤ σ^{∑}` when
  entries are *below* their bounds — kept; `hσ0` needed for `pow_nonneg`. [5] the fork's proof is
  sorry-free and generalises verbatim.  SURVIVED.
- **A-L2** (leaf, project): `norm_minor_le_pow_sum` — transport along `Finset.orderIsoOfFin`,
  exactly the fork's private `norm_minor_le_pow_sum` (`1_SlopeTheorem.lean:223`) with `w` general.
  Source: same page.  Attacks: [2] `S = ∅` ⇒ both sides `1`; [3] no cardinality hypothesis needed
  once `w` is general (the fork's `hS : S.card = m` was only for the `Fin m` transport — keep it
  as an implicit via `S.card`); [5] fork proof sorry-free.  SURVIVED.
- **A-L3** (leaf, combinatorial): `choose_two_le_sum` — the fork proves the strict version
  `choose_two_lt_sum_of_ne_range` (`1_SlopeTheorem.lean:133`, sorry-free) via
  `sum_range_le_sum_and_eq`; the `≤` form is that lemma's first component.  Source [Jac03, p. 34]:
  > "the smallest possible value of `∑_{i ∈ S} i` for `|S| = m` is `0 + 1 + ⋯ + (m−1)`."  SURVIVED.
- **A-L4** (leaf, combinatorial): `sum_div_le_sum_block` — for `S ⊆ ι × ℕ` with `|S| = n`, the
  multiset of second coordinates has at most `|ι|` copies of each value, so its sum is at least
  the sum of the `n` smallest such values, `∑_{k<n} ⌊k/|ι|⌋`.  Source: the same counting, applied
  to Jacobs's `3`-block model ([Jac03, p. 21]: "`U_p` can be represented as `|I|²`
  endomorphisms").  Discharged by: `Finset.sum_le_sum_of_ne_zero`-style counting; mathlib
  `Finset.exists_subset_card_le`/`Finset.sum_range_id`.  Attacks: [2] `n = 0` ✓; `|ι| = 1` gives
  back A-L3 (`∑_{k<n} k = n(n−1)/2`) ✓; [3] `Fintype ι` needed for `Fintype.card`; [4] this is
  our counting, not a source statement — flagged as an *expansion* of the source (allowed: the
  source works after transporting the 3-block operator to `c(ℕ,K)`); SURVIVED.
- **A-L5** (leaf, project): `norm_charCoeff_le_pow` — `charCoeff`, `norm_tsum_le_iSup`
  (used at `Fredholm.lean:242`), A-L2, `hf`, `pow_le_pow_of_le_one`.  Source [Ser62, §5];
  [Jac03, Thm 2.12].  Attacks: [3] `hu : IsCompactoid u` needed for summability of the minors
  (`summable_minor`); [5] `norm_tsum_le_iSup` + `summable_minor` both sorry-free.  SURVIVED.
- **A-L6** (leaf, project): `norm_matrixCoeff_heckeBlock_le` / `_heckeBlockOp_le` — `heckeBlock`
  is `∑_t χ(w) • κ.kappaSlash w`; `matrixCoeff_sum`/`matrixCoeff_smul`, the ultrametric sum
  bound, `norm_matrixCoeff_kappaSlash_le` (SlashAction.lean:386) at the certificate elements
  with `norm_det_toMatrix_certificate_le`, and `hnorm : ‖χ g‖ ≤ 1`.  Source [Jac03, Lemma 2.7];
  [Buz07, Lemma 12.2] ("the fact that `n` and `v` take values … with supremum norm 1 easily
  implies that `γ : A_{κ,r} → A_{κ,r}` is norm-decreasing").  Attacks: [3] `hnorm` is exactly
  Buzzard's "supremum norm 1" hypothesis on the twist — necessary, since a large `χ` would
  destroy the bound; at `χ = 1` it is `norm_one`; [5] all cited decls sorry-free.  SURVIVED.
- **A-L7** (internal): `norm_charCoeff_heckeCharPowerSeries_le` = A-L5 at A-L6's decay with
  `w = Prod.snd`, `f = ∑_{k<n} ⌊k/|ι|⌋` (A-L4).  Composition attack: could the blocks decay but
  the operator not?  No — `matrixCoeff_blockOp` is literally the block's coefficient.  SURVIVED.
- **A-L8** (leaf, project): the Newton-polygon statement — `IsNewtonPolygonOf.isGreatest`
  (`NewtonPolygons/Spec.lean:71`): > "Any polygon with the same starting `x`-coordinate lying
  on/below the points lies on/below `P`."  With `Q := ofSlopes (k ↦ ⌊k/|ι|⌋ · v σ)` and
  `height_ofSlopes` (4_SlopeReading.lean:155) this is A-L7 re-read through `pointHeight`.
  Starting points agree because `charCoeff u 0 = 1` (`charCoeff_zero`).  Attacks: [2] `n = 0`
  fixes the starting vertex ✓; [3] needs `ofSlopes`'s monotone-slope hypothesis — `⌊k/d⌋` is
  monotone ✓; [5] `isGreatest` is a field of the spec structure, sorry-free.  SURVIVED.

## R-B: the Hecke-algebra datum and its consequences

### Plain-English proof ([Buz07, §5 p. 33])
Buzzard's machine takes a commutative `R`-algebra `T` with `T → End(M)` and a compact `φ ∈ T`.
Given the Riesz decomposition `M = N ⊕ F` at a zero of `det(1 − Tφ)`, every `t ∈ T` commutes
with `φ`, hence preserves `N = ker((1 − aφ)^h)`.  `N` is finite-dimensional, so a commuting
family of endomorphisms of `N` over an algebraically closed field has a common generalised
eigenvector: a system of eigenvalues.

### Leaves
- **B-L1** (leaf, project): `heckeOperatorSlash_comm_of_reps` — both operators expanded by
  `heckeOperatorSlash_eq_finsetSum` (`Slash/HeckeMonoid.lean:204`), `slash_mul`, `Finset.sum_comm`
  and the supplied bijection `e`.  Source [Buz07, §9 p. 69] (the coset expansion) + §5 p. 33
  (commutativity is *data*, hence the criterion form).  Lean ↔ source: the source never proves
  commutativity, so we state the criterion and leave its discharge to the caller.  Attacks:
  [3] the naive "disjoint support ⇒ commuting representatives" is **FALSE** (representatives are
  `η·u` with `u ∈ U` global), which is why the hypothesis is a pairing bijection — this attack
  succeeded against the first draft and the statement was corrected;  [5] `…_eq_finsetSum`
  sorry-free.  SURVIVED (after correction).
- **B-L2** (leaf, mathlib): `mapsTo_ker_of_commute` — `Commute.pow_left`/`apply_of_mul_eq`
  style: `(1 − a•φ)^n (t x) = t ((1 − a•φ)^n x) = 0`.  Source [Buz07, p. 33] ("the `T`-action
  preserves the decomposition").  Attacks: [2] `n = 0` ⇒ hypothesis is `x = 0` ✓; [3] only
  `Commute φ t` needed; [5] `Commute.pow_left` exists.  SURVIVED.
- **B-L3** (leaf, mathlib): `exists_common_eigenvector` —
  `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo` (Eigenspace/Pi.lean:148) gives
  that the simultaneous generalised eigenspaces span; a nonzero space then has a nonzero one.
  Source: standard linear algebra (Buzzard uses it implicitly for "system of eigenvalues").
  Attacks: [2] `M = 0` excluded by `Nontrivial M`; [3] `IsAlgClosed` and `FiniteDimensional`
  both needed (`ℚ₃` has irreducible quadratics; infinite-dimensional fails); [5] the mathlib
  lemma's hypotheses (`∀ i j, MapsTo`) follow from commutation.  SURVIVED.
- **B-L4** (internal, MILESTONE): the eigen-system on the Riesz subspace = B-L2 (stability) +
  `exists_riesz_decomposition_forms` (finite rank) + B-L3.  Composition attack: `N` could be
  zero — excluded because `1 ≤ h` and `finrank N = h`.  SURVIVED.

## R-C: the level dictionary
- **C-L1** (leaf, mathlib): `Sigma0'.levelBounds_valued` — **verified during planning**: the
  10-line proof `Sigma0'.levelBounds (norm_nonneg _) (norm_lt_one_iff.mpr …) …
  norm_le_one_iff.mpr / le_antisymm … / norm_le_iff.mpr` compiles at `v.adicCompletion F`.
  Source: mathlib `Valued.toNormedField.norm_le_iff` (`NormedValued.lean:242` area):
  > "theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1".  Lean ↔ source: the three hypotheses of
  `Sigma0'.levelBounds` are exactly these iffs at `y`, `1`, `1`.  Attacks: [3] `RankOne` is what
  makes the norm exist and be monotone — necessary; [5] compiled.  SURVIVED.
- **C-L2** (leaf, project): `SigmaOne` + `levelBounds_sigmaOne` — the fork's `sigma1Norm` /
  `levelBounds_sigma1Norm` (`5_KappaWeight.lean`, sorry-free) with `ρ` for `‖3‖`.  Source
  [Jac03, §2.1 p. 29]: > "In all cases of `(a b; c d)` that we will calculate with, `c ≡ 0 mod 9`
  and `d ≡ 1 mod 9`."  Attacks: [2] `ρ = 0`: the level is `{integral, c = 0, d = 1}`, bounds still
  hold ✓; [3] `ρ² ≤ ρ` needs `ρ ≤ 1` — supplied by `hρ`; [5] fork proof sorry-free.  SURVIVED.
- **C-L3** (leaf, mathlib): `mem_sigmaOne_iff_valued` — three applications of `norm_le_iff`
  (at `1`, `ϖ^2`, `ϖ`) with `map_pow`/`norm_pow`.  Source: as C-L1.  SURVIVED.
- **C-L4** (refactor): fork `sigma1Norm := SigmaOne K₃ ‖3‖ …`; delete `norm_le_of_valued_le`,
  `norm_eq_one_of_valued_eq_one` (`4_KappaColumn.lean:51,62`) in favour of mathlib; `Σ₁(3) ≤
  SigmaOne` via C-L3.

## R-D: compact open levels (forms-riesz T009)
- **D-L1** (leaf, mathlib): `Units.isCompact_of_isCompact` — `Units.isClosedEmbedding_embedProduct`
  (`Topology/Algebra/Group/Basic.lean:1422`) + `IsClosedEmbedding.isCompact_preimage`; the set is
  the preimage of `s ×ˢ (MulOpposite.op '' s)`.  Source [Buz07, §9 p. 68] ("compact open subgroup
  `U ⊆ D_f^×`").  Attacks: [2] `s = ∅` ⇒ empty ✓; [3] `T1Space` is the closed-embedding
  hypothesis; `ContinuousMul` for the embedding; [5] mathlib lemma verified by grep.  SURVIVED.
- **D-L2** (leaf, project): `isCompact_integralTensor` — `IsCompact.image` of
  `(integralAdeles)^n` (compact: `FiniteAdeleRing.isCompact_integralAdeles`,
  FLTstuff, sorry-free) under `a ↦ ∑ᵢ bᵢ ⊗ aᵢ`, continuous because `D ⊗ 𝔸_f` carries the module
  topology and the map is a finite sum of continuous maps.  Attacks: [3] `Module.Finite F D` is
  what gives the finite basis; the topology instance is a hypothesis (the concrete one comes from
  FLTstuff's module-topology instances) — flagged: the *continuity* of `a ↦ ∑ bᵢ ⊗ aᵢ` may need
  `IsModuleTopology`; if the instance search fails this becomes a sub-ticket.  SURVIVED with a
  recorded risk.
- **D-L3** (leaf, project — fork): `U0`, `U₁(9)` compact = D-L1 at D-L2's order (with
  `localOrder w` matched to the integral order), then `finite_image_doubleCoset_of_isOpen_of_isCompact`
  discharges the Hecke finiteness hypothesis.  Source [Buz07, §9 p. 69].

## Confidence gate
1 leaves discharged/cited ✓ (D-L2's continuity risk recorded) · 2 skeleton builds ✓ · 3 quotes ✓
· 4 attacks ✓ (B-L1's first draft was killed by attack 3 and corrected) · 5 B2 log clean ✓
· 6 mirrors the sources; commutativity deliberately *not* a leaf because Buzzard takes it as data ✓
· 7 single-conclusion ✓ (`exists_common_eigenvector` is a shared-witness existential — documented).
