# Ticket Board — `lwx-atkinlehner` (the H1 reduction)

**BOARD PATH: `.mathlib-quality/lwx-atkinlehner/`.**  The default `.mathlib-quality/` board belongs
to the completed NewtonPolygons project — NEVER touch it.  Every `/beastmode` run must name this
board path explicitly.

**Files owned by this board**: `PhD/TateFredholm/CharpolyPairing.lean`, `PhD/LWX/AtkinLehner.lean`.
Both are new.  Do not edit any other file.

**Build**: `lake build PhD.LWX.AtkinLehner` (whole chain).  The skeleton compiles today with sorry
warnings only.  Every ticket is "fill the sorry at the named declaration"; statements are
transcribed verbatim from the compiling skeleton and are **protected** — if a statement is wrong,
file a B2 in `b2_log.jsonl` rather than editing it.

**Read before working any ticket**: `.mathlib-quality/lwx-stepone/JL-AUDIT.md` (the
Jacquet–Langlands audit) and this board's `plan.md` and `decomposition.md`.  In particular: this
board **reduces** [LWX, Prop 3.22] rather than proving it.  The operator identity
`U_p ∘ U'_p = p^{k+1}` is a **hypothesis**, deliberately not ticketed, because no source stating it
in the quaternionic setting was found.  Do not attempt to prove it; do not weaken a statement to
avoid it.

## Summary

- Total: 29 tickets — 20 proof, 9 cleanup.
- Open: 0 | In Progress: 0 | Done: 30 (all).
- **BOARD COMPLETE 2026-09-06.**  Both files sorry-free; `lake build PhD.LWX.AtkinLehner` clean;
  `#print axioms` on all 15 public results shows exactly `[propext, Classical.choice, Quot.sound]`;
  `runLinter` reports **zero** errors in either of this board's files (the 25 it reports are all in
  pre-existing modules this board does not own: `TateFredholm.{Tate,Fredholm,Compact,Matrix,
  ModelSpace}` and `ForMathlib.Analysis.Normed.Ring.NegLogNorm`).
- One sub-ticket was spawned during execution: **A6a** (Tier A2, missing sub-lemma) for the
  roots-of-`reverse` gap in mathlib.  Depth 1.
- Parallel capacity: 5 workers at peak (A1/A2/A3/A4 and the whole W-chain are independent).
- **Milestone**: `[R2]` `LWX.roots_charpoly_atkinLehner`.

## Dependency order

```
CharpolyPairing.lean:  A1 A2 A3 [CLEANUP-1] A4 A5 A6 [CLEANUP-2]
AtkinLehner.lean:      W1 W2 W3 [CLEANUP-3] W4 W5 W6 [CLEANUP-4] W7 W8 W9 [CLEANUP-5]
                       W10 W11 R1 [CLEANUP-6] [CLEANUP-ALL-1] R2 R3 [CLEANUP-7]
                       [CLEANUP-FINAL]
```

---

## Group A — `PhD/TateFredholm/CharpolyPairing.lean`

### [A1·done] `Matrix.det_mul_det_of_mul_eq_smul`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:55
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem det_mul_det_of_mul_eq_smul (h : A * B = c • (1 : Matrix n n R)) :
    A.det * B.det = c ^ Fintype.card n := by
  sorry
```
(section variables: `{n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]`
`{A B : Matrix n n R} {c : R}`)

#### Proof sketch
1. **Take determinants of the hypothesis.** `rw [← Matrix.det_mul, h]` turns the goal into
   `(c • (1 : Matrix n n R)).det = c ^ Fintype.card n`.
2. **Evaluate the right-hand determinant.** `Matrix.det_smul` gives
   `(c • M).det = c ^ Fintype.card n * M.det`; with `M = 1`, `Matrix.det_one` finishes.
   Tactic: `simp [Matrix.det_smul]`.

#### Mathlib lemmas needed
- `Matrix.det_mul` — `Determinant/Basic.lean:138` (verified present).
- `Matrix.det_smul` — `Determinant/Basic.lean:272`, `det (c • A) = c ^ Fintype.card n * det A`
  (verified present, exact form checked).
- `Matrix.det_one`.

#### Sources
None — this is standard linear algebra used by the reduction, not a transcription of [LWX].
Its role is [LWX, Prop 3.22]'s determinant shadow, which is the only strength [LWX, Step I]
consumes (`lwx.txt:1815–1818`).

#### Generality decision
`CommRing R`: the proof uses no field, no invertibility, no `Nontrivial`.  Index type
`[Fintype n] [DecidableEq n]`, the minimum for `det`.  Universe-polymorphic.

---

### [A2·done] `Matrix.charpolyRev_conj`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:60
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem charpolyRev_conj (P Q M : Matrix n n R) (h : Q * P = 1) :
    (P * M * Q).charpolyRev = M.charpolyRev := by
  sorry
```

#### Proof sketch
1. **Apply Sylvester's identity** to move `Q` to the front:
   `rw [Matrix.charpolyRev_mul_comm (P * M) Q]`, giving `(Q * (P * M)).charpolyRev`.
2. **Reassociate and cancel.** `rw [← Matrix.mul_assoc, h, Matrix.one_mul]`.

#### Mathlib lemmas needed
- `Matrix.charpolyRev_mul_comm` — **project**, `PhD/TateFredholm/Charpoly.lean:47`, verified
  sorry-free: `(A * B).charpolyRev = (B * A).charpolyRev` for `A : Matrix n m R`, `B : Matrix m n R`.
- `Matrix.mul_assoc`, `Matrix.one_mul`.

#### Sources
None — standard linear algebra.

#### Generality decision
Only the one-sided hypothesis `Q * P = 1` is used, deliberately: for square matrices it implies the
other side, so callers prove strictly less.  `CommRing R` (required by `charpolyRev` itself).

---

### [A3·done] `Matrix.charpoly_conj`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:65
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem charpoly_conj (P Q M : Matrix n n R) (h : Q * P = 1) :
    (P * M * Q).charpoly = M.charpoly := by
  sorry
```

#### Proof sketch
1. **Upgrade the one-sided inverse to a unit.** `Matrix.mul_eq_one_comm` turns `h : Q * P = 1` into
   `P * Q = 1`; together these exhibit `P` as a unit, via `Matrix.nonsingInvUnit` or by building
   `⟨P, Q, hPQ, h⟩ : (Matrix n n R)ˣ` directly with `Units.mk`.
2. **Apply conjugation invariance.** `Matrix.charpoly_units_conj` states
   `(↑M' * N * ↑M'⁻¹).charpoly = N.charpoly` for a unit `M'`.  Match `M' := ⟨P, Q, _, _⟩` so that
   `↑M' = P` and `↑M'⁻¹ = Q`, then `exact`.

Bridging tactics that may be needed: `Units.inv_mk` / `Units.val_mk` to see `↑M'⁻¹` as `Q`; a
`show` to align the association `(P * M) * Q` with `P * (M * Q)`.

#### Mathlib lemmas needed
- `Matrix.mul_eq_one_comm` — one-sided inverses of square matrices are two-sided.
- `Matrix.charpoly_units_conj` — `Charpoly/Basic.lean:280` (verified present).
- `Units.mk`, `Matrix.mul_assoc`.

#### Sources
None — standard linear algebra.  A convenience wrapper is worth having because
`charpoly_units_conj` bundles into `(Matrix n n R)ˣ`, which is awkward at every call site here.

#### Generality decision
`CommRing R` and the one-sided hypothesis, as in A2.

---

### [CLEANUP-1·done] Run /cleanup on PhD/TateFredholm/CharpolyPairing.lean
- **Status**: done (2026-09-06; merged with CLEANUP-2, file complete) | **File**: PhD/TateFredholm/CharpolyPairing.lean
- **Depends on**: A3 | **Parallel**: no | **Type**: cleanup
- Per-file cadence rule (3 proof tickets on this file since the last cleanup).  Blocks A4–A6.

---

### [A4·done] `Matrix.C_det_mul_charpolyRev_eq`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:72
- **Depends on**: CLEANUP-1 | **Parallel**: yes (with A5 once A1 done) | **Type**: theorem
- **Note**: the largest leaf on this board.  If the algebra does not close in one proof, spawn
  sub-tickets (`Parent: A4`) rather than weakening the statement.

#### Statement
```lean
theorem C_det_mul_charpolyRev_eq (h : A * B = c • (1 : Matrix n n R)) :
    C A.det * B.charpolyRev
      = (-1) ^ Fintype.card n * A.charpoly.comp (C c * X) := by
  sorry
```

#### Proof sketch
1. **Unfold `charpolyRev`** to `det (1 - X • B.map C)` (`Matrix.charpolyRev` is a `def`; use
   `rw [Matrix.charpolyRev]`).
2. **Absorb `C A.det` into the determinant.** `C A.det = (A.map C).det` by
   `RingHom.map_det`; then `Matrix.det_mul` merges the two determinants into
   `det (A.map C * (1 - X • B.map C))`.
3. **Distribute and use the hypothesis.** `A.map C * (1 - X • B.map C) = A.map C - X • (A * B).map C`
   (needs `Matrix.map_mul`, `Matrix.mul_smul`, `Matrix.mul_sub`, `Matrix.mul_one`).  Rewriting with
   `h` and `Matrix.map_smul` gives `A.map C - (C c * X) • 1`.
4. **Recognise the characteristic polynomial.** `Matrix.charpoly` is `(charmatrix A).det` with
   `charmatrix A = X • 1 - A.map C`.  So
   `A.map C - (C c * X) • 1 = -((C c * X) • 1 - A.map C)`, and `Matrix.det_neg` produces the
   `(-1) ^ Fintype.card n` factor.
5. **Match the substitution.** `(C c * X) • 1 - A.map C` is `charmatrix A` with `X` replaced by
   `C c * X`; taking determinants, `Polynomial.comp` commutes with `det` because composition is a
   ring hom fixing constants (`Polynomial.compRingHom` / `RingHom.map_det` again).

Hand-verified at `n = 1` (`a - cX` both sides) and at `n = 2` for diagonal `A`, `B`
(`(a₁-cX)(a₂-cX)` both sides) — see `decomposition.md`, leaf A4.  A sign error would show at
`n = 1`; it does not.

#### Mathlib lemmas needed
- `Matrix.charpolyRev` — `Charpoly/Coeff.lean:292` (def, verified).
- `Matrix.charpoly`, `Matrix.charmatrix` — `Charpoly/Basic.lean:132,49` (verified).
- `RingHom.map_det`, `Matrix.det_mul`, `Matrix.det_neg`.
- `Matrix.map_mul`, `Matrix.map_smul`, `Matrix.mul_sub`, `Matrix.mul_one`, `Matrix.mul_smul`.
- `Polynomial.comp`, `Polynomial.C`, `Polynomial.X`.

#### Sources
None — this is the division-free form of "the spectra are exchanged by `x ↦ c/x`", which is the
content of [LWX, Prop 3.22] (`lwx.txt:1763–1768`) but not its proof.

#### Generality decision
`CommRing R`.  Deliberately stated without division so that no invertibility hypothesis is needed;
the field-level consequences are A5 and A6.

---

### [A5·done] `Matrix.det_ne_zero_of_mul_eq_smul`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:84
- **Depends on**: A1, CLEANUP-1 | **Parallel**: yes (with A4) | **Type**: theorem

#### Statement
```lean
theorem det_ne_zero_of_mul_eq_smul (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n K)) :
    A.det ≠ 0 := by
  sorry
```
(section variables: `{K : Type*} [Field K] {A B : Matrix n n K} {c : K}`)

#### Proof sketch
1. **Get the determinant product** from A1: `A.det * B.det = c ^ Fintype.card n`.
2. **The right side is nonzero**: `pow_ne_zero _ hc`.
3. **Conclude**: if `A.det = 0` the left side is `0`; `mul_ne_zero_iff` or `intro` + `simp` closes it.

#### Mathlib lemmas needed
- `Matrix.det_mul_det_of_mul_eq_smul` — A1, this file.
- `pow_ne_zero`, `mul_ne_zero_iff`.

#### Sources
None.

#### Generality decision
`Field K` is genuinely needed: over a general `CommRing`, `A.det` could be a zero-divisor and the
argument fails.  `c ≠ 0` is needed: at `c = 0`, `A = 0` is a counterexample for `card n ≥ 1`.

---

### [A6·done] `Matrix.roots_charpoly_of_mul_eq_smul`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean:93
- **Depends on**: A4, A5, A6a | **Parallel**: no | **Type**: theorem
- **Note**: classified in `decomposition.md` as an internal node, not a true leaf (its discharge
  needs more than three lemmas).  Sub-tickets (`Parent: A6`) are expected and fine.

#### Statement
```lean
theorem roots_charpoly_of_mul_eq_smul (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n K)) :
    B.charpoly.roots = A.charpoly.roots.map (fun x => c / x) := by
  sorry
```
(section variables add `[IsAlgClosed K]`)

#### Proof sketch
1. **Both polynomials split with full multiplicity.** Over `IsAlgClosed K`, `charpoly` is monic
   (`Matrix.charpoly_monic`) of degree `Fintype.card n`
   (`Matrix.charpoly_natDegree_eq_dim`), so `roots` has that cardinality
   (`Polynomial.splits_iff_card_roots`, `Polynomial.roots_count_eq_degree`).
2. **`0` is not a root of `A.charpoly`.** By A5, `A.det ≠ 0`; `Matrix.det_eq_prod_roots_charpoly`
   (`Charpoly/Eigs.lean:98`) expresses `det` as the product of roots, so no root is `0`.  This is
   what makes `fun x => c / x` well defined on the root multiset — record it as an explicit `have`.
3. **Transport the factorisation.** Rewrite `A.charpoly` as `∏ (X - C λ)` over its roots
   (`Polynomial.eq_prod_roots_of_monic_of_splits_id`), substitute into the identity of A4, and read
   off that `B.charpoly` factors as `∏ (X - C (c / λ))`.
4. **Conclude on multisets.** Two monic split polynomials with equal factorisations have equal root
   multisets; `Polynomial.roots_multiset_prod_X_sub_C` gives the roots of the right-hand product
   directly as the mapped multiset.

#### Mathlib lemmas needed
- `Matrix.charpoly_monic` — `Charpoly/Coeff.lean:120` (verified).
- `Matrix.charpoly_natDegree_eq_dim` — `Charpoly/Coeff.lean:116` (verified).
- `Matrix.det_eq_prod_roots_charpoly` — `Charpoly/Eigs.lean:98` (verified).
- `Polynomial.eq_prod_roots_of_monic_of_splits_id`, `Polynomial.roots_multiset_prod_X_sub_C`,
  `Polynomial.splits_iff_card_roots` (`Splits.lean:373`, verified).
- `IsAlgClosed.splits_codomain`.
- A4, A5 (this file).

#### Sources
[LWX, Prop 3.22], `lwx.txt:1763–1768` — this is that statement's content at the level of matrices,
in multiset form.  See `decomposition.md` for the formulation decision and the verbatim quote.

#### Generality decision
`IsAlgClosed K` is load-bearing: without it `roots` undercounts and the two multisets can have
different cardinalities.  `c ≠ 0` as in A5.

---

### [A6a·done] `Matrix.reverse_multiset_prod` and `Matrix.roots_charpolyRev`
- **Status**: done | **File**: PhD/TateFredholm/CharpolyPairing.lean
- **Depends on**: A5 | **Parent**: A6 | **Parallel**: no | **Type**: theorem
- **Spawned** 2026-09-06 (beastmode, Tier A2 MISSING SUB-LEMMA).

#### Why this was spawned
A6 needs to relate `charpolyRev` roots to `charpoly` roots.  Five-method-equivalent search of
mathlib found **no roots-of-reverse lemma**: `Mathlib/Algebra/Polynomial/Reverse.lean` has
`reverse_mul_of_domain`, `coeff_reverse`, `reverse_natDegree` and friends but nothing about
`roots`, and `grep rootMultiplicity.*reverse` over all of mathlib returns nothing.  The only four
`charpolyRev` lemmas in mathlib (`Charpoly/Coeff.lean:292,329,336,343`) are the definition,
`eval_charpolyRev`, `coeff_charpolyRev_eq_neg_trace` and `isUnit_charpolyRev_of_isNilpotent` —
none about roots.  It was also checked that the gap is unavoidable: applying the A4 functional
equation with the roles of `A` and `B` swapped still leaves `charpolyRev` on one side, so no
combination of A4 with `roots_comp_C_mul_X_add_C` eliminates it.

#### Statement
```lean
private theorem reverse_multiset_prod {R : Type*} [CommRing R] [NoZeroDivisors R]
    (s : Multiset R[X]) : s.prod.reverse = (s.map Polynomial.reverse).prod

theorem roots_charpolyRev (hA : A.det ≠ 0) :
    A.charpolyRev.roots = A.charpoly.roots.map (fun x => x⁻¹)
```

#### Proof sketch
1. `reverse_multiset_prod` by `Multiset.induction_on`, using `Polynomial.reverse_mul_of_domain`.
2. `A.charpoly` is monic and splits over an algebraically closed field, so
   `A.charpoly = (A.charpoly.roots.map fun a => X - C a).prod`
   (`Polynomial.eq_prod_roots_of_monic_of_splits_id`).
3. No root is `0`: `Matrix.det_eq_prod_roots_charpoly` gives `A.det = roots.prod`, so a zero root
   would force `A.det = 0`, contradicting `hA`.
4. `reverse (X - C a) = 1 - C a * X` (from `coeff_reverse`; `revAt 1` swaps the two coefficients),
   and for `a ≠ 0` that is `C (-a) * (X - C a⁻¹)`, whose roots are `{a⁻¹}`.
5. Assemble with `reverse_charpoly`, step 1, and `Polynomial.roots_multiset_prod`
   (`Roots.lean:272`, needs `0 ∉ s`).

#### Mathlib lemmas needed
- `Polynomial.reverse_mul_of_domain` (`Reverse.lean:277`), `Polynomial.coeff_reverse`
  (`Reverse.lean:221`), `Matrix.reverse_charpoly` (`Charpoly/Coeff.lean:294`).
- `Polynomial.eq_prod_roots_of_monic_of_splits_id`, `Polynomial.roots_multiset_prod`
  (`Roots.lean:272`), `Polynomial.roots_multiset_prod_X_sub_C` (`Roots.lean:308`).
- `Matrix.det_eq_prod_roots_charpoly` (`Charpoly/Eigs.lean:98`), `Matrix.charpoly_monic`.

#### Sources
None — standard polynomial algebra; the gap is in mathlib, not in [LWX].

#### Generality decision
`reverse_multiset_prod` over any `CommRing` with `NoZeroDivisors` (what `reverse_mul_of_domain`
needs), `private` because it is pure plumbing.  `roots_charpolyRev` inherits `Field` +
`IsAlgClosed` from A6's section, which is where `roots` has full multiplicity.

---

### [CLEANUP-2·done] Run /cleanup on PhD/TateFredholm/CharpolyPairing.lean (final per-file)
- **Status**: done (2026-09-06; runLinter clean, all proofs < 30 lines, axioms standard) | **File**: PhD/TateFredholm/CharpolyPairing.lean
- **Depends on**: A6 | **Parallel**: no | **Type**: cleanup
- Final per-file cleanup.  This file is a plausible mathlib contribution; hold it to that standard.

---

## Group W — `PhD/LWX/AtkinLehner.lean`, the Atkin–Lehner element

All eight matrix statements were hand-verified at planning time.  The computations are written out
in `decomposition.md` (leaves W1–W11) because [LWX] never performs them, so there is no source
passage to quote.  If a computation disagrees with the decomposition, file a B2.

### [W1·done] `LWX.pow_ne_zero_padic`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:72
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem pow_ne_zero_padic (m : ℕ) : ((p : ℚ_[p]) ^ m) ≠ 0 := by
  sorry
```
(section variables: `{p : ℕ} [hp : Fact p.Prime] {m : ℕ}`)

#### Proof sketch
1. **Reduce to the base.** `pow_ne_zero m` reduces the goal to `(p : ℚ_[p]) ≠ 0`.
2. **Cast.** `Nat.cast_ne_zero.mpr hp.out.pos.ne'` — `ℚ_[p]` has characteristic zero, so the cast of
   a positive natural is nonzero.  Tactic: `simp [hp.out.pos.ne']` or `exact_mod_cast`.

#### Mathlib lemmas needed
- `pow_ne_zero`, `Nat.cast_ne_zero`, `Nat.Prime.pos`.

#### Sources
None.

#### Generality decision
Stated with the ambient `Fact p.Prime` of every LWX file, although `p ≠ 0` would suffice; matching
the file convention avoids a second hypothesis style in one namespace.

---

### [W2·done] `LWX.det_atkinLehner`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:77
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
@[simp]
theorem det_atkinLehner : (atkinLehner p m).det = (p : ℚ_[p]) ^ m := by
  sorry
```

#### Proof sketch
1. **Unfold and use the 2×2 determinant.** `simp [atkinLehner, Matrix.det_fin_two_of]` reduces to
   `0 * 0 - 1 * (-(p ^ m)) = p ^ m`.
2. **Close by `ring`.**

Hand check: `det (0, 1; −P, 0) = 0·0 − 1·(−P) = P`.  The minus sign sits in the lower-left entry.

#### Mathlib lemmas needed
- `Matrix.det_fin_two_of`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`.

#### Sources
None.  The element is [LWX]'s Atkin–Lehner element at level `p^m`; the determinant is our own
computation.

#### Generality decision
No hypotheses; holds at every `m` including `m = 0`, where `det = 1`.

---

### [W3·done] `LWX.atkinLehner_mul_atkinLehnerConj`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:82
- **Depends on**: W1 | **Parallel**: yes | **Type**: theorem
- **This is the defining identity of the board.**  Everything else about conjugation rests on it.

#### Statement
```lean
theorem atkinLehner_mul_atkinLehnerConj (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehner p m * atkinLehnerConj p m γ = γ * atkinLehner p m := by
  sorry
```

#### Proof sketch
1. **Reduce to entries.** `ext i j` then `fin_cases i <;> fin_cases j`.
2. **Unfold both matrices and multiply out.**
   `simp [atkinLehner, atkinLehnerConj, Matrix.mul_apply, Fin.sum_univ_two]`.
3. **Clear the division.** The `(1,0)` entry needs `−P · (−c/P) = c`, which is where `P ≠ 0` enters:
   `field_simp [pow_ne_zero_padic (p := p) m]` then `ring`.

Hand verification (`P := p^m`), from `decomposition.md` leaf W3:
`w · conj γ` row 1 `= (−bP, a)`, row 2 `= (−Pd, c)`; `γ · w` row 1 `= (−bP, a)`, row 2 `= (−Pd, c)`.

#### Mathlib lemmas needed
- `Matrix.mul_apply`, `Fin.sum_univ_two`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`,
  `Matrix.ext_iff`.
- `W1` (`LWX.pow_ne_zero_padic`) for `field_simp`.

#### Sources
None — [LWX] never writes this identity.  Its role: it is the inverse-free form of `conj γ = w⁻¹ γ w`,
so that no matrix inverse appears anywhere in this development.

#### Generality decision
Stated for **every** matrix `γ`, with no integrality or invertibility hypothesis, because the
identity is formal.  Checked at planning time that integrality is not needed.

---

### [CLEANUP-3·done] Run /cleanup on PhD/LWX/AtkinLehner.lean
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean
- **Depends on**: W3 | **Parallel**: no | **Type**: cleanup
- Per-file cadence.  Blocks W4 onwards.

---

### [W4·done] `LWX.det_atkinLehnerConj`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:88
- **Depends on**: W1, CLEANUP-3 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
@[simp]
theorem det_atkinLehnerConj (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    (atkinLehnerConj p m γ).det = γ.det := by
  sorry
```

#### Proof sketch
1. **Unfold both determinants** with `Matrix.det_fin_two_of` and `Matrix.det_fin_two`.
2. **Cancel the level.** The goal becomes `d·a − (−c/P)(−bP) = a·d − b·c`; `field_simp` with W1
   clears `P`, then `ring`.

Hand check: `det (d, −c/P; −bP, a) = da − (c/P)(bP) = da − cb = det γ`.

#### Mathlib lemmas needed
- `Matrix.det_fin_two`, `Matrix.det_fin_two_of`, `W1`.

#### Sources
None.

#### Generality decision
No hypotheses on `γ`; `P ≠ 0` comes from W1, not from the caller.

---

### [W5·done] `LWX.atkinLehnerConj_apply_zero_zero`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:96
- **Depends on**: CLEANUP-3 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
@[simp]
theorem atkinLehnerConj_apply_zero_zero (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehnerConj p m γ 0 0 = γ 1 1 := by
  sorry
```

#### Proof sketch
Definitional after unfolding: `simp [atkinLehnerConj]`.  If `simp` does not reduce the
`Matrix.of ![![...]]` application, add `Matrix.cons_val_zero`, `Matrix.cons_val'`, `Matrix.of_apply`.

#### Mathlib lemmas needed
- `Matrix.of_apply`, `Matrix.cons_val_zero`, `Matrix.cons_val'`.

#### Sources
None.  Together with W6 this is the matrix-level content of "conjugation by `w` inverts the
nebentypus" ([LWX, Prop 3.22]'s proof twists by a central character, `lwx.txt:1783–1786`).

#### Generality decision
`@[simp]` because downstream nebentypus bookkeeping rewrites with it constantly.  No hypotheses.

---

### [W6·done] `LWX.atkinLehnerConj_apply_one_one`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:103
- **Depends on**: CLEANUP-3 | **Parallel**: yes (with W5) | **Type**: theorem

#### Statement
```lean
@[simp]
theorem atkinLehnerConj_apply_one_one (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehnerConj p m γ 1 1 = γ 0 0 := by
  sorry
```

#### Proof sketch
As W5: `simp [atkinLehnerConj]`, with `Matrix.cons_val_one`, `Matrix.head_cons` if needed.

#### Mathlib lemmas needed
- `Matrix.of_apply`, `Matrix.cons_val_one`, `Matrix.head_cons`.

#### Sources
None.  This is **the diagonal swap** — the reason the nebentypus inverts.

#### Generality decision
As W5.

---

### [CLEANUP-4·done] Run /cleanup on PhD/LWX/AtkinLehner.lean
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean
- **Depends on**: W6 | **Parallel**: no | **Type**: cleanup
- Per-file cadence (W4, W5, W6 since CLEANUP-3).

---

### [W7·done] `LWX.mul_diagonal_eq_det_add`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:109
- **Depends on**: CLEANUP-4 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem mul_diagonal_eq_det_add (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    γ 0 0 * γ 1 1 = γ.det + γ 0 1 * γ 1 0 := by
  sorry
```

#### Proof sketch
1. `rw [Matrix.det_fin_two]` turns the goal into `a * d = (a * d - b * c) + b * c`.
2. `ring`.

#### Mathlib lemmas needed
- `Matrix.det_fin_two`.

#### Sources
None.  This is the **exact** form of "the two diagonal characters multiply to the central one":
since `p^m ∣ c` on the Iwahori, reducing modulo `p^m` gives `a·d ≡ det`.  The congruence is left to
the consumer so that no `ZMod` machinery enters this board.

#### Generality decision
Stated as an exact identity rather than a congruence, deliberately — see Sources.  No hypotheses.

---

### [W8·done] `LWX.atkinLehnerConj_upElt`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:125
- **Depends on**: CLEANUP-4 | **Parallel**: yes | **Type**: theorem
- **This is the statement that `w` carries `U_p` to `U'_p`.**

#### Statement
```lean
theorem atkinLehnerConj_upElt : atkinLehnerConj p m (upElt p) = upEltAdj p := by
  sorry
```

#### Proof sketch
1. **Reduce to entries**: `ext i j`, `fin_cases i <;> fin_cases j`.
2. **Unfold**: `simp [atkinLehnerConj, upElt, upEltAdj]`.  With `a = 1, b = 0, c = 0, d = p`, the
   formula `(d, −c/p^m; −b·p^m, a)` gives `(p, 0; 0, 1)` directly.
3. The `(0,1)` entry is `−0 / p^m = 0`, which holds in Lean **without** `p^m ≠ 0` since `0 / x = 0`;
   so this ticket does not need W1.

#### Mathlib lemmas needed
- `Matrix.of_apply`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons`,
  `zero_div`, `neg_zero`.

#### Sources
None as an identity.  Its role is [LWX, Prop 3.22]'s pairing of `U_p` on the `ψ`-space with `U_p` on
the `ψ⁻¹`-space (`lwx.txt:1786–1789`).

#### Generality decision
Holds at every `m`, and the answer does not depend on `m` at all — the conjugate of a diagonal
matrix is level-independent, which is why `U_p ↦ U'_p` at every level.  No hypotheses.

---

### [W9·done] `LWX.Iw` (the Iwahori subgroup) and `LWX.mem_Iw_iff`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:132
- **Depends on**: CLEANUP-4 | **Parallel**: yes | **Type**: def + API
- Two sorries (`mul_mem'`, `one_mem'`) in one definition; `mem_Iw_iff` is already `Iff.rfl`.

#### Statement
```lean
def Iw (m : ℕ) : Submonoid (Matrix (Fin 2) (Fin 2) ℚ_[p]) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ m ∧ ‖g.det‖ = 1}
  mul_mem' := by sorry
  one_mem' := by sorry
```

#### Proof sketch
`mul_mem'`: crib the existing proof of `LWX.Mh` (`PhD/LWX/HaloWeightH.lean:54`), which establishes
exactly the first two conditions for the same carrier shape.
1. **Entrywise bound**: `Matrix.mul_apply` + `Fin.sum_univ_two`, then the ultrametric bound
   `IsUltrametricDist.norm_add_le_max` and `norm_mul_le` on each summand.
2. **Lower-left bound**: the `(1,0)` entry of a product is `g₁₀k₀₀ + g₁₁k₁₀`; each summand is
   bounded by `(p:ℝ)⁻¹ ^ m` using the respective hypotheses.
3. **Determinant**: `Matrix.det_mul` and `norm_mul` give `‖det (g*k)‖ = ‖det g‖ * ‖det k‖ = 1`.
   This replaces `Mh`'s `‖g 1 1‖ = 1` clause and is where the two definitions differ.

`one_mem'`: `simp [Matrix.one_apply]`; the entries are `0` or `1`, the `(1,0)` entry is `0`, and
`det 1 = 1`.

#### Mathlib lemmas needed
- `Matrix.mul_apply`, `Fin.sum_univ_two`, `Matrix.det_mul`, `Matrix.one_apply`, `Matrix.det_one`.
- `IsUltrametricDist.norm_add_le_max`, `norm_mul_le`, `norm_mul`.

#### Sources
[LWX] uses `Iw_{p^m}` throughout §3 (e.g. `lwx.txt:1763–1768`) without giving a formal definition;
this is the standard Iwahori subgroup of level `p^m`.

#### Generality decision
A **new** definition rather than reuse of `LWX.Mh`: `Mh` requires only `‖g 1 1‖ = 1`, but
conjugation by `w` swaps `a` and `d`, so the conjugate needs `‖g 0 0‖ = 1` too.  Asking for
`‖det‖ = 1` supplies both (see W10).  Recorded so nobody "simplifies" `Iw` back to `Mh`.

---

### [CLEANUP-5·done] Run /cleanup on PhD/LWX/AtkinLehner.lean
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean
- **Depends on**: W9 | **Parallel**: no | **Type**: cleanup
- Per-file cadence (W7, W8, W9 since CLEANUP-4).

---

### [W10·done] `LWX.norm_apply_zero_zero_of_mem_Iw`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:142
- **Depends on**: W7, W9, CLEANUP-5 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem norm_apply_zero_zero_of_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hm : m ≠ 0)
    (hg : g ∈ Iw p m) : ‖g 0 0‖ = 1 := by
  sorry
```

#### Proof sketch
1. **Bound the off-diagonal product.** From `hg`, `‖g 0 1‖ ≤ 1` and `‖g 1 0‖ ≤ (p:ℝ)⁻¹ ^ m`, so
   `‖g 0 1 * g 1 0‖ ≤ (p:ℝ)⁻¹ ^ m < 1` — strictness needs `hm : m ≠ 0`.
2. **Ultrametric equality case.** By W7, `g 0 0 * g 1 1 = g.det + g 0 1 * g 1 0`.  Since
   `‖g.det‖ = 1` and the second summand has norm `< 1`, the ultrametric equality case gives
   `‖g 0 0 * g 1 1‖ = 1`.
3. **Both factors are units.** `norm_mul` gives `‖g 0 0‖ * ‖g 1 1‖ = 1` with both factors `≤ 1`;
   hence both equal `1`.  Close with `le_antisymm` and `nlinarith` or an explicit argument.

#### Mathlib lemmas needed
- `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (or the `norm_add_eq_of_norm_lt` variant),
  `norm_mul`, `norm_mul_le`.
- `W7` (`LWX.mul_diagonal_eq_det_add`), `mem_Iw_iff`.
- `pow_lt_one₀`, `inv_lt_one_of_one_lt₀`.

#### Sources
None.  This is the standard fact that both diagonal entries of an Iwahori element are units.

#### Generality decision
`hm : m ≠ 0` is **necessary, not over-specified**: at `m = 0` the matrix `(0,1;1,0)` lies in `Iw p 0`
with unit determinant but has `‖g 0 0‖ = 0`.  The adversarial pass ran this counterexample
explicitly; see `decomposition.md` leaf W10.

---

### [W11·done] `LWX.atkinLehnerConj_mem_Iw`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:148
- **Depends on**: W4, W9, CLEANUP-5 | **Parallel**: yes | **Type**: theorem
- **This is the normalisation statement: `w` normalises `Iw_{p^m}`.**

#### Statement
```lean
theorem atkinLehnerConj_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (hg : g ∈ Iw p m) : atkinLehnerConj p m g ∈ Iw p m := by
  sorry
```

#### Proof sketch
Unfold with `mem_Iw_iff` and check the three clauses on `conj g = (d, −c/p^m; −b·p^m, a)`.
1. **Entrywise `≤ 1`.** `d` and `a` directly from `hg`.  For `−c/p^m`: `norm_div` and
   `‖(p:ℚ_[p])^m‖ = (p:ℝ)⁻¹ ^ m` give `‖c/p^m‖ = ‖c‖ · (p:ℝ)^m ≤ 1` from `‖c‖ ≤ (p:ℝ)⁻¹ ^ m`.
   For `−b·p^m`: `norm_mul` gives `‖b‖ · (p:ℝ)⁻¹ ^ m ≤ 1`.
2. **Lower-left bound.** The `(1,0)` entry is `−b·p^m` with norm `‖b‖ · (p:ℝ)⁻¹ ^ m ≤ (p:ℝ)⁻¹ ^ m`.
3. **Determinant.** `W4` gives `det (conj g) = det g`, so `‖det‖ = 1` transfers unchanged.

Norm of the uniformiser power: use the project's existing `padicNormE` / `Padic.norm_p_pow` lemma
(`‖(p : ℚ_[p]) ^ m‖ = (p : ℝ)⁻¹ ^ m`); if the exact name differs, `Padic.norm_p` plus `norm_pow`.

#### Mathlib lemmas needed
- `norm_div`, `norm_mul`, `norm_neg`, `norm_pow`, `Padic.norm_p`.
- `W4` (`LWX.det_atkinLehnerConj`), `mem_Iw_iff`.

#### Sources
None.  [LWX] uses the normalisation implicitly when it twists between `ψ` and `ψ⁻¹`
(`lwx.txt:1783–1786`).

#### Generality decision
**No `m ≠ 0` hypothesis.**  The draft carried one, copied from W10; the adversarial pass re-derived
all four entry bounds and found none of them uses it, so it was removed and the statement
re-elaborated.  The statement holds at `m = 0` too.  See `decomposition.md` leaf W11.

---

### [R1·done] `LWX.det_mul_det_atkinLehner`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:167
- **Depends on**: A1, CLEANUP-5 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem det_mul_det_atkinLehner {A B A' P Q : Matrix ι ι R} {c : R}
    (hAB : A * B = c • (1 : Matrix ι ι R)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A.det * A'.det = c ^ Fintype.card ι := by
  sorry
```
(section variables: `{ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]`)

#### Proof sketch
1. **Compute `det A'`.** `subst hA'`, then `Matrix.det_mul` twice gives
   `det A' = det P * det B * det Q`.
2. **Kill the conjugating factors.** From `hQP`, `det Q * det P = 1` (apply `Matrix.det_mul` and
   `Matrix.det_one`).  Commutativity of `R` then reduces `det A'` to `det B`.
3. **Apply A1.** `exact det_mul_det_of_mul_eq_smul hAB`.

#### Mathlib lemmas needed
- `Matrix.det_mul`, `Matrix.det_one`, `mul_comm`, `mul_assoc`.
- `Matrix.det_mul_det_of_mul_eq_smul` — A1.

#### Sources
[LWX, Step I] consumes exactly this strength: "the sum of all `U_p`-slopes on
`S^D_{k+2}(K^pIw_{q²};ψ) ⊕ S^D_{k+2}(K^pIw_{q²};ψ⁻¹)` is `(k+1)²qt`" (`lwx.txt:1815–1818`).  With
`c = p^{k+1}` and valuations, this determinant identity is that slope sum.

#### Generality decision
`CommRing R` — no field, no algebraic closure, no invertibility.  The draft placed this in the
`[Field K] [IsAlgClosed K]` section; the adversarial pass found the proof uses neither and it was
moved to its own `CommRing` section.

---

### [CLEANUP-6·done] Run /cleanup on PhD/LWX/AtkinLehner.lean
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean
- **Depends on**: R1 | **Parallel**: no | **Type**: cleanup
- Per-file cadence (W10, W11, R1 since CLEANUP-5).

---

### [CLEANUP-ALL-1·done] Run /cleanup-all on the project so far
- **Status**: done | **File**: (project-wide)
- **Depends on**: CLEANUP-2, CLEANUP-6 | **Parallel**: no | **Type**: cleanup
- Pre-milestone project-wide cleanup.  Blocks the milestone R2.

---

### [R2·done] `LWX.roots_charpoly_atkinLehner` — **MILESTONE**
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:182
- **Depends on**: A3, A6, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem
- **The board's goal**: [LWX, Prop 3.22] granted the operator identity.

#### Statement
```lean
theorem roots_charpoly_atkinLehner {A B A' P Q : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • (1 : Matrix ι ι K)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x) := by
  sorry
```
(section variables: `{ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [IsAlgClosed K]`)

#### Proof sketch
1. **Transport along the conjugation.** `subst hA'`; by A3 (`Matrix.charpoly_conj`) with `hQP`,
   `(P * B * Q).charpoly = B.charpoly`, so the goal becomes a statement about `B`.
2. **Apply the root pairing.** `exact roots_charpoly_of_mul_eq_smul hc hAB` (A6).

That is the whole proof: the board's design puts all the work in A3 and A6.

#### Mathlib lemmas needed
- `Matrix.charpoly_conj` — A3, `CharpolyPairing.lean`.
- `Matrix.roots_charpoly_of_mul_eq_smul` — A6, `CharpolyPairing.lean`.

#### Sources
[LWX, Prop 3.22], `lwx.txt:1763–1768`, quoted verbatim in `decomposition.md`.  **The source proves
it by Jacquet–Langlands** (`lwx.txt:1775`); we do not.  `hAB` is the hypothesis that replaces that
route — see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.

#### Generality decision
Root multisets rather than [LWX]'s sorted indexing: equivalent, needs no sorting, and serves both
consumers directly (`Multiset.sum` for Step I's slope total, `Multiset.count` for Step III's
multiplicities).  `IsAlgClosed` is load-bearing; `c ≠ 0` is load-bearing.

---

### [R3·done] `LWX.norm_roots_charpoly_atkinLehner`
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean:198
- **Depends on**: R2 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_roots_charpoly_atkinLehner {A B A' P Q : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • (1 : Matrix ι ι K)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖) := by
  sorry
```
(section variables: `{ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [NormedField K]`
`[IsAlgClosed K]`)

#### Proof sketch
1. **Rewrite with R2**: `rw [roots_charpoly_atkinLehner hc hAB hQP hA']`.
2. **Compose the maps**: `Multiset.map_map` turns the left side into
   `A.charpoly.roots.map (fun x => ‖c / x‖)`.
3. **Distribute the norm**: `simp [norm_div]` — `‖c / x‖ = ‖c‖ / ‖x‖` in a normed field.

#### Mathlib lemmas needed
- `Multiset.map_map`, `norm_div`.
- `R2` (`LWX.roots_charpoly_atkinLehner`).

#### Sources
[LWX, Prop 3.22] in slope form: applying `-log` to this identity gives
`α(ψ⁻¹) = v(c) − α(ψ)` with `c = p^{k+1}`, i.e. `α_i(ψ) = k + 1 − α_{n−1−i}(ψ⁻¹)`.

#### Generality decision
Kept in `AtkinLehner.lean` rather than `CharpolyPairing.lean` so that the algebraic file stays free
of analysis imports — recorded in both module docstrings.  `NormedField` is the minimal class
carrying `‖·‖` with `norm_div`.

---

### [CLEANUP-7·done] Run /cleanup on PhD/LWX/AtkinLehner.lean (final per-file)
- **Status**: done | **File**: PhD/LWX/AtkinLehner.lean
- **Depends on**: R3 | **Parallel**: no | **Type**: cleanup

---

### [CLEANUP-FINAL·done] Run /cleanup-all on the whole board
- **Status**: done | **File**: (project-wide)
- **Depends on**: every other ticket | **Parallel**: no | **Type**: cleanup
- After this, run `/pre-submit`.  Check `#print axioms LWX.roots_charpoly_atkinLehner` shows exactly
  `[propext, Classical.choice, Quot.sound]`.

---

## Cleanup-cadence verification

20 proof tickets.  Cadence requires at least `⌈20/3⌉ = 7` per-file cleanups plus one final per file.

| File | Proof tickets | Cadence cleanups | Final | Total |
|---|---|---|---|---|
| CharpolyPairing.lean | 6 | CLEANUP-1 (after A3) | CLEANUP-2 | 2 |
| AtkinLehner.lean | 14 | CLEANUP-3, -4, -5, -6 (after W3, W6, W9, R1) | CLEANUP-7 | 5 |
| project-wide | — | CLEANUP-ALL-1 (pre-milestone) | CLEANUP-FINAL | 2 |

Total 9 cleanup tickets — meets the rule.
