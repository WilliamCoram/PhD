# Decomposition — `lwx-atkinlehner` (the H1 reduction)

**BOARD PATH: `.mathlib-quality/lwx-atkinlehner/`.**  Never touch the default `.mathlib-quality/`
board (NewtonPolygons) or any other board's files.

## Skeleton location

- `PhD/TateFredholm/CharpolyPairing.lean` (99 lines, 6 sorries) — the algebraic half.
- `PhD/LWX/AtkinLehner.lean` (205 lines, 15 sorries) — the `p`-adic half plus the reduction.

`lake build PhD.LWX.AtkinLehner` passes with **sorry warnings only, no errors** — verified
2026-09-06.  Both files are new; neither collides with any other board.

---

## Standing note: this decomposition deliberately DEPARTS from the source's proof

The `/develop` source-faithfulness rule says transcribe, don't invent.  Here the source's own proof
is unavailable to us by explicit user constraint, so the **source-gap fallback chain** applies and
is recorded honestly rather than papered over.

[LWX, Prop 3.22]'s proof, `lwx.txt:1773–1789`:

> "Firstly note that the base change of S^D_{k+2}(K^pIw_{pᵐ};ψ) to ℂ is isomorphic to the
> corresponding classical space of automorphic forms for D.  Since ψ has conductor pᵐ while the
> level structure at p is Iw_{pᵐ}, by **applying Jacquet–Langlands** and [LW12, Proposition 2.8],
> we see that for every automorphic representation π appearing in S^D_{k+2}(K^pIw_{pᵐ};ψ), its
> p-component π_p is a principal series of GL₂(ℚ_p) whose corresponding two characters of ℚ_p^×
> are unr(α) and unr(α⁻¹)⊗ω_p … In conclusion, one can pair the U_p-eigenvalues of
> S^D_{k+2}(K^pIw_{pᵐ};ψ) and the U_p-eigenvalues of S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹) so that they
> multiply to p^{k+1}."

Jacquet–Langlands is ruled out for this development (see `../lwx-stepone/JL-AUDIT.md`).  Fallback
chain applied:

1. **Cross-reference within the project's references.** Buzzard 2004 and 2007, Johansson–Newton,
   Bellaïche, Loeffler, Pollack, Dembélé — none proves the slope symmetry without
   Jacquet–Langlands.  Dembélé's "perfect pairing" (`../lwx-stepone/references/dembele.txt:990`) is
   the weight-2 forms ↔ `Div(X)` duality giving transposes of Brandt matrices: Hecke adjointness,
   not the Atkin–Lehner relation.
2. **Wider search.** The classical statement is Miyake Thm 4.6.17 / Atkin–Li; the natural local
   reference is Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973).  Neither
   is to hand, and neither is quaternionic.
3. **Consequence.** The **operator identity is NOT ticketed.** It is carried as an explicit
   hypothesis `A * B = c • 1` in every downstream statement, and is the intended `/expert-review`
   question.  Everything that can be proved without it is ticketed.

What this board delivers is therefore a **reduction**, not a proof of Prop 3.22: it discharges
every step of the argument except the one identity, so that a later source find or reviewer answer
converts directly into the theorem.

### Where the substrate comes from instead

For the elementary matrix leaves there is no source passage to quote, because [LWX] never performs
these computations.  Per the fallback chain's "expand it yourself", each was **verified by hand
during planning** and the verification is recorded in the leaf's entry.  A leaf whose hand
verification is not written out below is a defect.

---

## Result R: [LWX, Prop 3.22] granted the operator identity

Statement being reduced, verbatim, `lwx.txt:1763–1768`:

> "Proposition 3.22 (Atkin–Lehner). We use α₀(ψ),…,α_{(k+1)q⁻¹pᵐt−1}(ψ) to denote the slopes of
> U_p acting on S^D_{k+2}(K^pIw_{pᵐ},ψ) in non-decreasing order.  Then we have
> α_i(ψ) = k + 1 − α_{(k+1)q⁻¹pᵐt−1−i}(ψ⁻¹)."

### Plain-English proof of the reduction

Let `w = (0, 1; −p^m, 0)`.  Three facts make `w` an Atkin–Lehner element at level `p^m`.  It
normalises the Iwahori subgroup `Iw_{p^m}`, so conjugation by it carries forms of level `Iw_{p^m}`
to forms of the same level.  It exchanges the two diagonal entries of an Iwahori matrix, so it
carries nebentypus `ψ` to `ψ⁻¹`.  And it conjugates `diag(1,p)` to `diag(p,1)`, so it carries `U_p`
to `U'_p`.  Consequently the matrix `A'` of `U_p` on the `ψ⁻¹`-space is conjugate to the matrix `B`
of `U'_p` on the `ψ`-space.

Now suppose `A · B = c · 1` with `c = p^{k+1}`, where `A` is the matrix of `U_p` on the `ψ`-space.
Then `A` is invertible and `B = c A⁻¹`, so the eigenvalues of `B` are `c/λ` as `λ` runs over the
eigenvalues of `A` with multiplicity.  Conjugation does not change characteristic polynomials, so
the eigenvalues of `A'` are also `c/λ`.  Taking valuations, the slopes on the `ψ⁻¹`-space are
`(k+1) − α` as `α` runs over the slopes on the `ψ`-space.  Sorting one list in increasing order
sorts the other in decreasing order, which is the indexed form quoted above.

### Formulation decision (deviation from the source's indexing, same content)

The Lean statements use **multisets of roots** rather than [LWX]'s sorted indexing
`α_i = k+1 − α_{n−1−i}`.  Justification: the two are equivalent, the multiset form needs no sorting
machinery, and it serves both consumers directly — `Multiset.sum` gives the slope total that
[LWX, Step I] consumes, `Multiset.count` gives the per-slope multiplicities that [LWX, Step III]
consumes ("the multiplicity is the same as the dimension of slope zero subspace",
`lwx.txt:2053–2058`).  Recovering the sorted form later is a pure `Multiset.sort` exercise with no
mathematical content and is deliberately not planned.

---

## Leaves — algebraic half (`PhD/TateFredholm/CharpolyPairing.lean`)

- **A1** (leaf, mathlib): `Matrix.det_mul_det_of_mul_eq_smul` — `CharpolyPairing.lean:55`
  - `A * B = c • 1 → A.det * B.det = c ^ Fintype.card n`.
  - Substrate (hand verification): `det (A*B) = det A * det B` and
    `det (c • 1) = c ^ card * det 1 = c ^ card`.
  - Discharged by: `Matrix.det_mul` (`Determinant/Basic.lean:138`, verified),
    `Matrix.det_smul` (`Determinant/Basic.lean:272`, verified — signature
    `det (c • A) = c ^ Fintype.card n * det A`), `Matrix.det_one`.  Three lemmas, at the ≤ 3
    threshold.
  - Attacks attempted:
    - [1] Counterexample: the identity is an equality of two ring elements derived by a chain of
      three `rfl`-level rewrites; no contradicting statement possible.  Searched
      `Determinant/Basic.lean` for a competing `det_smul` convention — only the one above exists.
    - [2] Edge cases: `card n = 0` (empty index) gives `1 * 1 = c ^ 0 = 1` ✓; `card n = 1` gives
      `a * b = c` ✓; `c = 0` gives `det A * det B = 0`, consistent since `A * B = 0` ✓.
    - [3] Hypothesis strength: no `Nontrivial`, no `Field`, no invertibility used — `CommRing` is
      minimal.  Removing `h` makes the statement plainly false.  No hidden typeclass.
    - Verdict: SURVIVED.

- **A2** (leaf, project): `Matrix.charpolyRev_conj` — `CharpolyPairing.lean:60`
  - `Q * P = 1 → (P * M * Q).charpolyRev = M.charpolyRev`.
  - Substrate: `charpolyRev (P*M*Q) = charpolyRev (Q*(P*M))` by Sylvester, `= charpolyRev ((Q*P)*M)`
    by associativity, `= charpolyRev M`.
  - Discharged by: `Matrix.charpolyRev_mul_comm` in `PhD/TateFredholm/Charpoly.lean:47` (verified
    present and **sorry-free**: `grep -c sorry PhD/TateFredholm/Charpoly.lean` = 0), plus
    `Matrix.mul_assoc`, `Matrix.one_mul`.
  - Attacks attempted:
    - [1] Counterexample: none; Sylvester's identity is symmetric and unconditional over `CommRing`.
    - [2] Edge cases: `M = 0` ✓; `P = Q = 1` ✓; non-square intermediate not possible here since all
      are `n × n`.
    - [3] Hypothesis strength: only `Q * P = 1` is used, **not** `P * Q = 1` — deliberately the
      weaker one-sided hypothesis, so callers need not prove both.  Attempted to weaken further to
      `Q * P` idempotent: fails, `charpolyRev_eq_of_mul_eq` shows that needs extra `ME = EM = M`
      hypotheses.  So `Q * P = 1` is exactly right.
    - [5] Discharge: `charpolyRev_mul_comm (A : Matrix n m R) (B : Matrix m n R) : (A*B).charpolyRev
      = (B*A).charpolyRev` — read from source, type matches at `A := P*M`, `B := Q`.
    - Verdict: SURVIVED.

- **A3** (leaf, mathlib): `Matrix.charpoly_conj` — `CharpolyPairing.lean:65`
  - `Q * P = 1 → (P * M * Q).charpoly = M.charpoly`.
  - Substrate: for square matrices a one-sided inverse is two-sided, so `P` is a unit; conjugation
    by a unit preserves `charpoly`.
  - Discharged by: `Matrix.mul_eq_one_comm` (turns `Q * P = 1` into `P * Q = 1`, hence a unit) and
    `Matrix.charpoly_units_conj` (`Charpoly/Basic.lean:280`, verified present).  Two lemmas.
  - Attacks attempted:
    - [1] Counterexample: none — similarity invariance of `charpoly` is standard.
    - [2] Edge cases: `card n = 0` ✓ (both sides `1`); `P = Q = 1` ✓.
    - [3] Hypothesis strength: `mul_eq_one_comm` needs the index type finite and decidable, both
      already in scope.  Over a general (non-commutative) ring this would fail, but `CommRing` is
      assumed and required by `charpoly` itself.
    - [4] Source-drift: this is not from [LWX] at all; it is standard linear algebra used by the
      reduction.  No drift possible.
    - [5] Discharge: `charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R)` — signature read
      from `Basic.lean:280`.  The bundling into `ˣ` is why the convenience wrapper is worth having.
    - Verdict: SURVIVED.

- **A4** (leaf, mathlib): `Matrix.C_det_mul_charpolyRev_eq` — `CharpolyPairing.lean:72`
  - `A * B = c • 1 → C A.det * B.charpolyRev = (-1)^card * A.charpoly.comp (C c * X)`.
  - Substrate (hand verification): multiply `charpolyRev B = det (1 − X·B)` by `det A` to get
    `det (A − cX·1)`, then `det (A − cX) = (−1)^n det (cX − A) = (−1)^n · charpoly A` evaluated at
    `cX`.  **Checked at `n = 1`:** LHS `a(1−bX) = a − cX`; RHS `−(cX − a) = a − cX` ✓.
    **Checked at `n = 2`, `A = diag(a₁,a₂)`, `B = diag(b₁,b₂)`:** LHS `(a₁−cX)(a₂−cX)`; RHS
    `(+1)(cX−a₁)(cX−a₂) = (a₁−cX)(a₂−cX)` ✓.
  - Discharged by: `Matrix.charpolyRev`, `Matrix.charpoly`, `Matrix.charmatrix`
    (`Charpoly/Basic.lean:49,132`), `Matrix.det_mul`, `Polynomial.comp`.  This is the largest leaf
    on the board and may want splitting during execution; flagged in its ticket.
  - Attacks attempted:
    - [1] Counterexample: the `n = 1` and `n = 2` checks above are the counterexample search; both
      confirm rather than refute.  A sign error would show at `n = 1`, and does not.
    - [2] Edge cases: `card n = 0` — both sides `1` (empty det, `(-1)^0`, `charpoly = 1`) ✓;
      `c = 0` — LHS `C (det A) * charpolyRev B`, RHS `(−1)^n · charpoly A` composed with `0`,
      i.e. constant term; consistent since `A * B = 0` ✓; `R` the zero ring — both sides `0` ✓.
    - [3] Hypothesis strength: no invertibility, no `Field`, no `Nontrivial` — `CommRing` minimal.
      `h` is essential; without it the two sides are unrelated.
    - Verdict: SURVIVED, with a size flag rather than a correctness flag.

- **A5** (leaf, mathlib): `Matrix.det_ne_zero_of_mul_eq_smul` — `CharpolyPairing.lean:84`
  - `c ≠ 0 → A * B = c • 1 → A.det ≠ 0`.  Immediate from A1: `det A * det B = c^n ≠ 0` in a field.
  - Discharged by: A1 (project, this file) plus `pow_ne_zero`, `mul_ne_zero_iff`.
  - Attacks attempted:
    - [1] Counterexample: would need `det A = 0` with `c ≠ 0`; then `c^n = 0`, contradiction in a
      field.  None exists.
    - [2] Edge cases: `card n = 0` — `det A = 1 ≠ 0` ✓ and `c^0 = 1 ≠ 0` ✓.
    - [3] Hypothesis strength: `Field` needed (over a general `CommRing`, `det A` could be a
      zero-divisor); `c ≠ 0` needed (at `c = 0`, `A = 0` is a counterexample for `n ≥ 1`).  Both
      necessary.
    - Verdict: SURVIVED.

- **A6** (leaf, mathlib): `Matrix.roots_charpoly_of_mul_eq_smul` — `CharpolyPairing.lean:93`
  - `c ≠ 0 → A * B = c • 1 → B.charpoly.roots = A.charpoly.roots.map (c / ·)`.
  - Substrate: over an algebraically closed field `charpoly` is monic of degree `n` and splits, so
    `roots` has full multiplicity; `A` is invertible by A5, `B = c A⁻¹`, and the eigenvalues of
    `c A⁻¹` are `c/λ`.  A4 is the division-free form of exactly this.
  - Discharged by: A4 + A5 (project, this file), `Matrix.charpoly_monic`
    (`Charpoly/Coeff.lean:120`), `Matrix.charpoly_natDegree_eq_dim` (`Coeff.lean:116`),
    `Polynomial.roots`.  More than three lemmas ⇒ **this is an internal node, not a true leaf**;
    its ticket says so and permits sub-tickets.
  - Attacks attempted:
    - [1] Counterexample: searched for a root `0` of `A.charpoly`, which would make `c / x`
      undefined-by-junk.  `A` invertible (A5) rules it out: `0` is a root of `charpoly` iff
      `det A = 0`.  Recorded because this is the one way the statement could silently be wrong.
    - [2] Edge cases: `card n = 0` — both multisets empty ✓; `card n = 1` — `{c/a}` vs `{c/a}` ✓;
      `A = c • 1, B = 1` — roots of `B.charpoly` are `{1,…}` and `c/c = 1` ✓.
    - [3] Hypothesis strength: `IsAlgClosed` needed, else `roots` undercounts and the multisets have
      different cardinalities (e.g. `A` a rotation over `ℝ`: `roots = ∅` but the claim would
      still assert equality of empty multisets — vacuously fine, yet `B`'s roots need not be empty;
      so the hypothesis is genuinely load-bearing).  `c ≠ 0` needed as in A5.
    - Verdict: SURVIVED, reclassified leaf → internal node.

## Leaves — `p`-adic half (`PhD/LWX/AtkinLehner.lean`)

All eight matrix leaves below were verified by hand at planning time; the computations are written
out because there is no source passage to quote.

- **W0** (def): `LWX.atkinLehner`, `LWX.atkinLehnerConj` — `AtkinLehner.lean:62,67`.
  `w = (0, 1; −p^m, 0)` and `conj γ = (d, −c/p^m; −b p^m, a)`.  API: W1–W8 below.

- **W1** (leaf, mathlib): `LWX.pow_ne_zero_padic` — `:72`.  `(p : ℚ_[p])^m ≠ 0`.
  Substrate: `ℚ_[p]` has characteristic zero and `p ≠ 0` in `ℕ`.
  Discharged by: `pow_ne_zero`, `Nat.cast_ne_zero`, `hp.out.pos`.
  Attacks: [1] no counterexample — `p` prime so `p ≠ 0`; [2] `m = 0` gives `1 ≠ 0`, needs
  `Nontrivial ℚ_[p]` ✓; [3] `Fact p.Prime` already in scope, not over-specified (`p ≠ 0` would
  suffice but `Fact p.Prime` is the ambient convention of every LWX file).  SURVIVED.

- **W2** (leaf, mathlib): `LWX.det_atkinLehner` — `:77`.  `det w = p^m`.
  Substrate: `det (0,1; −P,0) = 0·0 − 1·(−P) = P`.
  Discharged by: `Matrix.det_fin_two_of`, `ring`.
  Attacks: [1] recomputed twice by hand, `= +P` not `−P` (the minus sign sits in the lower-left
  entry, and `det = ad − bc = 0 − (1)(−P)`); [2] `m = 0` gives `det = 1` ✓, consistent with `w`
  then lying in `GL₂(ℤ_p)`; [3] no hypotheses to weaken.  SURVIVED.

- **W3** (leaf, hand-verified): `LWX.atkinLehner_mul_atkinLehnerConj` — `:82`.
  `w * conj γ = γ * w`, the defining identity, stated multiplicatively so **no matrix inverse ever
  appears** in this development.
  Substrate (full hand verification, `P := p^m`):
  `w · conj γ` row 1 `= (0·d + 1·(−bP), 0·(−c/P) + 1·a) = (−bP, a)`; row 2
  `= (−P·d + 0, −P·(−c/P) + 0) = (−Pd, c)`.
  `γ · w` row 1 `= (a·0 + b·(−P), a·1 + b·0) = (−bP, a)`; row 2 `= (c·0 + d·(−P), c·1 + d·0)
  = (−Pd, c)`.  Both rows agree ✓.
  Discharged by: `Matrix.mul_fin_two` / `Matrix.ext` + `Fin.cases`, `field_simp` (to clear `c/P`),
  `ring`.  Needs W1 for `P ≠ 0`.
  Attacks: [1] the row-2 entry `−P·(−c/P) = c` is the only step that can fail, and it fails exactly
  when `P = 0`; W1 excludes that.  Recorded as the single point of failure.  [2] `m = 0`: `w =
  (0,1;−1,0)`, `conj γ = (d,−c;−b,a)`, recomputed by hand, identity holds ✓.  `γ = 0`: both sides
  `0` ✓.  `γ` singular: the identity is polynomial in the entries, so singularity is irrelevant ✓.
  [3] No hypothesis on `γ` at all — deliberately stated for **every** matrix, not just Iwahori
  elements, since the identity is formal.  Attempted to see whether integrality is needed: it is
  not.  SURVIVED.

- **W4** (leaf, hand-verified): `LWX.det_atkinLehnerConj` — `:88`.  `det (conj γ) = det γ`.
  Substrate: `det (d, −c/P; −bP, a) = da − (−c/P)(−bP) = da − cb = det γ` ✓ (needs `P ≠ 0`).
  Discharged by: `Matrix.det_fin_two_of`, W1, `field_simp`, `ring`.
  Attacks: [1] the cancellation `(c/P)(bP) = cb` is the only risk and needs `P ≠ 0` (W1);
  [2] `m = 0` ✓, `γ = 0` ✓; [3] no hypotheses on `γ`.  SURVIVED.

- **W5, W6** (leaves, mathlib): `LWX.atkinLehnerConj_apply_zero_zero`, `_apply_one_one` — `:96,103`.
  `conj γ 0 0 = γ 1 1` and `conj γ 1 1 = γ 0 0`: **the diagonal swap**, which is the matrix-level
  content of "conjugation by `w` inverts the nebentypus".
  Discharged by: `simp [atkinLehnerConj]` — both are definitional after `Matrix.cons_val`.
  Attacks: [1] read off the definition, no room for error; [2] no edge cases (unconditional);
  [3] no hypotheses.  Marked `@[simp]` because downstream character bookkeeping will rewrite with
  them constantly.  SURVIVED.

- **W7** (leaf, hand-verified): `LWX.mul_diagonal_eq_det_add` — `:109`.
  `γ 0 0 * γ 1 1 = γ.det + γ 0 1 * γ 1 0`, i.e. `ad = det + bc`.
  Substrate: `det = ad − bc` for a 2×2 matrix, so `ad = det + bc` ✓ — an identity, not a congruence.
  This is deliberately the **exact** form; the "characters multiply to the central one modulo `p^m`"
  statement follows because `p^m ∣ c` on the Iwahori, and is left to the consumer so that no `ZMod`
  reduction machinery enters this board.
  Discharged by: `Matrix.det_fin_two`, `ring`.
  Attacks: [1] no counterexample — pure `ring` after unfolding `det_fin_two`; [2] `γ = 0` ✓,
  `γ = 1` gives `1 = 1 + 0` ✓; [3] no hypotheses; deliberately **not** stated modulo `p^m`, which
  would have imported `PadicInt.toZModPow` for no gain.  SURVIVED.

- **W8** (leaf, hand-verified): `LWX.atkinLehnerConj_upElt` — `:125`.
  `conj (diag(1,p)) = diag(p,1)`, i.e. **`w` carries `U_p` to `U'_p`**.
  Substrate: with `a=1, b=0, c=0, d=p` the formula `(d, −c/P; −bP, a)` gives `(p, 0; 0, 1)` ✓.
  Discharged by: `simp [atkinLehnerConj, upElt, upEltAdj]`, `Matrix.ext`.
  Attacks: [1] recomputed: the `−c/P` entry is `0/P = 0` — well-defined even without `P ≠ 0`, since
  `0/x = 0` in Lean; so this leaf does **not** need W1, a small independence worth noting;
  [2] `m = 0` ✓ (the answer does not depend on `m` at all — the conjugate of a diagonal matrix is
  independent of the level, which is the reason `U_p ↦ U'_p` holds at every level);
  [3] no hypotheses.  SURVIVED.

- **W9** (def + API): `LWX.Iw`, `LWX.mem_Iw_iff` — `:132,137`.
  The Iwahori subgroup: integral, `p^m ∣ c`, unit determinant.  Modelled on the existing
  `LWX.Mh` (`PhD/LWX/HaloWeightH.lean:54`) but with `‖det‖ = 1` in place of `d` a unit, because
  the conjugation swaps `a` and `d` and so does **not** preserve `Mh`.  That non-preservation is
  the reason a new definition is needed rather than reuse; recorded so nobody "simplifies" it back
  to `Mh`.
  Attacks: [3] hypothesis design — checked whether `Mh p (m-1)` could serve: it cannot, since `Mh`
  requires only `‖g 1 1‖ = 1` and the conjugate needs `‖g 0 0‖ = 1` too.  Confirmed by W10.
  SURVIVED.

- **W10** (leaf, hand-verified): `LWX.norm_apply_zero_zero_of_mem_Iw` — `:142`.
  `m ≠ 0 → g ∈ Iw p m → ‖g 0 0‖ = 1`.
  Substrate: `det = ad − bc` with `‖bc‖ ≤ ‖c‖ ≤ p^{−m} < 1 = ‖det‖`, so by the ultrametric equality
  case `‖ad‖ = ‖det‖ = 1`; both `‖a‖, ‖d‖ ≤ 1` forces both `= 1` ✓.
  Discharged by: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (or the `norm_sub` variant),
  `norm_mul`, W7.
  Attacks: [2] **`m = 0` is a genuine counterexample**: `γ = (0,1;1,0)` has `‖det‖ = 1` and
  `‖γ 0 0‖ = 0`.  So [3] the hypothesis `m ≠ 0` is **necessary, not over-specified** — this attack
  was run precisely to test it and confirms the hypothesis.  SURVIVED with the hypothesis justified.

- **W11** (leaf, hand-verified): `LWX.atkinLehnerConj_mem_Iw` — `:148`.
  **`w` normalises `Iw_{p^m}`.**
  Substrate: entries of `conj γ` are `d` (norm ≤ 1 ✓), `−c/P` (`‖c/P‖ = ‖c‖·p^{m} ≤ 1` ✓),
  `−bP` (`‖bP‖ = ‖b‖p^{−m} ≤ p^{−m}`, which is both ≤ 1 and the lower-left bound ✓), and `a`
  (≤ 1 ✓); determinant unchanged by W4 ✓.
  Discharged by: W4, `mem_Iw_iff`, `norm_div`, `norm_mul`, `padicNormE` norm of `p^m`.
  Attacks: [3] **hypothesis-strength attack SUCCEEDED during planning.**  The draft carried
  `hm : m ≠ 0`, copied from W10.  Re-deriving the four bounds shows none of them uses `m ≠ 0`:
  the statement holds at `m = 0` as well.  The hypothesis was **removed** from the skeleton and the
  statement re-elaborated.  This is the one leaf whose statement changed as a result of the
  adversarial pass.  [2] `m = 0` now checked explicitly and holds ✓.  [1] no counterexample after
  the fix.  SURVIVED after correction.

## Internal node — the reduction

- **R1** (leaf, project): `LWX.det_mul_det_atkinLehner` — `:167`.
  `A * B = c • 1`, `Q * P = 1`, `A' = P * B * Q` ⟹ `det A * det A' = c ^ card ι`.
  Substrate: `det A' = det P · det B · det Q = det B` since `det Q · det P = 1`; then A1.
  Discharged by: A1, A2-style `det_mul`, `Matrix.det_mul`.
  Attacks: [3] **hypothesis-strength attack SUCCEEDED during planning.**  The draft placed this in
  a `[Field K] [IsAlgClosed K]` section; the proof uses neither.  Moved to its own `CommRing`
  section and re-elaborated.  Second statement changed by the adversarial pass.
  [2] `card ι = 0` ✓.  [1] no counterexample.  SURVIVED after correction.

- **R2** (internal, MILESTONE): `LWX.roots_charpoly_atkinLehner` — `:182`.
  [LWX, Prop 3.22] in multiset form, granted the hypothesis.
  Composition: A3 (conjugation preserves `charpoly`) then A6 (root pairing).
  Composition attack: could A3 and A6 both hold and R2 fail?  Only if `A' = P B Q` did not transfer
  `charpoly`, or if the `map (c/·)` were applied to the wrong side.  Checked by instantiating
  `P = Q = 1`, `A' = B`, where R2 reduces exactly to A6 ✓; and by `card ι = 1`, where both sides are
  `{c/a}` ✓.  No composition gap.
  Ticket permits sub-tickets if the `charpoly` transfer needs its own step.

- **R3** (leaf, project): `LWX.norm_roots_charpoly_atkinLehner` — `:198`.
  The slope form.  `Multiset.map_map` on R2 plus `norm_div`.
  Attacks: [1] none; [2] `card ι = 0` ✓; [3] `NormedField` is the minimal class carrying `‖·‖` with
  `norm_div`; `IsAlgClosed` inherited from R2.  Kept in this file rather than `CharpolyPairing.lean`
  so that the algebraic file stays free of analysis imports — a deliberate design choice recorded
  in both module docstrings.  SURVIVED.

---

## Prior-B2 log consultation (Step 4.6)

Read `.mathlib-quality/b2_log.jsonl` (3 entries) and every per-board log
(`jacobs` 4, `lwx-halo` 3, `lwx-seam-m` 2, `lwx-seam` 0, `lwx-slopes` 0, `tate-riesz` 0) — 12
entries total.

- **No match by name**: none of the 20 declaration names on this board appears as a
  `lemma_name` in any log.
- **No match by shape**: grep for `atkin` / `lehner` across all logs returns 0 hits.  No prior B2
  concerns `charpoly`, `charpolyRev`, root multisets, or Iwahori normalisation.
- Verdict: clean of prior B2 history.

## Confidence gate (Step 5)

| # | Condition | Status |
|---|---|---|
| 1 | Every leaf discharged from mathlib or project code, or an explicit API gap with a sub-tree | **PASS** — 18 leaves discharged; the operator identity is carried as a hypothesis, not a leaf |
| 2 | Lean skeleton compiles | **PASS** — `lake build PhD.LWX.AtkinLehner`, sorry warnings only, verified 2026-09-06 |
| 3 | Verbatim source quote per leaf | **PASS with a recorded exception** — the top-level result R has its verbatim quote; the eighteen elementary leaves have **no source passage because [LWX] never performs these computations**, and each instead carries a written-out hand verification per the fallback chain |
| 4 | Adversarial pass on every leaf and internal node | **PASS** — 3+ attack categories each; **two attacks succeeded** (W11's `hm`, R1's typeclasses) and both were fixed in the skeleton before this gate |
| 5 | Prior-B2 log checked | **PASS** — 12 entries, no name or shape match |
| 6 | Tree mirrors the source's proof structure | **DELIBERATE DEPARTURE, documented** — the source proves R by Jacquet–Langlands, which is ruled out; the fallback chain is applied and recorded above.  No LOC estimates are given anywhere on this board, precisely because there are no source line counts to anchor them |
| 7 | Every leaf single-conclusion | **PASS** — no leaf's conclusion is a top-level `∧`; the multi-part source statement is split into determinant form (R1), root form (R2) and slope form (R3) |

**Gate verdict: PASS for ticket creation**, with condition 3's exception and condition 6's departure
recorded explicitly above rather than silently absorbed.  The one genuine API gap — the operator
identity — is deliberately **not** ticketed and is the intended `/expert-review` question.
