# Ticket Board — hurwitz-cn1

Board: `.mathlib-quality/hurwitz-cn1/` (parallel-boards repo — workers MUST name this
board; the default board belongs to another project).  Companion documents:
`plan.md` (goal, inventory, graph), `decomposition.md` (per-leaf source quotes,
Lean ↔ source matches, adversarial logs — **read the entry for your leaf before
starting**).

## Summary
- Total: 28 tickets (18 proof + 1 integration + 9 cleanup)
- Open: 0 | In Progress: 0 | Done: 28
- Parallel capacity: 3 workers at peak (the three prefix-≤3 files are independent)
- Skeleton: all statements already declared `:= by sorry` and `lake build`-green
  (3581 jobs, 2026-08-10).  Tickets are "fill the sorry at file:decl" — do NOT
  restate declarations unless the ticket says so.
- House rules: `omega` not `lia`; never import `PhD.Jacobs`; keep everything inside
  `PhD/JacobsSlash/CN1/` except T19's listed edits; `lake exe runLinter
  PhD.JacobsSlash.CN1.«<file>»` at cleanup gates.

## Conventions used below
- `𝔸f := FiniteAdeleRing (RingOfIntegers ℚ) ℚ`, `K_w := w.adicCompletion ℚ`,
  `𝓞_w := w.adicCompletionIntegers ℚ`.
- All declarations in namespace `JacobsSlash`; statements below are verbatim from the
  compiled skeleton.

---

### [T01] Prove `exists_normSq_sub_le_half`
- **Status**: done (2026-08-10, batch-1 worker A) | **File**: PhD/JacobsSlash/CN1/2_Euclidean.lean:43
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_normSq_sub_le_half (γ : ℍ[ℚ]) :
    ∃ μ ∈ hurwitzOrder, normSq (γ - μ) ≤ 1 / 2 := by sorry
```

#### Proof sketch
[Voight 11.3.1 + Ex. 11.7, p. 169; source proof is 6 lines — expect ~60-90 LOC.]
1. Coordinates: `t := γ.re, x := γ.imI, y := γ.imJ, z := γ.imK`.  Integer candidate
   `μ₁ := (⟨round t, round x, round y, round z⟩ : ℍ[ℚ])`-with-ℤ-casts; it is Hurwitz
   via `IsHurwitz` with `A = 2·round t` etc. (all-even parities, `omega`).
2. Half-integer candidate: `μ₂ := μ₁' + ofTuple`-style — concretely coordinates
   `round (c - 1/2) + 1/2` for each coordinate `c`; Hurwitz with all-odd `A = 2·round
   (t-1/2)+1` etc.  (Use `ofTuple`/`ofTuple_mem_of_parity` from `1_Hurwitz` if
   convenient.)
3. Set `f_c := c - round c` per coordinate; `abs_sub_round` gives `|f_c| ≤ 1/2`.
   `normSq (γ - μ₁) = Σ f_c²` and `normSq (γ - μ₂) = Σ g_c²` with `g_c := c - 1/2 -
   round (c - 1/2)`, `|g_c| ≤ 1/2` — expand with `normSq_def'`, `push_cast`, `ring_nf`.
4. Key inequality: for each coordinate, `f_c² + g_c² ≥ 2·(1/4) - |f_c|·…` — do it
   globally: `Σf² + Σg² ≤ ...` route from decomposition: show
   `min (Σf²) (Σg²) ≤ 1/2` from `Σf² + Σg² ≤ 1`:  per coordinate `f² + g² ≤ 1/4 +
   1/4`? — NO: the sharp fact is `f_c` and `g_c` differ by `1/2` mod ℤ, so
   `|f_c| + |g_c| = 1/2`… simplest formal route: `g_c = f_c - 1/2` or `f_c + 1/2`
   (case on `round (c - 1/2)` vs `round c`, or avoid rounds: `nlinarith` with
   `f_c² ≤ |f_c|/2`, `g_c² ≤ |g_c|/2`, `|f_c| + |g_c| ≥ 1/2`… CHECK: actually
   `f² ≤ |f|/2` needs `|f| ≤ 1/2` ✓ both; and `f² + g² ≤ (|f|+|g|)/2`; with
   `|f_c - g_c| = 1/2`-shape give `Σf² + Σg² ≤ Σ(|f|+|g|)/2` — then min ≤ half of
   sum; close with `nlinarith`/`rcases le_total`).
5. `rcases le_total (Σf²) (Σg²)` and supply `μ₁` or `μ₂` accordingly.

#### Mathlib lemmas needed
- `abs_sub_round` (`|x - round x| ≤ 1/2`) — verified Algebra/Order/Round.lean:193
- `Quaternion.normSq_def'` (`normSq a = a.re^2 + …`) — project-precedented
- `nlinarith` / `push_cast` / `omega` for the parity arithmetic

#### Sources
[Voight GTM 288] 11.3.1 (p. 169) + Exercise 11.7; verbatim quote in
decomposition.md L1.  The half-lattice is what beats the deep hole `(½,½,½,½)` —
integer rounding alone gives only `≤ 1`, insufficient.

#### Generality decision
Concrete `ℍ[ℚ]` (FloorRing generalisation recorded in plan.md, not taken).

---

### [T02] Prove `exists_div_rem`
- **Status**: done (proven in batch 1, 2026-08-10, in CN1/2_Euclidean.lean; status field flipped late 2026-08-11 during CLEANUP-FINAL board audit — code was long verified: build green, axioms [propext, Classical.choice, Quot.sound] re-confirmed in the final battery) | **File**: PhD/JacobsSlash/CN1/2_Euclidean.lean:49
- **Depends on**: T01 | **Parallel**: after T01 | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_div_rem (a b : hurwitzOrder) (hb : b ≠ 0) :
    ∃ q r : hurwitzOrder, a = b * q + r ∧ hnorm r < hnorm b := by sorry
```

#### Proof sketch
[Voight Lemma 11.3.2, p. 169; source proof 4 lines — expect ~40 LOC.]
**Sidedness is load-bearing**: `a = b * q + r`, quotient RIGHT of `b` (see the module
docstring and decomposition.md L2 — the legacy skeleton had it backwards).
1. `hb' : (b : ℍ[ℚ]) ≠ 0` from `Subtype`-injectivity; `γ := (↑b)⁻¹ * ↑a : ℍ[ℚ]`.
2. T01 at `γ`: `μ ∈ hurwitzOrder`, `normSq (γ - μ) ≤ 1/2`.
3. `q := ⟨μ, hμ⟩`, `r := a - b * q`; the first conjunct is `by ring`-rearrangement.
4. `(↑r : ℍ[ℚ]) = ↑b * (γ - μ)`: `field_simp`/`mul_sub` with `mul_inv_cancel₀ hb'`.
5. `normSq ↑r = normSq ↑b * normSq (γ - μ) ≤ normSq ↑b / 2 < normSq ↑b` using
   `map_mul normSq`, `normSq > 0` (from `hb'` via `normSq_eq_zero`), `linarith`.
6. Convert to `hnorm` with `hnorm_coe` + `Nat.cast_lt` (`exact_mod_cast`).

#### Mathlib lemmas needed
- `map_mul` (of `Quaternion.normSq`), `Quaternion.normSq_eq_zero`,
  `mul_inv_cancel₀`; project `hnorm_coe` (1_Hurwitz.lean:153), `hnorm_eq_zero_iff`.

#### Sources
[Voight Lemma 11.3.2] (p. 169); verbatim quote + sidedness analysis in
decomposition.md L2.

#### Generality decision
Right-division form only (that is what right-ideal descent consumes; the left form is
not needed by anything downstream — do not add it).

---

### [T03] Prove `right_ideal_principal`
- **Status**: done (proven in batch 1, 2026-08-10, in CN1/2_Euclidean.lean; status field flipped late 2026-08-11 during CLEANUP-FINAL board audit — code was long verified: build green, axioms [propext, Classical.choice, Quot.sound] re-confirmed in the final battery) | **File**: PhD/JacobsSlash/CN1/2_Euclidean.lean:55
- **Depends on**: T02 | **Parallel**: after T02 | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem right_ideal_principal (I : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder) :
    ∃ x : hurwitzOrder, I = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x} := by sorry
```

#### Proof sketch
[Voight Prop. 11.3.4, p. 169; source proof 5 lines — expect ~50 LOC.]
1. `by_cases hI : I = ⊥`: take `x = 0`; `Submodule.span_zero_singleton`.
2. Else `∃ y ∈ I, y ≠ 0` (`Submodule.ne_bot_iff`).  Let
   `S := {n : ℕ | ∃ y ∈ I, y ≠ 0 ∧ hnorm y = n}`; nonempty; `n₀ := sInf S`;
   `Nat.sInf_mem` gives minimal witness `x ∈ I`, `x ≠ 0`, `hnorm x = n₀`.
3. `≥`: `Submodule.span_le` + `Set.singleton_subset_iff` (`x ∈ I`).
4. `≤`: for `a ∈ I`: T02 with `b := x` (`hb : x ≠ 0`): `a = x * q + r`,
   `hnorm r < hnorm x`.  `r = a - x * q ∈ I`: `x * q = MulOpposite.op q • x`
   (`rfl`-check against `Semiring.toOppositeModule`; the smul is `op q • x = x * q`),
   so `I.smul_mem _ hx`, then `sub_mem`.
5. Minimality: if `r ≠ 0` then `hnorm r ∈ S` contradicts `Nat.sInf_le` + step-2 bound;
   so `r = 0`, `a = x * q ∈ span` via `Submodule.mem_span_singleton` (`⟨op q, rfl⟩`).

#### Mathlib lemmas needed
- `Nat.sInf_mem`, `Nat.sInf_le`, `Submodule.ne_bot_iff`, `Submodule.span_le`,
  `Submodule.mem_span_singleton` (Span/Defs.lean:449),
  `Submodule.span_zero_singleton`; `Semiring.toOppositeModule` (instance, automatic).

#### Sources
[Voight Prop. 11.3.4] (p. 169); quote + the Lipschitz counterexample (Example 11.3.8 —
why this is Hurwitz-specific) in decomposition.md L3.

#### Generality decision
Stated for ALL right ideals including `⊥` (no nontriviality hypothesis) — matches
source.

---

### [CLEANUP-1] /cleanup PhD/JacobsSlash/CN1/2_Euclidean.lean
- **Status**: done (2026-08-10; 172→145 lines; gates 4/4 incl. runLinter "Linting passed";
  helpers merged (two_mul_add_emod_two), rounding blocks factored into exists_normSq_sub_eq,
  public statements byte-identical; 3 redundant imports dropped, Mathlib.Data.Rat.Floor kept
  (FloorRing ℚ); downstream 4_Dictionary + 6_Matrix rebuilt green after import drop) | **Depends on**: T03 | **Type**: cleanup
- Cadence: 3rd proof ticket on the file + final per-file (file complete after T03).
  Include `lake exe runLinter PhD.JacobsSlash.CN1.«2_Euclidean»`.

---

**Progress (T01-T03, worker A, 2026-08-10)**: all three DONE sorry-free, std axioms,
runLinter clean, 1535-job build green. T01 at 2_Euclidean.lean:87-121 via private helpers
`sq_add_sq_le_quarter`/`sq_add_sq_round_le` (per-coordinate f²+g² ≤ 1/4 from f-g = ±1/2);
parity via `two_mul_emod_two` helpers (omega can't see tuple-projection atoms); ADDED import
Mathlib.Data.Rat.Floor (FloorRing ℚ instance missing from Round.lean alone). T02 at :125-140
(`abel` not `ring` — noncommutative; explicit rw chain instead of field_simp). T03 at :145-169
(`I.smul_mem (MulOpposite.op q)` typechecks definitionally at `x * q ∈ I` as planned).

---

### [T04] Prove `hurwitzGen_mem` + `mem_localOrder_iff_exists_coords`
- **Status**: done (2026-08-10, batch-1 worker B) | **File**: PhD/JacobsSlash/CN1/3_LocalApprox.lean:45,52
- **Depends on**: none | **Parallel**: yes (independent of T01-T03) | **Type**: def API + theorem

#### Statement (in skeleton)
```lean
theorem hurwitzGen_mem (i : Fin 4) : hurwitzGen i ∈ hurwitzOrder := by sorry

theorem mem_localOrder_iff_exists_coords {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    {x : D ⊗[ℚ] w.adicCompletion ℚ} :
    x ∈ localOrder w ↔ ∃ c : Fin 4 → w.adicCompletionIntegers ℚ,
      x = ∑ i, hurwitzGen i ⊗ₜ[ℚ] (c i : w.adicCompletion ℚ) := by sorry
```

#### Proof sketch
[Voight 9.4.5/9.5.3 free-basis presentation, p. 145; expect ~120 LOC.]
1. `hurwitzGen_mem`: `fin_cases i` + `Subring.one_mem` / `qi_mem` / `qj_mem` /
   `qomega_mem`.
2. (⇐): `Subring.sum_mem`, each term `tmul_mem_localOrder (hurwitzGen_mem i) (c i)`.
3. (⇒): `Subring.closure_induction` (pattern: `theta_localOrder_subset`,
   2_Level.lean:168).  Predicate: "has a coordinate presentation".
   - Generator `d ⊗ 1`, `d` Hurwitz: `mem_hurwitzOrder_iff_coords` gives integers
     `n : Fin 4 → ℤ` with `d = Σ nᵢ • hurwitzGen i` (prove the reconstruction as a
     private lemma: expand `hurwitzCoord` and check the four quaternion coordinates
     with `QuaternionAlgebra.ext` + `push_cast; ring`).  Coefficients `c i := (nᵢ : 𝓞_w)`
     (`intCast` integrality: `IsUltrametricDist.norm_intCast_le_one` +
     `Valued.toNormedField.norm_le_one_iff`, both project-precedented).
   - Generator `1 ⊗ z`: `c = ![z, 0, 0, 0]` (note `hurwitzGen 0 = 1`).
   - `0`, `+`, `neg`: coefficientwise (`Finset.sum_add_distrib`, `neg` via `-c`).
   - `*`: given presentations `Σ cᵢ (bᵢ⊗1)·Σ c'ⱼ (bⱼ⊗1)`; `tmul_mul_tmul` reduces to
     products `bᵢ*bⱼ ∈ hurwitzOrder` (order closed under mul), re-expanded by the
     private reconstruction lemma with integer matrices; collect `𝓞_w`-bilinearly
     (`Finset.sum_mul_sum`, `smul` bookkeeping).  This is the longest case; a
     16-entry `fin_cases`-table is acceptable (decide-style products of `1,i,j,ω`).

#### Mathlib lemmas needed
- `Subring.closure_induction`, `Subring.sum_mem`, `Algebra.TensorProduct.tmul_mul_tmul`,
  `TensorProduct.add_tmul`/`smul_tmul'`; project `mem_hurwitzOrder_iff_coords`
  (2_Level.lean:384), `tmul_mem_localOrder` (2_Level.lean:104), `qi_mem/qj_mem/qomega_mem`.

#### Sources
[Voight 9.5.3 proof, p. 145] "choose a basis M = Rx₁ ⊕ ⋯ ⊕ Rxₙ. Then M_p ≃ R_p x₁ ⊕ ⋯"
— quote in decomposition.md L10.  No `½` appears: the `1,i,j,ω` coordinates of a
Hurwitz quaternion are integers (that IS `mem_hurwitzOrder_iff_coords`).

#### Generality decision
Stated at every `w` uniformly (no `v₃`-specialisation).

---

### [T05] Prove `exists_intCast_valued_sub_le`
- **Status**: done (2026-08-10, batch-1 worker B) | **File**: PhD/JacobsSlash/CN1/3_LocalApprox.lean:61
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_valued_sub_le {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (c : w.adicCompletionIntegers ℚ) {M : ℤ} (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - (z : w.adicCompletion ℚ))
      ≤ Valued.v ((M : w.adicCompletion ℚ)) := by sorry
```

#### Proof sketch
[Voight (9.5.2), p. 145 — `R/pᵉ ≃ R_p/pᵉR_p`; expect ~70 LOC.]
1. `hMv : Valued.v ((M : K_w)) ≠ 0` (`M ≠ 0`, cast nonzero in char 0, valuation of
   nonzero is nonzero).
2. `denseRange_algebraMap` (AdicValuation.lean:883): rationals come arbitrarily close;
   extract `q : ℚ` with `Valued.v ((c:K_w) - algebraMap ℚ K_w q) ≤ Valued.v (M:K_w)`
   (use the valuation-ball neighbourhood basis: `Valued.mem_nhds` /
   `Valued.hasBasis_nhds`-family — pick the ball of radius `v(M)`; `≤` with `<` both
   fine).
3. `Valued.v (algebraMap ℚ K_w q) ≤ 1` by ultrametric (`≤ max (v c) (v (c - q))`,
   both `≤ 1` — WLOG `v(M) ≤ 1`: if `v(M) > 1`… `M : ℤ` always has `v(M) ≤ 1` ✓ so
   the bound propagates).
4. Convert to `w.valuation ℚ q ≤ 1` via `valuedAdicCompletion_eq_valuation'`; get
   `q = a / b` with `a b : ℤ`, `w.valuation (b) = 1` (write `q = q.num / q.den`;
   `v(q) ≤ 1` and `v(num/den)` arithmetic: if `v(den) < 1` then split den's `w`-part
   into num — cleaner: use `mem_integers_of_valuation_le_one` (project-precedented,
   2_Level.lean:403) to land `q` in `RingOfIntegers`-localization form, or direct:
   choose `k` with `w`-residue-prime power `p^k` s.t. `v(M) = v(p^k)`-comparable and
   solve `z ≡ a·b⁻¹ (mod p^k)` in `ℤ` (`Int.emod`-arithmetic; `b` invertible mod
   `p^k` since coprime to `p`).
5. `v(q - z) ≤ v(M)` by the mod-`p^k` congruence (`valuation_of_algebraMap` +
   `intValuation` of a multiple of `p^k`); combine with step 2 ultrametrically.
Implementation freedom: any route through `ℤ_(p)`-surjectivity is fine; keep the
statement fixed.

#### Mathlib lemmas needed
- `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap` (verified:883),
  `valuedAdicCompletion_eq_valuation'`, `mem_adicCompletionIntegers`,
  `HeightOneSpectrum.mem_integers_of_valuation_le_one`, `Rat.ringOfIntegersEquiv`,
  `Rat.num_div_den`; `Int` congruence API (`Int.emod_emod_of_dvd`,
  `Int.exists_gcd_eq…`-family or `ZMod` units).

#### Sources
[Voight (9.5.2)] quote in decomposition.md L11.  `M ≠ 0` is REQUIRED (B2-lesson audit
there — at `M = 0` the statement demands an exact integer hit, false).

#### Generality decision
`M : ℤ` (not `ℕ`), `≤` (not `<`) — matches consumers.

---

### [T06] Prove `exists_intCast_valued_eq_one_of_le`
- **Status**: done (2026-08-10, batch-1 worker B) | **File**: PhD/JacobsSlash/CN1/3_LocalApprox.lean:69
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_valued_eq_one_of_le {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (T : Finset (HeightOneSpectrum (RingOfIntegers ℚ))) (hw : w ∉ T) {M : ℤ} (hM : M ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ Valued.v ((m : w.adicCompletion ℚ)) = 1 ∧
      ∀ v ∈ T, Valued.v ((m : v.adicCompletion ℚ))
        ≤ Valued.v ((M : v.adicCompletion ℚ)) := by sorry
```

#### Proof sketch
[Voight 28.1.1 (CRT), p. 477; expect ~80 LOC.]
1. `Finset.induction` on `T` — base: `m = 1` (`Valued.v 1 = 1`, `map_one`).
2. Inductive step (`T = insert v T'`, `hv : v ∉ T'`, `v ≠ w`): from IH get `m'` for
   `T'`.  Need `n_v : ℤ`, `n_v ≠ 0`, `w`-unit AND `u`-unit for every `u ∈ T' ∪ {w}`…
   — simpler formulation that suffices: get `n_v` with `v(n_v) ≤ v(M)·v(m')⁻¹`-slack…
   AVOID inverse juggling: strengthen per-place: produce `n_v` with
   `Valued.v ((n_v : v.adicCompletion ℚ)) ≤ Valued.v ((M : _)) ` at `v` and
   `Valued.v ((n_v : u.adicCompletion ℚ)) = 1` for every `u ≠ v` (a "uniformiser-power
   coprime to everything else" — see 3).  Then `m := m' * n_v` works: at `v`:
   `v(m) = v(m')·v(n_v) ≤ 1·v(M)` ✓; at `u ∈ T'`: `= v(m')·1 ≤ v(M)` ✓; at `w`:
   `1·1 = 1` ✓.
3. Per-place kernel: distinct height-one primes of `𝓞_ℚ` are distinct maximal ideals;
   comaximality `v.asIdeal ⊔ u.asIdeal = ⊤` (`Ideal.IsMaximal.coprime_of_ne`-family).
   Take `r ∈ v.asIdeal^k` with `r ≡ 1 mod ∏_{u ∈ (T'∪{w})} u.asIdeal`
   (CRT: `Ideal.quotientInfRingEquivPiQuotient`-style, or transport everything to `ℤ`
   through `Rat.ringOfIntegersEquiv` and use plain `Int`/`Nat.chineseRemainder` with
   prime powers — RECOMMENDED, the ℤ route is far lighter).  `k` chosen so
   `v(p_v^k) ≤ v(M)` (`intValuation` of powers: `intValuation_le_pow_iff_dvd`-family,
   or repeat-multiply until below — `WithZero` order induction).
4. Nonzeroness: products of nonzeros.

#### Mathlib lemmas needed
- `Finset.induction_on`; `Nat.chineseRemainder` / `ZMod.chineseRemainder` (ℤ route);
  `Rat.ringOfIntegersEquiv`; `HeightOneSpectrum.intValuation_lt_one_iff_mem`-family +
  `valuation_of_algebraMap`; `map_one`, `map_mul` of `Valued.v`.

#### Sources
[Voight 28.1.1] verbatim CRT quote in decomposition.md L12.  `w ∉ T` is essential
(contradiction analysis there).

#### Generality decision
Valuation-inequality form (NOT ideal-divisibility) — the L13-catch formulation.

---

**Progress (T04-T06, worker B, 2026-08-10)**: all DONE, std axioms, build green (only T07
sorry at :277). DESIGN WINS recorded: T05 — mathlib ALREADY HAS the denominator-clearing step
as `HeightOneSpectrum.exists_valuation_sub_lt_of_integer` (AdicValuation.lean:561); no manual
mod-p^k construction. NB `Valued.mem_nhds` at this rev goes through `Valuation.restrict` into
`MonoidWithZeroHom.ValueGroup₀` — ball witness is `Units.mk0 (Valued.v.restrict (M:K_w)) _`
with `restrict_lt_iff`/`restrict_eq_zero_iff` simp bridges. T06 — NO CRT: per-place kernel
r^k with r ∈ v.asIdeal ∖ w.asIdeal (SetLike.not_le_iff_exists + IsMaximal.eq_of_le
incomparability), exponent via `WithZero.exists_exp_neg_natCast_lt`. T04 — no 16-case table:
coordSpan→coordSubring→Subring.closure_le (2_Level localSpan pattern), mul case uniform via
Finset.sum_mul_sum + tmul_mul_tmul. 12 private helpers incl. valued_intCast* family.

---

### [CLEANUP-2] /cleanup PhD/JacobsSlash/CN1/3_LocalApprox.lean (mid-file)
- **Status**: done (2026-08-10; 285→274 lines net of +8 docs; gates 4/4; T07 untouched at :272;
  1-use intCast helper inlined via root `intCast_mem`; unusedSimpArgs instrumented — zero
  droppable args; valued_algebraMap KEPT deliberately as instance-path bridge for the pinned
  Algebra ℚ K_w path) | **Depends on**: T04, T05, T06 | **Type**: cleanup
- Cadence: after the 3rd proof ticket on this file.  runLinter gate as CLEANUP-1.

---

### [T07] Prove `exists_intCast_approx`
- **Status**: done (2026-08-10, batch-2 worker; pure composition of T05+T06, 0 new helpers; Valuation.map_div directly; (m:K_w) ≠ 0 from v(m)=1 avoiding char-zero; proof :273-294) | **File**: PhD/JacobsSlash/CN1/3_LocalApprox.lean:80
- **Depends on**: T05, T06, CLEANUP-2 | **Parallel**: no | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_approx {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (T : Finset (HeightOneSpectrum (RingOfIntegers ℚ))) (hw : w ∉ T)
    (c : w.adicCompletionIntegers ℚ) {M : ℤ} (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - (z : w.adicCompletion ℚ))
        ≤ Valued.v ((M : w.adicCompletion ℚ)) ∧
      ∀ v ∈ T, Valued.v ((z : v.adicCompletion ℚ))
        ≤ Valued.v ((M : v.adicCompletion ℚ)) := by sorry
```

#### Proof sketch
[Voight 9.5.3 proof + 28.1.1; the `m`-factorisation design of decomposition.md L13 —
expect ~50 LOC.]
1. T06 (`T`, `hw`, `hM`): `m` nonzero, `w`-unit, `T`-small.
2. `c' := (c : K_w) / m`: in `𝓞_w` (`v(c') = v(c)·v(m)⁻¹ = v(c) ≤ 1` — division by a
   valuation-1 element; package as `⟨c', proof⟩ : 𝓞_w`).
3. T05 at `c'`, modulus `M`: `t : ℤ`, `v(c' - t) ≤ v(M)`.
4. `z := m * t`.  First conjunct: `c - z = m·(c' - t)` (field algebra, `m ≠ 0` cast),
   `v(c - z) = v(m)·v(c' - t) = v(c' - t) ≤ v(M)` (`map_mul`, `v(m) = 1`).
5. Second conjunct: at `v ∈ T`: `v(z) = v(m)·v(t) ≤ v(M)·1` (`t` integer ⟹ `v(t) ≤ 1`
   — `intCast` integrality).

#### Mathlib lemmas needed
- `map_mul` of `Valued.v`; `mul_le_one'`-style `WithZero` order lemmas; intCast
  integrality (as T04 step 3); `div_mul_cancel₀`.

#### Sources
[Voight 9.5.3 proof] quote at decomposition.md N3-head; the formulation-catch record
at L13 (integer divisibility by `M` at `w` would be FALSE — do not "simplify" the
statement back).

#### Generality decision
As stated; the `M²`-slack is applied by the CALLER (T15), not here.

---

### [CLEANUP-3] /cleanup PhD/JacobsSlash/CN1/3_LocalApprox.lean (final)
- **Status**: done (2026-08-10; 296→290 lines; gates 4/4; unusedSimpArgs/Tactic/Variables all
  clean; T07 tail golfed (dead hm0 dropped, Valuation.ne_zero_iff term, mul_div_cancel₀
  deterministic rewrite replacing field_simp). VERIFIED-BUT-HELD follow-up for CLEANUP-ALL-1:
  private one_re/one_imI/one_imJ/one_imK (:52-55) are redundant — mathlib has
  Quaternion.re_one/imI_one/imJ_one/imK_one (scoped simp, file has open Quaternion); swap into
  the :70 simp only and delete (scratch-verified clean). Same four also private in
  2_Level.lean:234-237 — cross-file dedup is out of cleanup scope, note only.) | **Depends on**: T07 | **Type**: cleanup

---

### [T08] Prove `exists_intCast_smul_mem_hurwitzOrder`
- **Status**: done (2026-08-10, batch-1 worker C) | **File**: PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean:43
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_smul_mem_hurwitzOrder (d : D) :
    ∃ M : ℤ, M ≠ 0 ∧ (M : ℚ) • d ∈ hurwitzOrder := by sorry
```

#### Proof sketch
[Clearing-denominators folklore, cf. Voight 11.3.7's "By clearing denominators…";
expect ~25 LOC.]
1. `M := 2 * (d.re.den * d.imI.den * d.imJ.den * d.imK.den)` (positive, nonzero).
2. Membership via `IsHurwitz`: exhibit `A := 2·(M/2·… numerator arithmetic)` — pick
   the direct route: each coordinate of `(M:ℚ)•d` equals an integer
   (`Rat.num_div_den`: `den ∣` clears; `push_cast` + `Rat.mul_den_eq_num`-shape), and
   `2 ∣ M` makes each an EVEN integer; supply `⟨2k₁, 2k₂, 2k₃, 2k₄⟩`-style witnesses
   with all-even parity (`omega`).

#### Mathlib lemmas needed
- `Rat.num_div_den`, `Rat.den_ne_zero`, `push_cast`; `IsHurwitz` unfold.

#### Sources
Folklore step (decomposition.md L4).

#### Generality decision
`M : ℤ` with `•` via `(M : ℚ)` — matches the `ℚ`-algebra structure downstream.

---

### [T09] Prove `exists_intCast_mul_mem_adicCompletionIntegers`
- **Status**: done (2026-08-10, batch-1 worker C) | **File**: PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean:49
- **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_mul_mem_adicCompletionIntegers
    {v : HeightOneSpectrum (RingOfIntegers ℚ)} (x : v.adicCompletion ℚ) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by sorry
```

#### Proof sketch
[The `αv ∈ Ov`-after-scaling content of Voight 27.6.1; expect ~40 LOC.]
1. `x = 0`: `n = 1`.  Else `γ := Valued.v x ≠ 0`.
2. If `γ ≤ 1`: `n = 1`.  Else: pick nonzero `r ∈ v.asIdeal` (nonzero ideal of a
   Dedekind domain); `v(r) < 1` (`intValuation_lt_one_iff_mem`-family through
   `valuation_of_algebraMap`).  In `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, powers of an
   element `< 1` tend to `0`: choose `k` with `v(r)^k ≤ γ⁻¹` (unfold to
   `Multiplicative ℤ` exponents; `omega` on the underlying integers — the project's
   `γ₉_lt_one`-style coercion arithmetic).
3. `n := (Rat.ringOfIntegersEquiv r : ℤ)^k`-shaped (transport `r : 𝓞_ℚ` to `ℤ`);
   `v(n·x) = v(r)^k·γ ≤ 1` ⟹ `mem_adicCompletionIntegers`.

#### Mathlib lemmas needed
- `mem_adicCompletionIntegers` (:812), `valuedAdicCompletion_eq_valuation'`,
  `HeightOneSpectrum.valuation_of_algebraMap`, `intValuation` API,
  `Rat.ringOfIntegersEquiv`, `Ideal.exists_ne_zero_mem`-family
  (`Submodule.exists_mem_ne_zero_of_ne_bot`), `zpow`/`WithZero` order API.

#### Sources
decomposition.md L5.

#### Generality decision
Multiplication form `(n:K_v) * x` (not smul) — composes with the adele component API.

---

### [T10] Prove `exists_intCast_mul_mem_adicCompletionIntegers_forall`
- **Status**: done (2026-08-10, batch-1 worker C) | **File**: PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean:57
- **Depends on**: T09 | **Parallel**: after T09 | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_mul_mem_adicCompletionIntegers_forall
    (a : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v, (N : v.adicCompletion ℚ) * a v ∈ v.adicCompletionIntegers ℚ := by
  sorry
```

#### Proof sketch
[Voight 27.6.1 restricted product = mathlib element structure; the live-framework
`canonicalForm`; expect ~45 LOC.]
1. `S := {v | a v ∉ 𝓞_v}` finite: `a.2` is `∀ᶠ v in cofinite, a v ∈ 𝓞_v`;
   `Filter.eventually_cofinite` unfolds to `S.Finite`.
2. `N := ∏ v ∈ S.toFinset, n_v` with `n_v` from T09 at `a v`.
3. At `v ∈ S`: `(N : K_v) = (n_v : K_v) * (rest : K_v)` (`Int.cast` of a product;
   `Finset.prod_eq_mul_prod_diff_singleton`); `v(rest) ≤ 1` (integer), so
   `v(N·a v) ≤ v(n_v·a v) ≤ 1`.
4. At `v ∉ S`: `v(N) ≤ 1` and `a v ∈ 𝓞_v`: `mul_mem`.

#### Mathlib lemmas needed
- `Filter.eventually_cofinite`, `Set.Finite.toFinset`,
  `Finset.prod_eq_mul_prod_diff_singleton` (or `Finset.mul_prod_erase`), `Int.cast_prod`,
  intCast integrality, `ValuationSubring.mul_mem`-shape.

#### Sources
decomposition.md L6; FLT seam note in the file docstring (their `canonicalForm` is
`sorry`, being dropped — we are first).

#### Generality decision
Componentwise form (`∀ v, (N:K_v) * a v ∈ 𝓞_v`) rather than an `𝔸f`-level statement —
avoids smul-apply plumbing.

---

**Progress (T08-T10, worker C, 2026-08-10)**: all three DONE, std axioms, build green
(only T11/T12 sorries remain at :124/:133). T08 at :59 (M formed in ℕ then cast — M ≠ 0 via
Int.natCast_ne_zero + simp). T09 at :85 — DESIGN WIN superseding the sketch: mathlib already
has the per-place clearing as `IsDedekindDomain.HeightOneSpectrum.adicCompletion.
mul_nonZeroDivisor_mem_adicCompletionIntegers` (AdicValuation.lean:971); only the 𝓞_ℚ→ℤ
bridge (Rat.ringOfIntegersEquiv) + algebraMap↔IntCast identification needed — 10 lines, no
ℤᵐ⁰ arithmetic. T10 at :104 via Finset.mul_prod_erase. Private helpers :42 (den-dvd) and :50
(intCast integrality). runLinter: file clean (60 pre-existing TateFredholm findings unrelated).

---

### [CLEANUP-4] /cleanup PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean (mid-file)
- **Status**: done (2026-08-10; 137→128 lines; gates 4/4; T08 golfed 20→6 lines term-mode —
  the ×2 factor in M was REDUNDANT (product of denominators suffices, IsHurwitz takes A=2a
  all-even), docstring corrected; bespoke intCast-integrality helper deleted in favour of
  root `intCast_mem` (ValuationSubring has SubringClass); T09 conv-block removed; runLinter
  zero findings in-file; sorries now at :117/:124) | **Depends on**: T08, T09, T10 | **Type**: cleanup

---

### [T11] Prove `eventually_toLocal_mem_localOrder`
- **Status**: done (2026-08-10, batch-2 worker) | **File**: PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean:66
- **Depends on**: T08, CLEANUP-4 | **Parallel**: with T12 | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem eventually_toLocal_mem_localOrder
    (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∀ᶠ w in Filter.cofinite, toLocal ℚ D w x ∈ localOrder w := by sorry
```

#### Proof sketch
[Voight 27.6.1 (⊆ half); expect ~60 LOC.]
1. `TensorProduct.induction_on x`.
   - `0`: `map_zero`, `Subring.zero_mem`, `Filter.Eventually.of_forall`.
   - `d ⊗ₜ a`: T08 gives `M`, `(M:ℚ)•d ∈ 𝓞_D`.  Eventually-set: `{w | a w ∈ 𝓞_w}`
     (∈ cofinite by `a.2`) ∩ `{w | Valued.v ((M : K_w)) = 1}` (cofinite:
     `HeightOneSpectrum.Support.finite` applied to `(M:ℚ)⁻¹`, or the finiteness of
     primes dividing `M` via `Int.natAbs.factorization` — either route fine).  On it:
     `toLocal w (d ⊗ₜ a) = d ⊗ₜ (a w)` (`toLocal_tmul` + `evalAlgHom`-apply)
     `= ((M:ℚ)⁻¹ • ((M:ℚ)•d)) ⊗ₜ (a w)`; move the scalar to the right leg
     (`TensorProduct.smul_tmul`), land in `localOrder` by `tmul_mem_localOrder`
     applied to `(M:ℚ)•d` and the local integer `((M:K_w))⁻¹·(a w)` (`v = 1` unit ⟹
     inverse integral: `inv` of valuation-1 has valuation 1).
   - `x + y`: `Filter.Eventually.and` + `map_add` + `add_mem`.

#### Mathlib lemmas needed
- `TensorProduct.induction_on`, `TensorProduct.smul_tmul`, `Filter.Eventually.and`,
  `Filter.eventually_cofinite`, `HeightOneSpectrum.Support.finite` (:44-51);
  QMF `toLocal_tmul`; project `tmul_mem_localOrder`.

#### Sources
decomposition.md L7 (with the [V 27.6.1] verbatim quote at N2-head).

#### Generality decision
`∀ᶠ cofinite` form (what T14/T15 consume via `Set.Finite`).

---

### [T12] Prove `exists_intCast_smul_toLocal_mem`
- **Status**: done (2026-08-10, batch-2 worker) | **File**: PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean:75
- **Depends on**: T08, T10, CLEANUP-4 | **Parallel**: with T11 | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_intCast_smul_toLocal_mem
    (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ w, toLocal ℚ D w ((N : ℚ) • x) ∈ localOrder w := by sorry
```

#### Proof sketch
[The live-framework `canonicalForm`; expect ~55 LOC.]
1. `TensorProduct.induction_on x`.
   - `0`: `N = 1`, `smul_zero`.
   - `d ⊗ₜ a`: `N := M * N_a` (T08 × T10).  `(N:ℚ) • (d ⊗ₜ a) = ((M:ℚ)•d) ⊗ₜ
     ((N_a:ℚ)•a)`-rearrangement (`smul_smul`, `TensorProduct.smul_tmul'`,
     `TensorProduct.smul_tmul`; `mul_comm` on the rational scalars).  At each `w`:
     `toLocal_tmul`, then `tmul_mem_localOrder` with the T10 component fact
     (`((N_a:ℚ)•a) w = (N_a:K_w)·a w` — smul-apply on the restricted product;
     `algebraMap_apply`/`Algebra.smul_def` bridging).
   - `x + y`: `N := N₁ * N₂`; `(N:ℚ)•(x+y) = (N₂:ℚ)•((N₁:ℚ)•x) + (N₁:ℚ)•((N₂:ℚ)•y)`;
     each term: extra integer scalar preserves `localOrder`-membership
     (`(k:ℚ)•ξ = ((1⊗(k:𝔸f-const))·ξ`-route, or scalar-tower smul: `map_smul` of
     `toLocal` then `(k:K_w)•ζ = includeRight(k)·ζ` with `k` integral —
     `Algebra.smul_def` + `mul_mem` + `includeRight_mem_localOrder`).

#### Mathlib lemmas needed
- As T11 plus `smul_smul`, `Algebra.smul_def`, `map_smul` (AlgHom);
  project `includeRight_mem_localOrder`.

#### Sources
decomposition.md L8.

#### Generality decision
`(N:ℚ) • x` smul form (composes with `Units`-scaling in T18/L19).

---

**Progress (T11-T12, batch-2 worker, 2026-08-10)**: both DONE, file 0 sorries, 0 warnings,
std axioms, runLinter clean-in-file. DESIGN WIN (T11): the "M-unit at a.a. places" step
needs NO Support.finite/valuation arithmetic — take the constant adele
b := algebraMap ℚ 𝔸f ((M:ℚ)⁻¹) and use b.2 as the second filter_upwards input; b w =
algebraMap ℚ K_w ((M:ℚ)⁻¹) is rfl under the pinned instance. SEAM NOTE: Algebra.smul_def
does NOT rw on D ⊗[ℚ] K_w (instance path) — `simpa using Algebra.smul_def _ _` works;
Int.cast_smul_eq_zsmul does not unify there. T12 add-case: double `rw [map_smul, map_smul]`
over-rewrites the inner smul — use two explicit `have e := map_smul _ _ _` first. New private
helper intCast_smul_mem_localOrder (:113).

---

### [CLEANUP-5] /cleanup PhD/JacobsSlash/CN1/3_AdeleIntegrality.lean (final)
- **Status**: done (2026-08-10; 181→173 lines; gates 4/4; fallback docstring past-tensed;
  intCast_smul_mem_localOrder retired the Algebra.smul_def seam via Int.cast_smul_eq_zsmul ℚ +
  zsmul_mem one-liner (NB the ring ℚ must be explicit). SEAM UPDATE for the board: the
  "two explicit have e := map_smul bindings" constraint in T12's add case was rw-route
  specific — a `simp only [map_add, map_smul, smul_add, smul_smul]` normalisation avoids the
  over-rewrite entirely. Downstream 4_Dictionary rebuilt green.) | **Depends on**: T11, T12 | **Type**: cleanup

---

### [T13] Prove `latticeOf` closure fields + `intCast_mem_latticeOf`
- **Status**: done (2026-08-10, batch-1 worker D) | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean:50,66
- **Depends on**: none (file imports are skeleton-level) | **Parallel**: yes | **Type**: def fields + theorem

#### Statement (in skeleton)
The three sorried fields of
```lean
noncomputable def latticeOf (g : Dfx ℚ D) : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder
```
(carrier `{y | ∀ w, toLocal ℚ D w (↑(g⁻¹)) * ((y:D) ⊗ₜ[ℚ] 1) ∈ localOrder w}`), plus
```lean
theorem intCast_mem_latticeOf {g : Dfx ℚ D} {N₁ : ℤ}
    (hN₁ : ∀ w, toLocal ℚ D w ((N₁ : ℚ) • (↑(g⁻¹) : D ⊗[ℚ] 𝔸f)) ∈ localOrder w) :
    ((N₁ : ℤ) : hurwitzOrder) ∈ latticeOf g := by sorry
```

#### Proof sketch
[Voight 27.6.8's `α̂𝓞̂ ∩ B`; expect ~50 LOC.]
1. `zero_mem'`: `(0:D) ⊗ₜ 1 = 0` (`TensorProduct.zero_tmul`), `mul_zero`, `zero_mem`.
2. `add_mem'`: `Subring.coe_add`-push, `TensorProduct.add_tmul`, `mul_add`, `add_mem`.
3. `smul_mem'`: for `c : 𝓞ᵐᵒᵖ`: `c • y = y * MulOpposite.unop c` (defeq;
   `rfl`-check), `((y*s : 𝓞) : D) ⊗ₜ 1 = ((y:D) ⊗ₜ 1) * ((s:D) ⊗ₜ 1)`
   (`tmul_mul_tmul` backwards), reassociate (`mul_assoc`), `mul_mem` with
   `tmul_mem_localOrder s.2`-at-`1` (i.e. `includeLeft`-form: use
   `includeLeft_mem_localOrder`).
4. `intCast_mem_latticeOf`: `((N₁:𝓞):D) ⊗ₜ 1 = (N₁:ℚ) • ((1:D) ⊗ₜ 1)`
   (`Int.cast`-through-ℚ + `TensorProduct.smul_tmul'`); `↑(g⁻¹) * ((N₁:ℚ)•(1⊗1)) =
   (N₁:ℚ) • (↑(g⁻¹) * (1⊗1)) = toLocal-image` chain: `mul_smul_comm`, `mul_one`,
   `map_smul`/`map_one` of `toLocal`; conclude from `hN₁ w`.

#### Mathlib lemmas needed
- `TensorProduct.zero_tmul/add_tmul/smul_tmul'`, `Algebra.TensorProduct.tmul_mul_tmul`,
  `mul_smul_comm`, `map_smul`; project `includeLeft_mem_localOrder`.

#### Sources
decomposition.md L14 (integral-truncation note: why `∩ 𝓞` loses nothing for
everywhere-integral `g`).

#### Generality decision
Defined for ALL `g` (no integrality hypothesis on the def) — hypotheses live on the
theorems.

---

**Progress (T13, worker D, 2026-08-10)**: DONE, std axioms, build green (5 expected sorries
remain in file). Fields at 4_Dictionary.lean:54-70, intCast_mem_latticeOf at :80-91. Notes:
`tmul_mem_localOrder (c.unop).2 1` matched the smul goal directly ((1:𝓞_w) coercion unifies
by rfl); carrier membership reduces definitionally after `intro w` (no mem_setOf rewriting);
`MulOpposite.smul_eq_mul_unop` + `Subring.coe_mul` for the ᵐᵒᵖ step; map_smul matched with
no instance bridge despite the pinned adic instance.

---

### [T14] Prove `latticeOf_ne_bot`
- **Status**: done (2026-08-10; :94-109; coercion shapes matched T12/T13 exactly, zero coaxing.
  BOARD NOTE for T15-T18: NO `CharZero hurwitzOrder` instance exists (no CharZero ℍ[ℚ] in
  mathlib; algebraRat.charZero is a theorem not an instance) — `Int.cast_ne_zero` in
  hurwitzOrder needs the coordinate route: Subring.coe_intCast → congrArg re → exact_mod_cast) | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean:73
- **Depends on**: T12, T13 | **Parallel**: after deps | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem latticeOf_ne_bot (g : Dfx ℚ D) : latticeOf g ≠ ⊥ := by sorry
```

#### Proof sketch
[Voight 9.3.5(b) sandwich; expect ~25 LOC.]
1. T12 at `↑(g⁻¹)`: `N₁ ≠ 0`, everywhere integral after `(N₁:ℚ)•`.
2. `intCast_mem_latticeOf` (T13): `(N₁ : 𝓞) ∈ latticeOf g`.
3. `(N₁ : 𝓞) ≠ 0`: coordinates (`Subtype.ext_iff` + `QuaternionAlgebra.ext_iff`,
   `Int.cast_ne_zero` in char-0 ℚ).
4. `Submodule.ne_bot_iff.mpr ⟨_, mem, ne⟩`.

#### Mathlib lemmas needed
- `Submodule.ne_bot_iff`, `Int.cast_ne_zero`.

#### Sources
decomposition.md L15 (with the [V 9.3.5(b)] verbatim quote).

---

### [T15] Prove `exists_mem_latticeOf_sub_smul`
- **Status**: done (2026-08-10, crux worker; :190-280 + 7 private helpers :111-176; std axioms.
  KEY simplification: T = bad places of g⁻¹ ONLY (latticeOf never consumes the g-side set) —
  so `hg` is UNUSED in the proof; signature kept frozen + linter-silenced pending the
  CLEANUP-6 decision below. Seams for T16-T18: Algebra.smul_def DOES rw on K_v (only D⊗K_v
  hostile); valuedAdicCompletion_eq_valuation' is term-use-only (WithVal coercion);
  toolchain renames: mul_le_mul_right' GONE (use mul_le_mul'), Finset.notMem_erase,
  zero_le not zero_le'. Output shapes for T16: heq : ξ − y⊗1 = (N₁:ℚ) • δ with
  δ = Σ hurwitzGen i ⊗ u i; mem_latticeOf_iff is Iff.rfl so intro v works directly.) | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean (the approximation
  theorem; statement block starting ~line 90)
- **Depends on**: T04, T07, T11, T13 | **Parallel**: no (the crux) | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_mem_latticeOf_sub_smul {g : Dfx ℚ D}
    (hg : ∀ w, toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] 𝔸f) ∈ localOrder w)
    {N₁ : ℤ} (hN₁ : N₁ ≠ 0) (hN₁mem : ((N₁ : ℤ) : hurwitzOrder) ∈ latticeOf g)
    {w} {ξ : D ⊗[ℚ] w.adicCompletion ℚ} (hξ : ξ ∈ localOrder w)
    (hξg : toLocal ℚ D w (↑(g⁻¹)) * ξ ∈ localOrder w) :
    ∃ y ∈ latticeOf g, ∃ δ ∈ localOrder w, ξ - (y : D) ⊗ₜ[ℚ] 1 = (N₁ : ℚ) • δ := by sorry
```

#### Proof sketch
[Voight 9.5.3 proof + 9.4.6 — THE research leaf; expect ~150 LOC.  Follow the
numbered discharge in decomposition.md L16 exactly; recalled here.]
1. `T` := (bad set of `↑g` ∪ bad set of `↑(g⁻¹)` from T11, as `Set.Finite`), erase `w`,
   `Set.Finite.toFinset`.
2. `mem_localOrder_iff_exists_coords` (T04) on `ξ`: coefficients `c : Fin 4 → 𝓞_w`.
3. Per `i`: T07 with `T`, `w ∉ T` (by construction), `c i`, modulus `M := N₁^2`
   (`pow_ne_zero`): integers `z i` with `v_w(c i − z i) ≤ v_w(N₁²)` and
   `∀ v ∈ T, v(z i) ≤ v(N₁²)`.  Note `v(N₁²) = v(N₁)² ≤ v(N₁)` (≤ 1).
4. `y := Σ i, (z i : 𝓞) * ⟨hurwitzGen i, hurwitzGen_mem i⟩` (in `𝓞`;
   `Subring.sum_mem`).  Second conjunct: `ξ − y⊗1 = Σ i, hurwitzGen i ⊗ₜ ((c i) − z i)`
   (linear bookkeeping: `Finset.sum_sub_distrib`, `TensorProduct.tmul_sub`,
   intCast-through-tensor); each right leg has `v_w ≤ v_w(N₁)`, so factor
   `= (N₁:ℚ) • Σ i, hurwitzGen i ⊗ₜ ((c i − z i)/N₁)` with quotient legs in `𝓞_w`;
   `δ` := that sum, in `localOrder w` by T04(⇐).
5. First conjunct `y ∈ latticeOf g`, place by place (`mem_latticeOf_iff`):
   - `v ∉ T ∪ {w}`: `toLocal v ↑(g⁻¹) ∈ localOrder v` (T-def) and `y⊗1 ∈ localOrder v`
     (`y ∈ 𝓞`, `tmul_mem_localOrder`); `mul_mem`.
   - `v ∈ T`: `↑(g⁻¹)·(y⊗1) = Σ i, (z i / N₁ : scalar) • (↑(g⁻¹)·(N₁•(bᵢ⊗1)))`:
     the inner factor is `toLocal v ((N₁:ℚ)•↑(g⁻¹)) · (bᵢ⊗1)`-shaped — integral by
     `hN₁mem` at `v` (unfold `intCast_mem_latticeOf`'s content: `↑(g⁻¹)·((N₁:𝓞):D ⊗ₜ 1)
     ∈ localOrder v`, commute the central scalar) times `bᵢ⊗1`; the outer scalar
     `z i / N₁` has `v(z i / N₁) = v(z i)·v(N₁)⁻¹ ≤ v(N₁²)·v(N₁)⁻¹ = v(N₁) ≤ 1` —
     integral; multiply in via `includeRight_mem_localOrder` + `mul_mem`.
     (Scalar centrality: `(q:ℚ)•ζ = (1 ⊗ₜ algebraMap-image)·ζ` — `Algebra.smul_def`
     in the tensor algebra; rational scalars are central.)
   - `v = w`: `↑(g⁻¹)·(y⊗1) = (↑(g⁻¹)·ξ) − (↑(g⁻¹)·(ξ − y⊗1))`; first term `hξg`;
     second `= (N₁:ℚ)•(↑(g⁻¹)·δ)`… — CAREFUL: `↑(g⁻¹)·δ` alone need NOT be integral;
     use instead `(N₁:ℚ)•(↑(g⁻¹))·δ` grouping: `hN₁mem`-content at `w` times
     `δ ∈ localOrder w`: `mul_mem` ✓.  (`mul_smul_comm` to regroup.)
6. Assemble `⟨y, step5, δ, step4⟩`.

#### Mathlib lemmas needed
- `Set.Finite.union/toFinset`, `Finset.erase`; `TensorProduct.tmul_sub/sum_tmul`;
  `Algebra.smul_def`, `mul_smul_comm`, `smul_smul`; `pow_ne_zero`; `WithZero` order
  (`v(N₁²) ≤ v(N₁)` from `v(N₁) ≤ 1`); project lemmas per T04/T07/T11/T13.

#### Sources
decomposition.md L16 (quotes at N3/N4 heads; the `M := N₁²` slack analysis).

#### Generality decision
`hg` kept although derivable (T-definition convenience; recorded as acceptable
redundancy in decomposition.md L16 attack 3 — do not silently drop OR silently rely
on it beyond `T`'s construction).

---

### [CLEANUP-6] /cleanup PhD/JacobsSlash/CN1/4_Dictionary.lean (mid-file)
- **Status**: done (2026-08-10; 322→278 lines (−13.7%); gates 4/4, runLinter ZERO findings
  (hg-drop applied — exists_mem_latticeOf_sub_smul now takes only hN₁ + hN₁mem + ξ hyps);
  helpers consolidated: NEW mul_intCast_tmul_one single-sources the cast computation;
  valued_intCast_sq_le+valued_div_le_one MERGED into valued_div_intCast_le_one;
  rat_smul_eq_mul + intCast_smul_one deleted (aliases). Sorries now at :250/:260/:276.
  CharZero probes: NEITHER v.adicCompletion ℚ NOR hurwitzOrder has the instance.)
- **ORCHESTRATOR AUTHORIZATION**: drop the unused `hg` hypothesis from
  `exists_mem_latticeOf_sub_smul` (statement WEAKENING, strictly more general; zero call
  sites exist yet — T16 not yet written; removes the one linter finding). Adjust the
  docstring accordingly and remove the `set_option linter.unusedVariables false in` guard. | **Depends on**: T13, T14, T15 | **Type**: cleanup

---

### [T16] Prove `exists_eq_generator_mul`
- **Status**: done (2026-08-10, tail worker; verified by orchestrator: build green, only hClassNumberOne sorry remains at :325) | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean (after the
  approximation theorem)
- **Depends on**: T03, T14, T15, CLEANUP-6 | **Parallel**: no | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_eq_generator_mul {g : Dfx ℚ D}
    (hg : ∀ w, toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] 𝔸f) ∈ localOrder w)
    {x : hurwitzOrder} (hx : latticeOf g = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x})
    (w : HeightOneSpectrum (RingOfIntegers ℚ)) :
    ∃ ζ ∈ localOrder w, toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] 𝔸f)
      = ((x : D) ⊗ₜ[ℚ] 1) * ζ := by sorry
```

#### Proof sketch
[Voight 28.2.4's "ℒ̂ = αẐ² = α̂Ẑ²" step; expect ~60 LOC.]
1. Choose `N₁` via T12 at `↑(g⁻¹)` and `intCast_mem_latticeOf` (as in T14) —
   `hN₁mem : (N₁:𝓞) ∈ latticeOf g`, `N₁ ≠ 0`.
2. T15 at `ξ := toLocal w ↑g` (`hξ := hg w`; `hξg`: `↑(g⁻¹)·↑g`-image `= 1 ∈
   localOrder` — `Units.inv_mul`, `map_one`): get `y ∈ latticeOf g`, `δ`,
   `ξ = y⊗1 + (N₁:ℚ)•δ`.
3. `hx ▸` memberships: `y ∈ span{x}` ⟹ `y = x * s` (`mem_span_singleton`, `unop`);
   `(N₁:𝓞) ∈ span{x}` ⟹ `N₁ = x * s₀`.
4. `y⊗1 = (x⊗1)·(s⊗1)` (`tmul_mul_tmul`); `(N₁:ℚ)•δ = ((N₁:𝓞):D ⊗ₜ 1)·δ`-scalar
   bridge (centrality of the rational integer: `(N₁:D)⊗1` is central —
   `Algebra.smul_def`-route) `= (x⊗1)·(s₀⊗1)·δ`.
5. `ζ := (s⊗1) + (s₀⊗1)*δ ∈ localOrder w` (`tmul_mem_localOrder`-at-`1` +
   `mul_mem` + `add_mem`); `mul_add` collects.

#### Mathlib lemmas needed
- `Submodule.mem_span_singleton`, `Units.inv_mul`, `Algebra.smul_def`,
  `Algebra.TensorProduct.tmul_mul_tmul`, `mul_add`.

#### Sources
decomposition.md L17 (with [V 28.2.4] verbatim proof quote at N4-head).

---

### [T17] Prove `exists_factor_of_forall_mem`
- **Status**: done (2026-08-10, tail worker; verified by orchestrator: build green, only hClassNumberOne sorry remains at :325) | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean
- **Depends on**: T03, T14, T16 | **Parallel**: no | **Type**: theorem

#### Statement (in skeleton)
```lean
theorem exists_factor_of_forall_mem {g : Dfx ℚ D}
    (hg : ∀ w, toLocal ℚ D w ((g : Dfx ℚ D) : D ⊗[ℚ] 𝔸f) ∈ localOrder w) :
    ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U0, g = d * u := by sorry
```

#### Proof sketch
[Voight 27.6.8 + 28.2.4 assembly; expect ~70 LOC.]
1. T03 on `latticeOf g`: generator `x`.  `x ≠ 0`: else `span{0} = ⊥` contradicts T14.
2. `hx0 : (x:D) ≠ 0` (`Subtype` + coordinates); `xu : Dˣ := Units.mk0 (x:D) hx0`;
   `d := unitsIncl ℚ D xu ∈ globalUnits` (`MonoidHom.mem_range ⟨xu, rfl⟩`).
3. `u := d⁻¹ * g`; `g = d * u` by group algebra.
4. `u ∈ U0` (`U0`'s carrier, both conjuncts, at every `w`):
   - `toLocal w ↑u = toLocal w (↑(d⁻¹)) * toLocal w ↑g` (`Units.val_mul`, `map_mul`);
     `toLocal w ↑(d⁻¹) = (x:D)⁻¹ ⊗ₜ 1`-form via `map_inv` on units +
     `toLocal_unitsIncl`; with T16's `toLocal w ↑g = (x⊗1)·ζ`, cancel:
     `((x⁻¹)⊗1)·(x⊗1) = 1` (`tmul_mul_tmul`, `inv_mul_cancel₀ hx0`, `mul_one`);
     conclude `= ζ ∈ localOrder w`.
   - `toLocal w ↑(u⁻¹)`: `u⁻¹ = g⁻¹ * d`; `= toLocal w ↑(g⁻¹) * ((x:D) ⊗ₜ 1)` — this
     is `mem_latticeOf_iff.mp (x-mem)` where `x ∈ latticeOf g` comes from T03's span
     (`x ∈ span{x}`, `Submodule.mem_span_singleton_self`) transported by `hx.symm ▸`.
5. Package `⟨d, mem, u, hu, by group⟩`.

#### Mathlib lemmas needed
- `Units.mk0`, `inv_mul_cancel₀`, `MonoidHom.mem_range`,
  `Submodule.mem_span_singleton_self`, `map_inv`, `Units.val_mul`; project
  `toLocal_unitsIncl` (2_Level.lean:498).

#### Sources
decomposition.md L18; `U0` bookkeeping precedented at `unitsIncl_mem_U0_iff`
(2_Level.lean:538 — read it before starting).

---

**Progress (T16-T17, tail worker, 2026-08-10)**: both DONE first-try, std axioms, 6_Matrix
rebuilt green. NEW private base helper intCast_tmul_one (:77) — probe-verified it
GENERALISES to arbitrary [CommRing A][Algebra ℚ A] (incl. A = 𝔸f, giving L19's centrality
step ((N:𝓞):D)⊗ₜ1 * x = (N:ℚ)•x directly): T18 worker should generalise the binder, not
re-derive. T18 seams: U0/latticeOf memberships are definitional (∀w-∧ shape, intro w +
refine ⟨?_,?_⟩); globalUnits is a Subgroup (mul_mem (inv_mem _) _ probed ✓);
Units.val_inv_eq_inv_val + Units.val_mk0 + ← map_inv chain before toLocal_unitsIncl;
sub_eq_iff_eq_add' consumes T15's output; scratch-harness technique: copy file's first
~104 lines + state deps sorried = ~12s cycles vs ~80s.

---

### [CLEANUP-ALL-1] /cleanup-all on CN1 so far
- **Status**: done (2026-08-10; gates 5/5 incl. 11-decl axiom battery all std + downstream
  fork build; one_re-swap APPLIED (mathlib re_one family; NB deleted lemmas were @[simp] —
  downstream cone rebuilt green); 3 naked `;` fixed; imports all proven necessary by
  removal-test; duplication audit recorded — exact dup valued_intCast_ne_zero in
  3_LocalApprox+4_Dictionary (lift would need publicizing, out of scope), one_re quadruple
  remains in U3/2_Level:234-237 (outside CN1 — natural T19/follow-up note); 935→932 lines) | **Depends on**: CLEANUP-1, CLEANUP-3, CLEANUP-5, T17 | **Type**: cleanup
- Pre-milestone project-wide pass over the four CN1 files (cross-file dedup, import
  minimisation, shared-helper extraction).

---

### [T18] Prove `hClassNumberOne` — **MILESTONE**
- **Status**: done (2026-08-10 — THE MILESTONE. hClassNumberOne PROVEN. Orchestrator-verified:
  zero sorried declarations fork-wide, lake build green (3416 jobs, no warnings),
  #print axioms = [propext, Classical.choice, Quot.sound])
- **Worker final report (2026-08-11)**: proof body :326-344 (file 346 lines); six gates all
  explicit-PASS incl. runLinter (60 closure findings, ZERO in CN1 files) and char-accurate
  ≤100-col scan. Deviations from plan, all sound: (1) nD = Units.mk0 routed through
  hurwitzOrder cast so Units.val_mk0 lands on intCast_tmul_one's LHS; (2) nonzeroness by
  the coordinate route (congrArg re), no FaithfulSMul; (3) dN via the file's obtain-rfl
  idiom so hdN.symm is the range witness; (4) endgame rw [mul_assoc, ← heq,
  inv_mul_cancel_left]. Seam: intCast_tmul_one now general at [CommRing A][Algebra ℚ A]
  (rw-friendly, no (v := …) needed); rewrite ORDER in hg' matters — ← map_smul LAST or the
  scalar lands on the wrong side of toLocal. | **File**: PhD/JacobsSlash/CN1/4_Dictionary.lean (final theorem)
- **Depends on**: T12, T17, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem (milestone)

#### Statement (in skeleton)
```lean
theorem hClassNumberOne : HClassNumberOne := by sorry
```

#### Proof sketch
[[J] Lemma 1.22 via the [V] replacement; the reduction is [V 27.2.6]'s "denominators
can be handled globally"; expect ~50 LOC.]
1. `intro g`.  T12 at `↑g`: `N ≠ 0`, `(N:ℚ)•↑g` everywhere integral.
2. `nD : Dˣ := Units.mk0 ((N:ℚ) • (1:D)) (by …)` — or cleaner `algebraMap`-unit:
   `(N:ℚ) ≠ 0`, `Units.map`-of `Units.mk0 (N:ℚ)` through `algebraMap ℚ D`.
   `g' := unitsIncl ℚ D nD * g`.
3. `↑g' = (N:ℚ)•↑g`: `Units.val_mul` + `toLocal_unitsIncl`-shape at the tensor level:
   `((N:ℚ)•1 ⊗ₜ 1)·↑g = (N:ℚ)•↑g` (`Algebra.smul_def`, `one_mul`; rational scalars
   central).  Hence `hg' : ∀ w, toLocal w ↑g' ∈ localOrder w` from step 1
   (`map_smul` alignment).
4. T17 at `g'`: `g' = d·u`.  Then `g = (unitsIncl nD)⁻¹ * d * u`;
   `d' := (unitsIncl nD)⁻¹ * d ∈ globalUnits` (subgroup `inv_mem` + `mul_mem`;
   `unitsIncl`-naturality for the inverse: `map_inv`).
5. `exact ⟨d', mem, u, hu, by group⟩`.
6. **Post-fill gates** (part of this ticket): `#print axioms JacobsSlash.hClassNumberOne`
   must show exactly `[propext, Classical.choice, Quot.sound]`;
   `lake build PhD.JacobsSlash.U3.«9_EigenvaluesU3»` green;
   `grep -rn "sorry" PhD/JacobsSlash --include="*.lean"` shows ZERO sorried
   declarations (docstring mentions excepted).

#### Mathlib lemmas needed
- `Units.mk0`, `Units.map`, `map_inv`, `Subgroup.inv_mem/mul_mem`,
  `Algebra.smul_def`; everything else via T12/T17.

#### Sources
[J] Lemma 1.22 (verbatim quote in decomposition.md R); reduction template
[V 28.2.4 preamble] quote in decomposition.md L19.

#### Generality decision
The statement is fixed (`HClassNumberOne` def in 2_Level.lean:645) — do NOT touch the
`Prop`.

---

### [CLEANUP-7] /cleanup PhD/JacobsSlash/CN1/4_Dictionary.lean (final)
- **Status**: done (2026-08-11 — golfer: 346→336 lines, 7/7 golfs landed 0 reverted,
  new shared private helper coe_intCast_ne_zero dedups the no-CharZero coordinate route,
  hClassNumberOne proof 20→14 lines; gates: file diagnostics clean, 0 proof-sorries,
  build green + axioms std, downstream 6_Matrix green; runLinter 0 findings in-file;
  frozen docstrings untouched, no seam-rule violations) | **Depends on**: T18 | **Type**: cleanup

---

### [T19] Integration: retire the FLT-contract narrative
- **Status**: done (2026-08-10, orchestrator-executed. All 6 edit sites from the verified
  inventory: 1_Hurwitz status note, 2_Level header, 2_U3Data no-external-sorries,
  6_Matrix consumer docstring, PROGRESS.md (status/axiom-contract/file-map + CN1 table),
  legacy pointers (ClassNumberOneFallback SUPERSEDED header + qmf B06/B18 one-liners;
  no legacy file deleted). Gates: 30-module fork build green 3581 jobs; 0 sorries;
  eval_classRep_injective' axioms = [propext, Classical.choice, Quot.sound] — sorryAx
  GONE from the consumer chain) | **Files**: U3/2_Level.lean, U3/1_Hurwitz.lean, 2_U3Data.lean,
  U3/6_Matrix.lean, PROGRESS.md | **Depends on**: T18 | **Parallel**: with CLEANUP-7
- **Type**: docs/integration

#### Work items (each a small prose edit; grep first, edit surgically)
1. `U3/2_Level.lean` module docstring (~lines 24-38): rewrite the "FLT's
   `completed_units` … expected to cover it upstream … deliberately deferred"
   narrative: (1.4.4) is now PROVEN in `CN1/4_Dictionary.lean` by the Voight route;
   keep the historical note one sentence.
2. `U3/1_Hurwitz.lean` header "Status note (user decision 2026-08-05)" block
   (~lines 28-35): replace the deferral story with: the chain is DEVELOPED in
   `PhD/JacobsSlash/CN1/` (cancelled deferral 2026-08-10).
3. `2_U3Data.lean:119` "The one contracted external `sorry` is `hClassNumberOne`…":
   update — no external sorries remain.
4. `U3/6_Matrix.lean` (~line 286) "**Depends on the fork's single external `sorry`**"
   docstring on `eval_classRep_injective'`: now unconditional; also revisit whether
   the primed convenience form should simply cite `hClassNumberOne` proven (keep both
   forms; hypothesis-taking `eval_classRep_injective` stays).
5. `PhD/JacobsSlash/PROGRESS.md`: "Axiom contract" section — `hClassNumberOne` moves
   from "single external sorry" to proven (std axioms); "Status" header line ("the
   only `sorry` is the contracted FLT interface") updated; add a CN1 section to the
   file map (5 files, board pointer).
6. Legacy pointers: `PhD/Jacobs/U3/ClassNumberOneFallback.lean` header + the old
   qmf-board B06/B18 entries get a one-line "superseded by
   `.mathlib-quality/hurwitz-cn1/` (executed 2026-…)" note (do NOT delete legacy
   files — Keep-PR'd-history rule).
7. Gates: full `lake build` of the fork top (`U3/«9_EigenvaluesU3»`), zero sorried
   declarations in `PhD/JacobsSlash`, `#print axioms` re-run on the PROGRESS.md
   headline chain (all std).

---

### [CLEANUP-FINAL] /cleanup-all on the whole CN1 development
- **Status**: done (2026-08-11, orchestrator-executed final battery, all green:
  markers/trailing-ws sweeps zero; char-accurate line length ≤100 zero violations
  (awk byte-count false alarm re-confirmed); full 30-module fork build 3581 jobs;
  fork-wide proof-sorries 0; axiom battery 8/8 public CN1+consumer decls exactly
  [propext, Classical.choice, Quot.sound]; runLinter 0 in-file findings on all four
  CN1 modules) | **Depends on**: T19, CLEANUP-7 | **Type**: cleanup
- Final pass; then `/pre-submit`-style checks per house rules.

---

## Dependency graph (execution view)

```
T01 → T02 → T03 → CLEANUP-1 ──────────────┐
T04 ─┐                                    │
T05 ─┼→ CLEANUP-2 → T07 → CLEANUP-3 ──────┤
T06 ─┘                                    │
T08 ─┐                                    ├→ CLEANUP-ALL-1 → T18 → {CLEANUP-7, T19} → CLEANUP-FINAL
T09 → T10 ─┼→ CLEANUP-4 → {T11, T12} → CLEANUP-5 ─┤
           │                                      │
T13 → T14 ─┴──────→ T15 → CLEANUP-6 → T16 → T17 ──┘
(T15 also needs T04, T07, T11; T14 needs T12; T16 needs T03; T18 needs T12, T17)
```

Three independent start fronts: {T01}, {T04, T05, T06}, {T08, T09, T13}.
