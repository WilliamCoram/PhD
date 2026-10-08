# Ticket board: overconvergent automorphic forms, Layer 0 (the adelic setting)

Board: `.mathlib-quality/tauceti-of-layer0/` — **always name this board** (`/beastmode` on the default path
belongs to other runs). Plan: `plan.md`. Decomposition, with the section substrates, verbatim quotes and
attack logs: `decomposition.md`. B2 log: `b2_log.jsonl` (empty at creation).

Conventions. Code lives in `PhD/TauCeti/Code/OverconvergentForms/`; build a file with
`lake build PhD.TauCeti.Code.OverconvergentForms.<Dir>.<File>` and never `lake build PhD`; never import
`PhD.Main.*` — [SRC] is read for proof ideas only. Statements are fixed: they are in the skeleton, which
builds with `sorry` warnings only. A worker who finds a statement false or unprovable as written stops,
logs a B2 entry and does not edit the statement silently. `omega`, not `lia`. Lines at most 100
codepoints. macOS has no `timeout`. Private helper lemmas are at the worker's discretion; public ones
need a docstring. `[Module.Finite F D]` and similar instance hypotheses that a finished proof does not
use are removed, and the callers updated (run `lake exe runLinter` on the module at each cleanup).

Worker protocol. `/beastmode` inline as the main agent, one ticket at a time in board order; cleanup
tickets are `/cleanup` inline, never dispatched to subagents. Mark a ticket `done` only when its file
builds and the named declarations are sorry-free.

## Summary

| Kind | Count |
|---|---|
| Proof and definition tickets | 82 |
| Per-file cleanup tickets | 34 |
| `CLEANUP-ALL` before milestones | 2 |
| Milestones | 2 |
| `CLEANUP-FINAL` | 1 |
| **Total** | **121** |

Next ticket: **none — board COMPLETE 2026-10-01 (121/121)**.

## Dependency order

- **G1** Quaternion algebras (§0.1): T001, T002, T003, T004, T005, T006, T007, T008, T009, T010, T013, T014, T015
- **G2** Right base change and the finite adeles: T011, T012, T016, T017, T018, T019
- **G3** The adelic group (§0.2.1–3): T020–T031
- **G4** The norm class (§0.2.4): T032–T036
- **G5** The local level (§0.4.1–2): T037–T043
- **G6** Standard levels (§0.3.1): T044–T046
- **G7** Class sets (§0.3.2–3): T047–T051
- **G8** The Hecke pair (§0.3.4, §0.4.3–5): T052–T057
- **G9** Hamilton: splitting, setting, level: T058–T066
- **G10** Class number one (§0.3.5): T067–T070
- **G11** The class set of `U₁(9)`: T071–T075
- **G12** The `η`-decomposition, the factorisations, the examples: T076–T082

G1, G2 and G5 are independent. `CLEANUP-ALL-1` and milestone **M1** close the general theory (G1–G8);
`CLEANUP-ALL-2`, **M2** and `CLEANUP-FINAL` close the board.

---

### [T001] `trd`, `nrd`, `trd_apply` and 8 more

- **Status**: done   (finished 2026-09-22) · **File**: `Quaternion/ReducedNorm.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L1.1, L1.2, L1.8, L1.9

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def trd : ℍ[R,a,b] →ₗ[R] R where
  toFun x := 2 * x.re
  map_add' := by sorry
  map_smul' := by sorry
def nrd : ℍ[R,a,b] →*₀ R where
  toFun x := x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2
  map_zero' := by sorry
  map_one' := by sorry
  map_mul' := by sorry
theorem trd_apply (x : ℍ[R,a,b]) : trd x = 2 * x.re := rfl
theorem nrd_apply (x : ℍ[R,a,b]) :
    nrd x = x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 := rfl
theorem coe_nrd (x : ℍ[R,a,b]) : ((nrd x : R) : ℍ[R,a,b]) = x * star x := by
  sorry
theorem coe_nrd' (x : ℍ[R,a,b]) : ((nrd x : R) : ℍ[R,a,b]) = star x * x := by
  sorry
theorem coe_trd (x : ℍ[R,a,b]) : ((trd x : R) : ℍ[R,a,b]) = x + star x := by
  sorry
def mapRingHom (f : R →+* S) (a b : R) : ℍ[R,a,b] →+* ℍ[S,f a,f b] where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry
theorem nrd_mapRingHom (f : R →+* S) (x : ℍ[R,a,b]) : nrd (mapRingHom f a b x) = f (nrd x) := by
  sorry
theorem trd_mapRingHom (f : R →+* S) (x : ℍ[R,a,b]) : trd (mapRingHom f a b x) = f (trd x) := by
  sorry
theorem nrd_eq_normSq (x : ℍ[R]) : QuaternionAlgebra.nrd x = normSq x := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.1** `trd`, `nrd` (fields), `trd_apply`, `nrd_apply` — [RM] §0.1.1 "Define the *reduced norm*
  `nrd : D → F` and *reduced trace* […] state the theory for `ℍ[F, a, b]` first". Lean:
  `trd : ℍ[R,a,b] →ₗ[R] R`, `nrd : ℍ[R,a,b] →*₀ R` with the explicit formulas. Match: the formula is
  [Voi21, 3.2.9]'s `α ᾱ`, expanded (substrate). Discharge: `map_add'`, `map_smul'` by `simp` +
  `ring`; `map_mul'` is a polynomial identity in eight variables: `simp [QuaternionAlgebra.mul_re, …]`
  then `ring`. Attacks: [1] is `nrd` multiplicative over a ring where `2` is not invertible? Yes: the
  identity is polynomial over `ℤ[a, b]`, no division ✓. [2] `R` the zero ring: `→*₀` needs
  `map_one`, `1 = 0` there, holds ✓. `a = 0`: `nrd = re² − b·imJ²`, still multiplicative (degenerate
  algebra) ✓. [3] no hypotheses. [4] Mathlib's general `ℍ[R,c₁,c₂,c₃]` has `c₂ ≠ 0` with
  `star x = ⟨re + c₂ imI, …⟩`; the two-parameter notation fixes `c₂ = 0`, which is the roadmap's
  `(a, b / F)` ✓. [5] `QuaternionAlgebra.mul_re` etc. are `simp` lemmas ✓. SURVIVED.

- **L1.2** `coe_nrd`, `coe_nrd'`, `coe_trd` — [RM] §0.1.1 "`nrd(x) = x x̄` for the canonical
  involution". Lean: `((nrd x : R) : ℍ[R,a,b]) = x * star x`, `= star x * x`, and
  `((trd x : R) : ℍ[R,a,b]) = x + star x`. Discharge: `ext <;> simp <;> ring`. Attacks: [2] the three
  imaginary coordinates of `x * star x` must vanish identically: `imK` is
  `re·(−imK) + imI·(−imJ) − imJ·(−imI) + imK·re = 0` ✓. [4] Mathlib has
  `QuaternionAlgebra.star_mul_eq_coe` (`star a * a = (star a * a).re`); ours identifies that real
  part ✓. [5] verified. SURVIVED.

- **L1.8** `mapRingHom` (fields), `nrd_mapRingHom`, `trd_mapRingHom` — change of coefficients along
  `f : R →+* S`, target `ℍ[S, f a, f b]`. Discharge: `ext <;> simp`. Attacks: [4] the target type
  carries `f a`, `f b`, not `a`, `b`; L3.1 is stated with `algebraMap F R a` accordingly ✓.
  SURVIVED.

- **L1.9** `Quaternion.nrd_eq_normSq` — [RM] §0.1.1 "where `nrd = normSq`". Discharge:
  `Quaternion.normSq_def'` + `simp [nrd_apply]` + `ring`. Attacks: [2] `ℍ[R]` is the *definition*
  `ℍ[R,-1,0,-1]`; the statement elaborated in the skeleton, so the unfolding is available ✓.
  SURVIVED.

#### Mathlib lemmas needed

`map_add'`, `map_smul'`, `map_mul'`, `map_one`, `QuaternionAlgebra.mul_re`, `QuaternionAlgebra.star_mul_eq_coe`, `Quaternion.normSq_def'`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.1 (module docstring: §0.1.1).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-22: stated nothing new — the skeleton statements were used verbatim. Name corrections
  against the sketch: Mathlib's component-of-operation simp lemmas are `re_mul`, `imI_mul`,
  `imJ_mul`, `imK_mul` (NOT `mul_re` etc. as the sketch said); `re_star`, `imI_star`, … likewise.
- 2026-09-22: `coe_nrd` / `coe_nrd'` are not provable by `ext <;> simp <;> ring` — `simp` pushes the
  `R → ℍ[R,a,b]` coercion inside the arithmetic and strands `(↑x.re ^ 2).re`. Route used instead:
  `rw [mul_star_eq_coe]` (resp. `star_mul_eq_coe`), `congr 1`, then `simp only [nrd_apply, re_mul,
  re_star, imI_star, imJ_star, imK_star]; ring`. `coe_trd` goes by `rw [self_add_star', trd_apply]`.
- 2026-09-22: `Quaternion.nrd_eq_normSq` — `simp`/`rw` cannot fire `nrd_apply` through
  `Quaternion R` (a `def`, not reducible, so the unifier will not unfold it to `ℍ[R,-1,0,-1]`).
  Discharged with an explicit `have … := rfl` at default transparency, then `normSq_def'` + `ring`.
- 2026-09-22: DONE — all 11 declarations proven, `lake build
  PhD.TauCeti.Code.OverconvergentForms.Quaternion.ReducedNorm` clean, `#print axioms` standard
  (`propext`, `Quot.sound`, `Classical.choice`) on every one.

### [T002] `nrd_star`, `trd_star`, `nrd_coe` and 5 more

- **Status**: done   (finished 2026-09-22) · **File**: `Quaternion/ReducedNorm.lean` · **Depends on**: [T001] · **Type**: proof · **Leaves**: L1.3, L1.4, L1.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem nrd_star (x : ℍ[R,a,b]) : nrd (star x) = nrd x := by
  sorry
theorem trd_star (x : ℍ[R,a,b]) : trd (star x) = trd x := by
  sorry
theorem nrd_coe (r : R) : nrd (r : ℍ[R,a,b]) = r ^ 2 := by
  sorry
theorem trd_coe (r : R) : trd (r : ℍ[R,a,b]) = 2 * r := by
  sorry
theorem nrd_smul (r : R) (x : ℍ[R,a,b]) : nrd (r • x) = r ^ 2 * nrd x := by
  sorry
theorem nrd_add (x y : ℍ[R,a,b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  sorry
theorem mul_self_eq (x : ℍ[R,a,b]) : x * x = trd x • x - nrd x • (1 : ℍ[R,a,b]) := by
  sorry
theorem isUnit_iff_isUnit_nrd {x : ℍ[R,a,b]} : IsUnit x ↔ IsUnit (nrd x) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.3** `nrd_star`, `trd_star`, `nrd_coe`, `trd_coe`, `nrd_smul`, `nrd_add` — API. `nrd_add` is
  the polarisation `nrd (x + y) = nrd x + nrd y + trd (x * star y)`. Discharge: `simp [nrd_apply]` +
  `ring`. Attacks: [1] `nrd_add` with `x = y`: `nrd(2x) = 4 nrd x = 2 nrd x + trd(x x̄) = 2 nrd x +
  2 nrd x` ✓. [3] none. SURVIVED.

- **L1.4** `mul_self_eq` — the quadratic relation `x * x = trd x • x − nrd x • 1`. Discharge:
  `ext <;> simp <;> ring`. Attacks: [2] `x = r` scalar: `r² = 2r·r − r²` ✓. SURVIVED.

- **L1.5** `isUnit_iff_isUnit_nrd` — [RM] §0.1.1 "`D^× = {x | nrd x ≠ 0}` when `D` is a division
  algebra". Lean: `IsUnit x ↔ IsUnit (nrd x)`, over any commutative ring. Sketch: (→) `nrd` is a
  monoid homomorphism; (←) `x * ((↑u⁻¹ : R) • star x) = 1` by `coe_nrd`, and the other side by
  `coe_nrd'`. Attacks: [1] over a ring with zero divisors, `nrd x` a non-unit non-zero-divisor:
  both sides false ✓. [3] commutativity of `R` is used (central scalars). [4] stronger than the
  roadmap's field statement, which is the case `IsUnit r ↔ r ≠ 0`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.1 (module docstring: §0.1.1).
- Literature: the quotations of the module docstring of `Quaternion/ReducedNorm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-22: DONE on the first build. `nrd_star`, `trd_star`, `nrd_smul`, `nrd_add` by
  `simp only [nrd_apply/trd_apply, re_*/imI_*/… component lemmas]; ring`; `nrd_coe`, `trd_coe` by
  `simp`; `mul_self_eq` by `ext <;> simp [trd_apply, nrd_apply] <;> ring`. `isUnit_iff_isUnit_nrd`:
  (→) `h.map nrd`; (←) the explicit unit `⟨x, ↑u⁻¹ • star x, _, _⟩`, both sides by `mul_smul_comm` /
  `smul_mul_assoc`, `← coe_nrd` / `← coe_nrd'`, `smul_coe`, `Units.inv_mul`, `coe_one` — no
  commutativity of `ℍ` needed (`isUnit_of_mul_eq_one` would need it). Axioms standard.

### [T003] `trace_map_eq_trd`, `det_map_eq_nrd`

- **Status**: done   (finished 2026-09-22) · **File**: `Quaternion/ReducedNorm.lean` · **Depends on**: [T002] · **Type**: proof · **Leaves**: L1.6, L1.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem trace_map_eq_trd (φ : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) S) (h2 : IsUnit (2 : S))
    (ha : IsUnit (algebraMap R S a)) (hb : IsUnit (algebraMap R S b)) (x : ℍ[R,a,b]) :
    (φ x).trace = algebraMap R S (trd x) := by
  sorry
theorem det_map_eq_nrd (φ : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) S) (h2 : IsUnit (2 : S))
    (ha : IsUnit (algebraMap R S a)) (hb : IsUnit (algebraMap R S b)) (x : ℍ[R,a,b]) :
    (φ x).det = algebraMap R S (nrd x) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.6** `trace_map_eq_trd` — [RM] §0.1.1 "prove they are independent of the splitting". Lean:
  for `φ : ℍ[R,a,b] →ₐ[R] M₂(S)` and `IsUnit 2`, `IsUnit (algebraMap a)`, `IsUnit (algebraMap b)` in
  `S`: `(φ x).trace = algebraMap R S (trd x)`. Sketch: substrate, second paragraph. Attacks: [1] a
  homomorphism with `φ i` scalar? Then `IJ = −JI` forces `2 (φ i) J = 0`, so `φ i = 0`, contradicting
  `(φ i)² = a` invertible — no such `φ` exists, consistent ✓. [3] each unit hypothesis is used once
  (`2`: twice; `b`: to cancel `J`; `a`: to cancel `I`); over `S = 𝔽₂` the statement fails for
  `ℍ[𝔽₂,1,1]` (commutative image), so `IsUnit 2` is necessary ✓. [4] the roadmap says "determinant and
  trace of the left-regular representation on any splitting"; ours is for every homomorphism, a
  splitting being the bijective case ✓. [5] `Matrix.trace_fin_two`, `Matrix.det_fin_two`; the
  `2 × 2` Cayley–Hamilton identity by `Matrix.ext` + `ring`, no `charpoly` needed. SURVIVED.

- **L1.7** `det_map_eq_nrd` — same hypotheses, `(φ x).det = algebraMap R S (nrd x)`. Sketch: L1.4
  under `φ`, L1.6, and the `(0,0)` entry of `(det − nrd)·1 = 0`. Attacks: [2] `x = 1`: `det 1 = 1`
  ✓. [4] this is [RM] §0.1.3's "`det (θ_𝔭 x) = nrd x`" before base change. SURVIVED.

#### Mathlib lemmas needed

`Matrix.trace_fin_two`, `Matrix.det_fin_two`, `Matrix.ext`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.1, §0.1.3 (module docstring: §0.1.1).
- Literature: the quotations of the module docstring of `Quaternion/ReducedNorm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-22: four private helpers added in `section Splitting` (worker's discretion):
  `algebraMap_matrix_eq_smul_one`, `mul_self_eq_trace_smul_sub_det_smul` (2 × 2 Cayley–Hamilton by
  `fin_cases` + `simp` + `ring`; Mathlib has no `charpoly_fin_two`), `exists_mul_eq_one_of_
  mul_self_eq_smul_one` (a two-sided inverse `u⁻¹ • M` from `M * M = u • 1`, so no
  `Matrix.mul_eq_one_comm` is needed), and `trace_eq_zero_of_anticommute` (the conjugation trick
  `tr M = tr (N' N M) = tr (N M N') = −tr M`, then cancel the unit `2`).
- 2026-09-22: `trace_map_eq_trd`: `I = φ i`, `J = φ j` are invertible (`I² = a`, `J² = b`); `I`, `J`,
  `K = φ k` each anticommute with an invertible one (`ji = −ij`, `ik = −ki`), so all three traces
  vanish; decompose `x = re + imI·i + imJ·j + imK·k`. `det_map_eq_nrd`: `mul_self_eq` under `φ` and
  Cayley–Hamilton with the trace identity give `det • 1 = nrd • 1`; read off entry `(0, 0)`.
- 2026-09-22: DONE — file sorry-free, `lake build …Quaternion.ReducedNorm` clean with no warnings,
  axioms standard.

### [CLEANUP-1] `/cleanup` of `Quaternion/ReducedNorm.lean` (final for the file)

- **Status**: done   (finished 2026-09-22) · **File**: `Quaternion/ReducedNorm.lean` · **Depends on**: [T003] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

_(none)_

#### Progress

- 2026-09-22: 258 → 232 lines. Module docstring now lists `mapRingHom`, `nrd_add` and
  `Quaternion.nrd_eq_normSq`. Mathlib replacement found: `coe_nrd'` is
  `(coe_nrd x).trans (star_comm_self' x).symm` (`ℍ[R,c₁,c₂,c₃]` carries `IsStarNormal`), so its
  five-line proof went. `nrd_star` / `trd_star` collapse to terminal `simp [nrd_apply]` /
  `simp [trd_apply]`. `fun _ =>` → `fun _ ↦`.
- 2026-09-22: STRUCTURE — `trace_map_eq_trd`'s 38-line body held three copies of one skeleton.
  Factored into the private `trace_map_eq_zero_of_anticommute` (φ of an element anticommuting with
  one whose square is a unit scalar has trace zero); the body is now 17 lines and `hI`/`hJ`/`hK`
  are one call each. `trace_eq_zero_of_anticommute` lost its docstring (private) and its
  `h0`/`mul_left_cancel` tail, now `h2.mul_right_eq_zero.mp (by linear_combination key)`;
  `det_map_eq_nrd` dropped `hq`/`key` for one `rw … at hCH` plus `sub_right_inj.mp`.
- 2026-09-22: gates — `lake build` of the module clean with NO warnings; `lake exe runLinter` on
  the module passes; 0 lines over 100 codepoints; no `sorry`, `set_option`, `λ`, `$`, `push_neg`
  or in-file `/-! ##` dividers; both dependents (`Quaternion/BaseChange.lean`,
  `Quaternion/Definite.lean`) still build.
- 2026-09-22: NOTE for every later cleanup ticket — `lake build PhD.TauCeti` is NOT a usable gate
  on this board: the chain root imports only `NewtonPolygons`, and a PARALLEL agent is editing
  `PhD/TauCeti/Code/NewtonPolygons/` live (Slope.lean and ConvexSeq.lean churned during this
  session), so that target fails for reasons unrelated to this board. Gate on the module plus its
  importers instead. The `/simplify` hand-off was done inline for the same reason (its default
  scope is the working-tree diff, which currently holds the other agent's files): outcome
  PASS-THROUGH, no duplicated skeletons left after the factoring above.

### [T004] `IsTotallyDefinite`, `nrd_pos`, `isTotallyDefinite_iff_nrd_pos` and 3 more

- **Status**: done   (finished 2026-09-22) · **File**: `Quaternion/Definite.lean` · **Depends on**: [T003] · **Type**: proof · **Leaves**: L2.1, L2.2, L2.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def IsTotallyDefinite (a b : F) : Prop :=
  ∀ σ : F →+* ℝ, σ a < 0 ∧ σ b < 0
theorem IsTotallyDefinite.nrd_pos (h : IsTotallyDefinite a b) (σ : F →+* ℝ) {x : ℍ[F,a,b]}
    (hx : x ≠ 0) : 0 < σ (nrd x) := by
  sorry
theorem isTotallyDefinite_iff_nrd_pos :
    IsTotallyDefinite a b ↔ ∀ σ : F →+* ℝ, ∀ x : ℍ[F,a,b], x ≠ 0 → 0 < σ (nrd x) := by
  sorry
theorem IsTotallyDefinite.nrd_ne_zero [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b)
    {x : ℍ[F,a,b]} (hx : x ≠ 0) : nrd x ≠ 0 := by
  sorry
theorem IsTotallyDefinite.isUnit_iff [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b)
    {x : ℍ[F,a,b]} : IsUnit x ↔ x ≠ 0 := by
  sorry
abbrev IsTotallyDefinite.divisionRing [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b) :
    DivisionRing ℍ[F,a,b] :=
  { (inferInstance : Ring ℍ[F,a,b]) with
    inv := fun x ↦ (nrd x)⁻¹ • star x
    exists_pair_ne := by sorry
    mul_inv_cancel := by sorry
    inv_zero := by sorry
    nnqsmul := _
    nnqsmul_def := fun _ _ ↦ rfl
    qsmul := _
    qsmul_def := fun _ _ ↦ rfl }
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.1** `IsTotallyDefinite`, `IsTotallyDefinite.nrd_pos` — [RM] §0.1.2 "`D` is *totally definite*
  if `D ⊗_F F_v` is a division algebra at every real place `v` of `F` […] define the predicate
  `IsTotallyDefinite F D` through the real embeddings of `F`"; [Buz07, p. 67] (`buzzard.txt:2620`):
  "let `D` be a quaternion algebra over `F` ramified at all infinite places." Lean:
  `IsTotallyDefinite a b := ∀ σ : F →+* ℝ, σ a < 0 ∧ σ b < 0`; `0 < σ (nrd x)` for `x ≠ 0`. Sketch:
  substrate, third paragraph; `σ` is injective (field homomorphism). Attacks: [1] is `σ a < 0 ∧
  σ b < 0` the right definiteness condition? `(a, b | ℝ) ≅ ℍ` iff `a, b < 0` ✓ (`(1, −1 | ℝ)` and
  `(−1, 1 | ℝ)` are split). [2] a field with no real embedding (`F = ℚ(i)`): the predicate is
  vacuously true, and the consequences below take `[Nonempty (F →+* ℝ)]` ✓. [4] **drift recorded**:
  the roadmap names `NumberField.InfinitePlace.IsReal`; ring homomorphisms `F →+* ℝ` are equivalent
  for a number field and need no `NumberField` instance — plan.md, scope boundary. SURVIVED.

- **L2.2** `isTotallyDefinite_iff_nrd_pos` — the intrinsic form. (←): `x = i` gives `σ(−a) > 0`,
  `x = j` gives `σ(−b) > 0`. Attacks: [3] no `Nonempty` needed (both sides quantify over `σ`) ✓.
  SURVIVED.

- **L2.3** `IsTotallyDefinite.nrd_ne_zero`, `.isUnit_iff`, `.divisionRing` — [RM] §0.1.2 "Prove that
  `D` is then a division algebra". Sketch: L2.1 at some `σ`, then L1.5. `divisionRing` is an
  `abbrev` with `inv x = (nrd x)⁻¹ • star x`. Attacks: [3] `Nonempty (F →+* ℝ)` is necessary:
  `(−1, −1 | ℚ(i)) ≅ M₂` is vacuously "totally definite" and not a division ring ✓ (this is why the
  hypothesis is explicit). [4] for `ℍ[ℚ]` Mathlib already has a `DivisionRing` instance; ours is an
  `abbrev`, never an instance, so no diamond ✓. SURVIVED.

#### Mathlib lemmas needed

`NumberField.InfinitePlace.IsReal`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.2 (module docstring: §0.1.2).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-22: DONE on the first build, all five declarations sorry-free, axioms standard.
  `nrd_pos`: `σ (nrd x) = σ re² + (−σ a)·σ imI² + (−σ b)·σ imJ² + (σ a · σ b)·σ imK²` by
  `simp only [nrd_apply, map_add, map_sub, map_mul, map_pow]; ring`; the three non-leading
  coefficients are positive (`mul_pos_of_neg_of_neg`), a component is nonzero by `by_contra` +
  `not_or`/`not_not` (no `push_neg`), and each of the four cases closes by `linarith` with one
  strict term — readable-arithmetic style, no `nlinarith`. `σ` injective via `RingHom.injective`.
- 2026-09-22: `isTotallyDefinite_iff_nrd_pos` (←) tests `i` and `j`: `nrd ⟨0,1,0,0⟩ = -a`,
  `nrd ⟨0,0,1,0⟩ = -b`. `isUnit_iff` (→) is `isUnit_zero_iff` + `zero_ne_one`, NOT
  `IsUnit.ne_zero` (`ℍ[F,a,b]` has no `NoZeroDivisors` instance before the division ring exists).
  `divisionRing`: the three fields are `⟨0, 1, zero_ne_one⟩`, `show x * ((nrd x)⁻¹ • star x) = 1`
  then `mul_smul_comm`/`← coe_nrd`/`smul_coe`/`inv_mul_cancel₀`/`coe_one`, and `simp` after a
  `show`; the `show` is needed because the `inv` field is the one being defined.

### [T005] `exists_int_trd_of_fg`, `exists_int_nrd_of_fg`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Definite.lean` · **Depends on**: [T004] · **Type**: proof · **Leaves**: L2.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_int_trd_of_fg {a b : ℚ} (h : IsTotallyDefinite a b) {S : Subring ℍ[ℚ,a,b]}
    (hS : S.toAddSubgroup.FG) {x : ℍ[ℚ,a,b]} (hx : x ∈ S) : ∃ t : ℤ, trd x = (t : ℚ) := by
  sorry
theorem exists_int_nrd_of_fg {a b : ℚ} (h : IsTotallyDefinite a b) {S : Subring ℍ[ℚ,a,b]}
    (hS : S.toAddSubgroup.FG) {x : ℍ[ℚ,a,b]} (hx : x ∈ S) : ∃ n : ℤ, nrd x = (n : ℚ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.4** `exists_int_trd_of_fg`, `exists_int_nrd_of_fg` — [Voi21, Lemma 11.1.2, proof]: "by
  Corollary 10.3.6 we have `t ∈ ½ℤ`" (elements of an order are integral). Lean: for `a b : ℚ`
  totally definite, `S : Subring ℍ[ℚ,a,b]` with `S.toAddSubgroup.FG`, `x ∈ S`: `trd x` and `nrd x`
  are integers. Sketch: `ℤ[x] ⊆ S` is a finitely generated `ℤ`-module (submodule of a f.g. module
  over a Noetherian ring), so `x` is integral over `ℤ`. If `x ∈ ℚ` then `x ∈ ℤ` (integrally closed)
  and `trd = 2x`, `nrd = x²`. Otherwise the minimal polynomial of `x` over `ℚ` is
  `X² − trd(x) X + nrd(x)` (it divides it by L1.4, and has degree `≥ 2`; irreducibility is not
  needed, only that a monic integral polynomial killing `x` exists and that `ℚ[x]` is a field, the
  algebra being a division ring by L2.3), and integrality puts its coefficients in `ℤ`. Attacks:
  [1] a split algebra has orders with non-scalar nilpotents, where `ℚ[x]` is not a field — excluded
  by definiteness, which is why the hypothesis is there ✓. [3] `FG` as an abelian group is the
  roadmap's "lattice". [5] `IsIntegral.of_finite` needs a commutative coefficient ring and works in
  the commutative subring `Algebra.adjoin ℤ {x}`; `minpoly.isIntegrallyClosed_eq_field_fractions'`
  is for a commutative domain — apply it inside `Algebra.adjoin ℚ {x}` — **flagged for the ticket**,
  with the fallback "the monic integer polynomial killing `x` has `X² − trd X + nrd` as a factor over
  `ℚ`; Gauss's lemma (`Polynomial.IsPrimitive`…) gives integer coefficients". SURVIVED.

#### Mathlib lemmas needed

`S.toAddSubgroup.FG`, `IsIntegral.of_finite`, `minpoly.isIntegrallyClosed_eq_field_fractions'`, `Polynomial.IsPrimitive`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.2).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-22: the sketch's minpoly + Gauss route was REPLACED (it needs `minpoly` over a
  commutative ring, and `ℍ[F,a,b]` is not commutative). Route actually used, four private
  helpers: (1) `isIntegral_of_mem_of_fg` — `IsIntegral.of_mem_of_fg` accepts a NONcommutative
  ambient `[Ring B]`, so `subalgebraOfSubring S` + `Submodule.fg_iff_addSubgroup_fg` gives
  `IsIntegral ℤ x` straight from `S.toAddSubgroup.FG`; (2) `isIntegral_star` — `star` is an
  anti-automorphism fixing `ℤ`, so it preserves integrality (`Polynomial.induction_on'` on the
  witness, `star_mul`/`star_pow`/`star_intCast` and `Int.cast_commute`); (3)
  `isIntegral_of_mem_closure_pair` — for two COMMUTING integral elements, every element of
  `Subring.closure {x, y}` is integral, proved by `Subring.closure_induction` inside the
  commutative subring; (4) `isIntegral_trd` / `isIntegral_nrd` — `coe_trd` / `coe_nrd` put
  `trd x`, `nrd x` in that closure (`x` and `star x` commute by `coe_nrd`/`coe_nrd'`), then
  descend along the injective `(Algebra.ofId F ℍ[F,a,b]).restrictScalars ℤ`.
  `IsIntegrallyClosed.isIntegral_iff` finishes over `ℤ ⊆ ℚ`.
- 2026-09-22: TRAP (cost ~3 h of builds) — the `[Ring R] [IsMulCommutative R] → CommRing R`
  instances in `Mathlib/Algebra/Ring/Defs.lean` are **scoped**. Without
  `open scoped IsMulCommutative in`, `Subring.isMulCommutative_closure` gives you
  `IsMulCommutative ↥(closure s)` but `IsIntegral.add`/`mul` still fail with an
  "Application type mismatch … CommRing.toRing ?m" because no `CommRing` instance can be
  synthesised. `Subring.closureCommRingOfComm` is deprecated and has the same requirement.
- 2026-09-22: FINDING for CLEANUP-2 — neither `exists_int_trd_of_fg` nor `exists_int_nrd_of_fg`
  uses its `h : IsTotallyDefinite a b` hypothesis, and `#lint` flags it. The route above needs
  no definiteness at all (the sketch's attack log assumed the minpoly route, where a split
  algebra with nilpotents would break `ℚ[x]` being a field). The statements are ticketed and so
  were NOT edited; CLEANUP-2 is where "removal of unused hypotheses with their callers updated"
  is authorised. The general fact is: for any subring of `ℍ[ℚ,a,b]` that is f.g. as an abelian
  group, every element has integral reduced trace and norm.

### [T006] `nonempty_ringHom_real`, `isTotallyDefinite_hamilton`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Definite.lean` · **Depends on**: [T005] · **Type**: proof · **Leaves**: L2.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem nonempty_ringHom_real [NumberField F] [NumberField.IsTotallyReal F] :
    Nonempty (F →+* ℝ) := by
  sorry
theorem isTotallyDefinite_hamilton : IsTotallyDefinite (-1 : ℚ) (-1) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.5** `nonempty_ringHom_real`, `isTotallyDefinite_hamilton` — a totally real number field has a
  real embedding (`NumberField.ComplexEmbedding.IsReal.embedding` at any infinite place);
  `(−1, −1 | ℚ)` is totally definite (`map_neg`, `map_one`, `neg_one_lt_zero`). SURVIVED.

#### Mathlib lemmas needed

`NumberField.ComplexEmbedding.IsReal.embedding`, `map_neg`, `map_one`, `neg_one_lt_zero`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.2).
- Literature: the quotations of the module docstring of `Quaternion/Definite.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-23: DONE. `nonempty_ringHom_real`: `Nonempty (F →+* ℂ)` is an instance for a number
  field, and `NumberField.IsTotallyReal.complexEmbedding_isReal φ` then gives
  `ComplexEmbedding.IsReal φ`, whose `.embedding` is the `F →+* ℝ`.
  `isTotallyDefinite_hamilton`: `intro σ; constructor <;> norm_num`.

### [CLEANUP-2] `/cleanup` of `Quaternion/Definite.lean` (final for the file)

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Definite.lean` · **Depends on**: [T006] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

_(none)_

#### Progress

- 2026-09-23: module docstring now lists `IsTotallyDefinite.nrd_pos` and `nonempty_ringHom_real`;
  docstring added to `nrd_ne_zero`. Factored the duplicated tail of `isIntegral_trd` /
  `isIntegral_nrd` into two private one-liners, `isIntegral_of_coe` (descent along the injective
  `(Algebra.ofId F ℍ[F,a,b]).restrictScalars ℤ`) and `isIntegral_of_mem_closure_star`.
- 2026-09-23: **statement change, authorised by this ticket** — the unused
  `h : IsTotallyDefinite a b` was removed from `exists_int_trd_of_fg` and `exists_int_nrd_of_fg`
  (no call sites yet; `#lint`/`unusedVariables` flagged both). They now read: for any subring of
  `ℍ[ℚ,a,b]` finitely generated as an abelian group, every element has integral reduced trace and
  norm — strictly more general, definiteness is not needed for integrality.
- 2026-09-23: `lake build …Quaternion.Definite` clean, no warnings, 0 sorries.

### [T007] `IsHurwitz`, `hurwitzOrder`, `mem_hurwitzOrder_iff` and 5 more

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [T006] · **Type**: proof · **Leaves**: L4.1, L4.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def IsHurwitz (x : ℍ[ℚ]) : Prop :=
  ∃ A B C D : ℤ, x.re = (A : ℚ) / 2 ∧ x.imI = (B : ℚ) / 2 ∧ x.imJ = (C : ℚ) / 2 ∧
    x.imK = (D : ℚ) / 2 ∧ A % 2 = B % 2 ∧ B % 2 = C % 2 ∧ C % 2 = D % 2
def hurwitzOrder : Subring ℍ[ℚ] where
  carrier := {x | IsHurwitz x}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
theorem mem_hurwitzOrder_iff {x : ℍ[ℚ]} : x ∈ hurwitzOrder ↔ IsHurwitz x := Iff.rfl
def hurwitzOmega : ℍ[ℚ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩
theorem mem_hurwitzOrder_iff_exists_int {x : ℍ[ℚ]} :
    x ∈ hurwitzOrder ↔ ∃ n₀ n₁ n₂ n₃ : ℤ,
      x = (n₀ : ℍ[ℚ]) + (n₁ : ℍ[ℚ]) * ⟨0, 1, 0, 0⟩ + (n₂ : ℍ[ℚ]) * ⟨0, 0, 1, 0⟩ +
        (n₃ : ℍ[ℚ]) * hurwitzOmega := by
  sorry
theorem star_mem_hurwitzOrder {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : star x ∈ hurwitzOrder := by
  sorry
theorem exists_nrd_eq_natCast {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : ∃ n : ℕ, nrd x = (n : ℚ) := by
  sorry
theorem exists_trd_eq_intCast {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : ∃ n : ℤ, trd x = (n : ℚ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.1** `IsHurwitz`, `hurwitzOrder` (fields), `mem_hurwitzOrder_iff`, `hurwitzOmega`,
  `mem_hurwitzOrder_iff_exists_int` — [RM] §0.1.4 "Define the Hurwitz order
  `ℤ⟨i, j, (1 + i + j + k)/2⟩ ⊆ ℍ[ℚ]`". Lean: the subring of quaternions whose doubled coordinates
  are integers of one parity; `x ∈ 𝒪 ↔ ∃ n₀ n₁ n₂ n₃ : ℤ, x = n₀ + n₁ i + n₂ j + n₃ ω`. [SRC]
  `1_Hurwitz.hurwitzOrder` (the parity form, `mul_mem'` by a parity case split). Attacks: [1] is the
  parity set closed under multiplication? It is `ℤ⟨i,j⟩ + ℤω` and `ω² = ω − 1`, `iω = (i − 1 − k +
  j)/2 ∈ 𝒪` ✓. [4] the roadmap's generator is `(1 + i + j + k)/2`, Voight's `ω` is
  `(−1 + i + j + k)/2`; they differ by `1` and generate the same order ✓. SURVIVED.

- **L4.2** `star_mem_hurwitzOrder`, `exists_nrd_eq_natCast`, `exists_trd_eq_intCast` — [SRC]
  `1_Hurwitz.star_mem`, `.exists_norm_eq_natCast`. Sketch: parities; `A² + B² + C² + D² ≡ 0 mod 4`
  when all four are odd. SURVIVED.

#### Mathlib lemmas needed

`mul_mem'`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4 (module docstring: §0.1.4).
- Literature: the quotations of the module docstring of `Quaternion/Hurwitz.lean`.
- [SRC] (proof idea only, never imported): `1_Hurwitz.hurwitzOrder`, `1_Hurwitz.star_mem`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (13) **Citation erratum, fixed in the README**

#### Progress
- 2026-09-23: DONE. `hurwitzOrder`'s five fields, `star_mem_hurwitzOrder`, `exists_nrd_eq_natCast`
  ported from [SRC] `JacobsSlash/U3/1_Hurwitz.lean` (parity form: one branch with a mod-2 side
  condition, not a four-way split); `exists_nrd_eq_natCast` goes through `nrd_eq_normSq` +
  `normSq_def'`. `exists_trd_eq_intCast` is `trd x = 2 * x.re` (by `rfl`) + `hr`.
  `mem_hurwitzOrder_iff_exists_int` needed the seam recipe below (`qI`, `qJ`, curated `simp only`).
- 2026-09-23: **THE `ℍ[ℚ]` TYPE SEAM — the dominant trap of this file.** `ℍ[ℚ]` is
  `Quaternion ℚ`, a plain `def` for `ℍ[ℚ,-1,-1]`, and it is NOT reducible. Consequences, all hit
  here: (a) lemmas stated for `ℍ[R,a,b]` (`QuaternionAlgebra.re_mul`, `trd_apply`, `nrd_apply`,
  `map_mul` for `nrd`) do NOT fire on `ℍ[ℚ]` terms — `rw` reports "not type-correct under the
  implicit transparency level"; (b) an anonymous constructor `⟨0,1,0,0⟩` written at expected type
  `ℍ[ℚ]` elaborates at `ℍ[ℚ,-1,-1]`, so a product `(↑n : ℍ[ℚ]) * ⟨0,1,0,0⟩` straddles the seam and
  NEITHER namespace's component lemmas match; (c) unfolding a `ℍ[ℚ]`-typed def whose body is a `mk`
  (`simp [hurwitzOmega]`, `simp [ofTuple]`) RE-CREATES the seam — keep such defs opaque and give
  them `rfl` component lemmas instead; (d) a `show` restating the goal at `ℍ[ℚ,-1,-1]` compiled
  with NO error but silently left `sorryAx` in the term (caught only by `#print axioms` — the
  `declaration uses 'sorry'` warning is easy to filter away by accident).
  **The working recipe**: name every `mk` literal as an `ℍ[ℚ]`-level `private def` (`qI`, `qJ`,
  `hurwitzOmega`) and rewrite the statement's literals to it by `simp only [show (⟨0,1,0,0⟩ :
  ℍ[ℚ]) = qI from rfl]`; give every such def and every cast (`intCast_re`, `ofNat_re`, …) `rfl`
  component lemmas; then use a CURATED `simp only [re_add, re_mul, …, <those rfl lemmas>]` — plain
  `simp` is wrong here because its `Int.cast_add`/`Int.cast_mul` split casts at quaternion level
  and strand `(2 : ℍ[ℚ]).re`. For `nrd`/`trd` use `nrd_eq_normSq` (an `ℍ[R]`-level lemma, so it
  DOES fire) and work with `normSq`; `trd y = 2 * y.re` is available as `rfl`.

### [T008] `isUnit_hurwitzOrder_iff`, `card_units_hurwitzOrder`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [T007] · **Type**: proof · **Leaves**: L4.3, L4.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem isUnit_hurwitzOrder_iff {x : hurwitzOrder} : IsUnit x ↔ nrd (x : ℍ[ℚ]) = 1 := by
  sorry
theorem card_units_hurwitzOrder : Nat.card (hurwitzOrder)ˣ = 24 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.3** `isUnit_hurwitzOrder_iff` — [Voi21, §11.2]: "`γ` […] is a unit if and only if
  `nrd(γ) = 1`". Sketch: (→) `nrd` multiplicative with values in `ℕ` (L4.2); (←) `star x` is the
  inverse (L1.2, L4.2). SURVIVED.

- **L4.4** `card_units_hurwitzOrder` — [RM] §0.1.4 "with exactly `24` units"; [Voi21, §11.2]
  "a group of order 24". [SRC] `1_Hurwitz.card_units_hurwitzOrder`: a bijection with the `24` tuples
  `(A,B,C,D) ∈ [−2,2]⁴` of one parity with `A²+B²+C²+D² = 4`, counted by `decide`. Attacks: [5]
  `decide` on a `Finset` filter of `625` tuples compiled in [SRC] ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4 (module docstring: §0.1.4).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `1_Hurwitz.card_units_hurwitzOrder`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (13) **Citation erratum, fixed in the README**

#### Progress
- 2026-09-23: DONE. `isUnit_hurwitzOrder_iff` is stated with `nrd`, so the proof converts with
  `nrd_eq_normSq` first and then uses `self_mul_star` / `star_mul_self` for the inverse `star x`;
  (→) is the ℕ-valued norms `n * m = 1`. `card_units_hurwitzOrder` ports the [SRC] enumeration:
  `unitTuples` = the same-parity tuples in `[-2,2]⁴` with `A²+B²+C²+D² = 4`, `card = 24` by
  `decide`, and `Nat.card_eq_of_bijective` against `{t // t ∈ unitTuples}`. `ofTuple` got four
  `rfl` component simp lemmas (never unfold it — see the seam note on T007).

### [T009] `exists_nrd_sub_le_half`, `exists_div_rem_right`, `exists_div_rem_left` and 1 more

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [T008] · **Type**: proof · **Leaves**: L4.5, L4.6, L4.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_nrd_sub_le_half (γ : ℍ[ℚ]) : ∃ μ ∈ hurwitzOrder, nrd (γ - μ) ≤ 1 / 2 := by
  sorry
theorem exists_div_rem_right (α β : hurwitzOrder) (hβ : β ≠ 0) :
    ∃ μ ρ : hurwitzOrder, α = β * μ + ρ ∧ nrd (ρ : ℍ[ℚ]) < nrd (β : ℍ[ℚ]) := by
  sorry
theorem exists_div_rem_left (α β : hurwitzOrder) (hβ : β ≠ 0) :
    ∃ μ ρ : hurwitzOrder, α = μ * β + ρ ∧ nrd (ρ : ℍ[ℚ]) < nrd (β : ℍ[ℚ]) := by
  sorry
theorem right_ideal_principal (I : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder) :
    ∃ x : hurwitzOrder, I = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x} := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.5** `exists_nrd_sub_le_half` — [Voi21, 11.3.1] (quoted). [SRC]
  `2_Euclidean.exists_normSq_sub_le_half`: round to `ℤ⁴` and to `(ℤ + ½)⁴`; the two squared
  distances sum to at most `1` coordinatewise (`(t − round t)² + (t − ½ − round(t − ½))² ≤ ¼`…), so
  one of them is `≤ ½`. SURVIVED.

- **L4.6** `exists_div_rem_right`, `exists_div_rem_left` — [RM] §0.1.4 "right-Euclidean for the
  reduced norm"; [Voi21, Lemma 11.3.2] (quoted). Sketch: `γ = β⁻¹α` (resp. `αβ⁻¹`), L4.5,
  `nrd ρ = nrd β · nrd(γ − μ) ≤ nrd β / 2 < nrd β` as `nrd β > 0`. Attacks: [4] **source
  inconsistency recorded**: Voight's proof of 11.3.4 invokes "the left Euclidean algorithm
  `α = μβ + ρ`" and then writes `ρ = α − βμ ∈ I`; for a *right* ideal only `α = βμ + ρ` keeps `ρ` in
  `I`. Both divisions are stated; L4.7 uses the right one. SURVIVED.

- **L4.7** `right_ideal_principal` — [RM] §0.1.4 "every right ideal is principal (11.3.4)";
  [Voi21, Proposition 11.3.4] (quoted). Lean: right ideals are `Submodule 𝒪ᵐᵒᵖ 𝒪`, as in [SRC]
  `2_Euclidean.right_ideal_principal`. Sketch: `Nat.sInf_mem` on the norms of the nonzero elements.
  Attacks: [2] `I = ⊥`: generator `0` ✓. SURVIVED.

#### Mathlib lemmas needed

`Nat.sInf_mem`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4 (module docstring: §0.1.4).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `2_Euclidean.exists_normSq_sub_le_half`, `2_Euclidean.right_ideal_principal`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (13) **Citation erratum, fixed in the README**

#### Progress
- 2026-09-23: DONE. The covering bound `exists_normSq_sub_eq` / `exists_nrd_sub_le_half` and the
  right division port [SRC] `JacobsSlash/CN1/2_Euclidean.lean`; `exists_div_rem_left` is new (the
  mirror through `α * β⁻¹`, needed because for a RIGHT ideal only `α = βμ + ρ` keeps `ρ` in `I` —
  the source inconsistency the decomposition recorded). All the `nrd` goals are converted to
  `normSq` before any rewriting. The parity side conditions go through a one-line
  `parity_two_mul_add` helper (bare `by omega` did not see through the tuple projections).
  `right_ideal_principal` uses a private ℕ-valued `hnorm` (choice from `exists_nrd_eq_natCast`)
  for the `Nat.sInf` descent.

### [CLEANUP-3] `/cleanup` of `Quaternion/Hurwitz.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [T009] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-23: folded into the single final cleanup pass with CLEANUP-4 (the file was finished by
  then); see CLEANUP-4.

### [T010] `eq_hurwitzOrder_of_le`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [CLEANUP-3] · **Type**: proof · **Leaves**: L4.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem eq_hurwitzOrder_of_le {S : Subring ℍ[ℚ]} (hS : S.toAddSubgroup.FG)
    (hle : hurwitzOrder ≤ S) : S = hurwitzOrder := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.8** `eq_hurwitzOrder_of_le` — [RM] §0.1.4 "prove it is a maximal order"; [Voi21, Lemma
  11.1.2] (quoted). Lean: a subring `S ⊇ hurwitzOrder` of `ℍ[ℚ]` with `S.toAddSubgroup.FG` equals
  it. Sketch: Voight's proof with L2.4 at `a = b = −1` for `α, αi, αj, αk ∈ S`. Attacks: [3] `FG`
  is necessary (`S = ℍ[ℚ]` contains `𝒪`). [4] "order" is rendered as "finitely generated subring";
  that it spans `ℍ[ℚ]` follows from `𝒪 ≤ S`. SURVIVED.

#### Mathlib lemmas needed

`S.toAddSubgroup.FG`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4 (module docstring: §0.1.4).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (13) **Citation erratum, fixed in the README**

#### Progress

- 2026-09-23: DONE, and no legacy source existed for it. Voight's argument: for `α ∈ S`, the
  reduced traces of `α`, `α·i`, `α·j`, `α·k` are integers by T005 (all four of `i, j, k` lie in
  `𝒪 ≤ S`), which puts `2·re`, `2·imI`, `2·imJ`, `2·imK` in `ℤ`; `nrd α ∈ ℤ` then gives
  `A² + B² + C² + D² = 4n`, and four integer squares summing to a multiple of `4` are all of the
  same parity (private `parity_of_sq_add_sq`: split each `z = 2q + p`, `p ∈ {0,1}`, note `p² = p`,
  so `Σp = 4m` with `Σp ≤ 4`). T005's `h : IsTotallyDefinite` removal in CLEANUP-2 is what lets it
  apply here without a definiteness hypothesis.
- 2026-09-23: the parity helper needs the nonlinear part generalised (`∃ m, Σp = 4 * m`) before
  `omega` — `omega` rejects a goal still containing `a ^ 2`.

### [CLEANUP-4] `/cleanup` of `Quaternion/Hurwitz.lean` (final for the file)

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/Hurwitz.lean` · **Depends on**: [T010] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-23: module docstring now lists `IsHurwitz`, `star_mem_hurwitzOrder`,
  `exists_nrd_eq_natCast`, `exists_trd_eq_intCast`, `isUnit_hurwitzOrder_iff` and
  `exists_nrd_sub_le_half`, and gained an **Implementation notes** section recording the `ℍ[ℚ]`
  type seam and the recipe used against it. A docstring orphaned by an insertion was moved back
  onto `eq_hurwitzOrder_of_le`; no `private` declaration carries a docstring.
- 2026-09-23: gates — 470 lines, 0 `sorry`, `lake build` clean with NO warnings, `lake exe
  runLinter` passes, 0 lines over 100 codepoints, `#print axioms` standard on all 15 public
  declarations.

### [T011] `commRight`, `commRight_tmul`, `instModuleFinite` and 4 more

- **Status**: done   (finished 2026-09-23) · **File**: `Adelic/RightBaseChange.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L5.1, L5.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def commRight (F D R : Type*) [CommRing F] [Ring D] [Algebra F D] [CommRing R] [Algebra F R] :
    R ⊗[F] D ≃ₗ[R] D ⊗[F] R :=
  { (TensorProduct.comm F R D).toAddEquiv with
    map_smul' := by sorry }
theorem commRight_tmul (r : R) (x : D) : commRight F D R (r ⊗ₜ x) = x ⊗ₜ r := by
  sorry
scoped instance instModuleFinite [Module.Finite F D] : Module.Finite R (D ⊗[F] R) := by
  sorry
scoped instance instModuleFree [Module.Free F D] : Module.Free R (D ⊗[F] R) := by
  sorry
def rightBasis (b : Module.Basis ι F D) : Module.Basis ι R (D ⊗[F] R) :=
  (Algebra.TensorProduct.basis R b).map (commRight F D R)
theorem rightBasis_apply (b : Module.Basis ι F D) (i : ι) :
    rightBasis (R := R) b i = b i ⊗ₜ 1 := by
  sorry
theorem rightBasis_repr_tmul (b : Module.Basis ι F D) (x : D) (r : R) (i : ι) :
    (rightBasis (R := R) b).repr (x ⊗ₜ r) i = r * algebraMap F R (b.repr x i) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.1** `commRight`, `commRight_tmul`, `instModuleFinite`, `instModuleFree` — [RM] §0.2.1
  "Mathlib's `IsModuleTopology` for the base change of a finite free module". Lean: the additive
  equivalence `TensorProduct.comm F R D` is `R`-linear from the left algebra on `R ⊗[F] D` to the
  scoped right algebra on `D ⊗[F] R`; finiteness and freeness transport along it. Sketch:
  `map_smul'` by `TensorProduct.induction_on`; on pure tensors `r • (r' ⊗ x) = (r r') ⊗ x ↦ x ⊗ (r r')
  = (1 ⊗ r)(x ⊗ r')`. Then `Module.Finite.equiv`, `Module.Free.of_equiv` with
  `Module.Finite.base_change`, `Module.Free.tensor`. Attacks: [1] is the scoped algebra the one
  Mathlib's lemmas about `rightAlgebra` talk about? It *is* `rightAlgebra`, made an instance by
  `attribute [scoped instance]`, not a copy ✓. [2] `D` commutative and equal to `R`: the right and
  left algebra structures on `R ⊗ R` differ — this is why the scope is opened only in files where
  `D` is the noncommutative factor; recorded in plan.md decision 1. [5] all five names verified.
  SURVIVED.

- **L5.2** `rightBasis`, `rightBasis_apply`, `rightBasis_repr_tmul` — `b i ⊗ₜ 1` is an `R`-basis.
  Defined as `(Algebra.TensorProduct.basis R b).map (commRight F D R)`. `repr (x ⊗ r) i =
  r * algebraMap F R (b.repr x i)`. Attacks: [2] `x = b j`, `r = 1`: `δ_{ij}` ✓. [5]
  `Algebra.TensorProduct.basis_apply` gives `1 ⊗ b i`, mapped to `b i ⊗ 1` ✓. SURVIVED.

#### Mathlib lemmas needed

`map_smul'`, `TensorProduct.induction_on`, `Module.Finite.equiv`, `Module.Free.of_equiv`, `Module.Finite.base_change`, `Module.Free.tensor`, `Algebra.TensorProduct.basis_apply`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1 (module docstring: §0.2.1).
- Literature: the quotations of the module docstring of `Adelic/RightBaseChange.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right**

#### Progress

- 2026-09-23: DONE. The skeleton declares `instModuleFinite` / `instModuleFree` BEFORE `commRight`,
  so the equivalence they transport along is a private `commRightAux` placed inside
  `namespace RightAlgebra`; the public `commRight` then reuses it as
  `map_smul' := (RightAlgebra.commRightAux F D R).map_smul'`, so the `map_smul'` argument is proved
  once. `commRight_tmul` and `rightCoordsL_apply` are `rfl`.
- 2026-09-23: the right action is `Algebra.smul_def` + `Algebra.TensorProduct.right_algebraMap_apply`
  (`algebraMap R (D ⊗[F] R) r = 1 ⊗ₜ r`, a `rfl` lemma) + `tmul_mul_tmul`.
- 2026-09-23: TRAP — in a `map_smul'` field proved by `TensorProduct.induction_on`, the induction
  hypotheses appear in `AddEquiv.toFun` form while `simp` normalises the goal to the coercion form,
  so `simp [hu, hv]` silently fails to use them. Restate them first with
  `have hu' : f (r • u) = r • f u := hu` (defeq) and simp with those.

### [T012] `rightCoordsL`, `rightCoordsL_apply`, `continuous_map_id`

- **Status**: done   (finished 2026-09-23) · **File**: `Adelic/RightBaseChange.lean` · **Depends on**: [T011] · **Type**: proof · **Leaves**: L5.3, L5.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def rightCoordsL (b : Module.Basis ι F D) : (D ⊗[F] R) ≃L[R] (ι → R) :=
  { (rightBasis (R := R) b).equivFun with
    continuous_toFun := by sorry
    continuous_invFun := by sorry }
theorem rightCoordsL_apply (b : Module.Basis ι F D) (x : D ⊗[F] R) (i : ι) :
    rightCoordsL b x i = (rightBasis (R := R) b).repr x i := by
  sorry
theorem continuous_map_id (f : R →ₐ[F] R') (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map (AlgHom.id F D) f) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.3** `rightCoordsL`, `rightCoordsL_apply` — the coordinates `D ⊗[F] R ≃L[R] (ι → R)`, `ι`
  finite. Sketch: both directions are `R`-linear between module-topology modules
  (`IsModuleTopology.instPi` on the right), so continuous by
  `IsModuleTopology.continuous_of_linearMap`. Attacks: [3] `Finite ι` is needed for `instPi` (the
  product topology on an infinite power is not the module topology) ✓. SURVIVED.

- **L5.4** `continuous_map_id` — [RM] §0.2.2 "induces `D_f → D ⊗_F F_v`, an `F`-algebra
  homomorphism, continuous". Lean: for a continuous `f : R →ₐ[F] R'`, `id ⊗ f` is continuous.
  Sketch: it is `f`-semilinear for the right actions; `IsModuleTopology.continuous_of_linearMapₛₗ`.
  [SRC] `04_Level.continuous_toLocal`. Attacks: [3] **succeeded**: the first draft carried
  `[Module.Finite F D]`; the semilinear lemma needs only `ContinuousAdd` and `ContinuousSMul` on the
  target, which every module topology has — hypothesis dropped, here and in L8.2, L8.5. [5]
  `continuous_of_linearMapₛₗ` verified, with the exact implicit-argument shape recorded in the
  ticket. SURVIVED after the edit.

#### Mathlib lemmas needed

`IsModuleTopology.instPi`, `IsModuleTopology.continuous_of_linearMap`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.2 (module docstring: §0.2.1).
- Literature: the quotations of the module docstring of `Adelic/RightBaseChange.lean`.
- [SRC] (proof idea only, never imported): `04_Level.continuous_toLocal`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right**

#### Progress

- 2026-09-23: DONE. Both directions of `rightCoordsL` are
  `IsModuleTopology.continuous_of_linearMap` (the target `ι → R` carries the module topology by
  `IsModuleTopology.instPi`, which is where `Finite ι` is used); `continuous_map_id` builds the
  `f`-semilinear map explicitly and applies `IsModuleTopology.continuous_of_linearMapₛₗ`.
- 2026-09-23: needed one addition to the scope — `ContinuousAdd (D ⊗[F] R)` (from
  `IsModuleTopology.toContinuousAdd`), which is NOT an instance in Mathlib and is required by both
  continuity lemmas. Added as `RightAlgebra.instContinuousAdd` and recorded in the module docstring.

### [CLEANUP-5] `/cleanup` of `Adelic/RightBaseChange.lean` (final for the file)

- **Status**: done   (finished 2026-09-23) · **File**: `Adelic/RightBaseChange.lean` · **Depends on**: [T012] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-23: `lake exe runLinter` flagged `continuous_map_id` for two unused instance arguments,
  `[IsTopologicalRing R]` and `[IsTopologicalRing R']`, picked up automatically from the section —
  exactly the drop the decomposition's L5.4 attack log predicted. Removed with
  `omit [IsTopologicalRing R] [IsTopologicalRing R'] in`. TRAP: `omit … in` must come BEFORE the
  docstring, not between it and the theorem ("unexpected token 'omit'; expected 'lemma'").
- 2026-09-23: gates — build clean with no warnings, linter passes, no lines over 100 codepoints,
  `#print axioms` standard on all nine declarations; module docstring now also lists
  `commRight` and the `ContinuousAdd` instance.

### [T013] `baseChangeEquiv`, `baseChangeEquiv_tmul`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/BaseChange.lean` · **Depends on**: [T003], [T012] · **Type**: proof · **Leaves**: L3.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def baseChangeEquiv :
    ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R,algebraMap F R a,algebraMap F R b] := by
  sorry
theorem baseChangeEquiv_tmul (x : ℍ[F,a,b]) (r : R) :
    baseChangeEquiv F a b R (x ⊗ₜ r) = r • mapRingHom (algebraMap F R) a b x := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.1** `baseChangeEquiv`, `baseChangeEquiv_tmul` — [RM] §0.2.4 "The reduced norm extends to
  `nrd : D_f^× →* (𝔸_F^f)^×`". Lean: `ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R, algebraMap a, algebraMap b]`,
  `x ⊗ r ↦ r • mapRingHom (algebraMap F R) a b x`. Sketch: forward map by
  `Algebra.TensorProduct.lift` of `mapRingHom` (as an `F`-algebra map) and `algebraMap R _`, which
  commute; `R`-linearity for the scoped right algebra is `right_algebraMap_apply`; bijectivity
  because it sends the `R`-basis `rightBasis (basisOneIJK a 0 b)` to `basisOneIJK` of the target.
  Attacks: [2] `R = F`: the identity up to `TensorProduct.rid` ✓. [3] `F` a field is not needed; a
  commutative ring suffices — kept as a field because every use has one. [5]
  `QuaternionAlgebra.basisOneIJK` verified; `rightBasis` is L5.2. SURVIVED.

#### Mathlib lemmas needed

`Algebra.TensorProduct.lift`, `right_algebraMap_apply`, `TensorProduct.rid`, `QuaternionAlgebra.basisOneIJK`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.4 (module docstring: §0.1.1, §0.2.4).
- Literature: the quotations of the module docstring of `Quaternion/BaseChange.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-23: DONE. Mathlib has no quaternion base change, so this is built by hand from the
  universal property `QuaternionAlgebra.Basis`/`liftHom`. Structure (all private, above the
  skeleton's `baseChangeEquiv`): `tmul_algebraMap_one` (`↑c ⊗ₜ 1 = algebraMap R _ (algebraMap F R c)`),
  `mapAlgHom` (T001's `mapRingHom` as an `F`-algebra hom), `baseChangeHomF` (=
  `Algebra.TensorProduct.lift`, an `F`-algebra hom) with `baseChangeHomF_tmul`, `baseChangeHom`
  (the same map as an `R`-algebra hom — only `commutes'` is new), `baseChangeBasis` (the
  quaternionic basis `i ⊗ 1`, `j ⊗ 1`, `k ⊗ 1` of `ℍ[F,a,b] ⊗[F] R`), `tmul_one_eq` and
  `liftHom_mapRingHom` (`liftHom (mapRingHom x) = x ⊗ₜ 1`). `baseChangeEquiv` is then
  `AlgEquiv.ofAlgHom`, with one side by `QuaternionAlgebra.hom_ext` (check on `i` and `j`) and the
  other by `TensorProduct.induction_on`. `baseChangeEquiv_tmul` is `baseChangeHomF_tmul`.
- 2026-09-23: TRAPS, all costly. (1) **`⊗ₜ` needs its base ring annotated** in a standalone
  `have`/private lemma: without `⊗ₜ[F]` the base is a metavariable, and the symptoms are a
  "typeclass instance problem is stuck" error and `simp only [TensorProduct.add_tmul, …]` silently
  making "no progress". (2) **The scoped right-algebra `•` is opaque to the generic smul simp
  lemmas** — `zero_smul` and `one_smul` do NOT fire on `(0 : R) • (y ⊗ₜ 1)`; rewrite with
  `Algebra.smul_def` and `Algebra.TensorProduct.right_algebraMap_apply` instead. (3) Going through
  `{ (Algebra.TensorProduct.lift …).toRingHom with commutes' := … }` and then `show` to unfold back
  to `lift` costs an `isDefEq` heartbeat timeout; name the `F`-algebra hom as its own private def
  and unfold that instead. (4) `Algebra.smul_def` fires on the `F`-smul inside a tensor before
  `TensorProduct.smul_tmul` can move it across, so do the tensor moves in a separate `simp only`
  first.

### [T014] `baseChangeEquiv_map`, `nrdBaseChange`, `nrdBaseChange_tmul_one` and 2 more

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/BaseChange.lean` · **Depends on**: [T013] · **Type**: proof · **Leaves**: L3.2, L3.3, L3.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem baseChangeEquiv_map (f : R →ₐ[F] R') (x : ℍ[F,a,b] ⊗[F] R) :
    equivTuple _ _ _
        (baseChangeEquiv F a b R' (Algebra.TensorProduct.map (AlgHom.id F ℍ[F,a,b]) f x)) =
      f ∘ equivTuple _ _ _ (baseChangeEquiv F a b R x) := by
  sorry
def nrdBaseChange : ℍ[F,a,b] ⊗[F] R →*₀ R :=
  (nrd (R := R)).comp (baseChangeEquiv F a b R).toAlgHom.toRingHom.toMonoidWithZeroHom
theorem nrdBaseChange_tmul_one (x : ℍ[F,a,b]) :
    nrdBaseChange F a b R (x ⊗ₜ 1) = algebraMap F R (nrd x) := by
  sorry
theorem nrdBaseChange_map (f : R →ₐ[F] R') (x : ℍ[F,a,b] ⊗[F] R) :
    nrdBaseChange F a b R' (Algebra.TensorProduct.map (AlgHom.id F ℍ[F,a,b]) f x) =
      f (nrdBaseChange F a b R x) := by
  sorry
theorem continuous_nrdBaseChange [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (nrdBaseChange F a b R) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.2** `baseChangeEquiv_map` — naturality in `R`, as one equation of coordinate tuples:
  `equivTuple _ _ _ (baseChangeEquiv F a b R' ((id ⊗ f) x)) = f ∘ equivTuple _ _ _ (baseChangeEquiv
  F a b R x)`. Match: the two sides live in `ℍ[R', algebraMap F R' a, …]` and `ℍ[R', f (algebraMap F
  R a), …]`, equal types only propositionally, hence the tuple form (plan.md decision 12). Sketch:
  `TensorProduct.induction_on`, L3.1. Attacks: [1] is the statement well-typed without a cast? Yes,
  `equivTuple` lands in `Fin 4 → R'` on both sides ✓ (the first draft was a four-fold conjunction
  and was replaced). SURVIVED.

- **L3.3** `nrdBaseChange`, `nrdBaseChange_tmul_one`, `nrdBaseChange_map` — the reduced norm
  `ℍ[F,a,b] ⊗[F] R →*₀ R`; `x ⊗ 1 ↦ algebraMap (nrd x)`; commutes with `f`. Sketch: L1.8, L3.2.
  SURVIVED.

- **L3.4** `continuous_nrdBaseChange` — for a topological ring `R`. Sketch: the four coordinates of
  `baseChangeEquiv x` are `R`-linear maps to `R`, continuous for the module topology
  (`IsModuleTopology.continuous_of_linearMap`), and `nrd` is a polynomial in them. Attacks: [3] no
  finiteness hypothesis: `ℍ` is finite free by instance ✓. SURVIVED.

#### Mathlib lemmas needed

`TensorProduct.induction_on`, `IsModuleTopology.continuous_of_linearMap`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.1, §0.2.4).
- Literature: the quotations of the module docstring of `Quaternion/BaseChange.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-23: DONE. `baseChangeEquiv_map` by `TensorProduct.induction_on`; the `add` case needs
  `Matrix.cons_val_two` / `Matrix.cons_val_three` / `Matrix.tail_cons` in the `simp_all` set,
  otherwise the index-2 and index-3 components of the induction hypotheses stay as
  `![…] 2` and the goals survive (indices 0 and 1 close without them, which makes the failure
  look sporadic). NOTE `equivTuple` is a bare `Equiv`, so `map_add` does NOT apply to it — expand
  the sum with `re_add`/`imI_add`/… instead.
- 2026-09-23: `nrdBaseChange_map` cannot be proved by induction (`nrd` is not additive); it reads
  the four coordinates off `baseChangeEquiv_map` and uses that `nrd` is a polynomial in them with
  coefficients in the image of `algebraMap F _`, where `f.commutes` applies.
  `continuous_nrdBaseChange` factors through the `R`-linear `L = linearEquivTuple ∘ₗ
  baseChangeEquiv`, continuous by `IsModuleTopology.continuous_of_linearMap`, and then `nrd` is a
  polynomial in `L x 0 … L x 3`.

### [T015] `det_eq_nrdBaseChange`

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/BaseChange.lean` · **Depends on**: [T014] · **Type**: proof · **Leaves**: L3.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem det_eq_nrdBaseChange (θ : ℍ[F,a,b] ⊗[F] R ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (ha : IsUnit (algebraMap F R a)) (hb : IsUnit (algebraMap F R b))
    (x : ℍ[F,a,b] ⊗[F] R) : (θ x).det = nrdBaseChange F a b R x := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.1 Quaternion algebras", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.5** `det_eq_nrdBaseChange` — [RM] §0.1.3 "Prove `det (θ_𝔭 x) = nrd x`". Lean: for every
  `R`-algebra isomorphism `θ : ℍ[F,a,b] ⊗[F] R ≃ₐ[R] M₂(R)` with `2`, `a`, `b` invertible in `R`.
  Sketch: L1.7 for `θ ∘ baseChangeEquiv.symm`, with `S = R`. Attacks: [3] bijectivity of `θ` is not
  used; an `AlgHom` would do — kept as `≃ₐ` because the consumer has one. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3 (module docstring: §0.1.1, §0.2.4).
- Literature: the quotations of the module docstring of `Quaternion/BaseChange.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-23: DONE in three lines: apply T003's `det_map_eq_nrd` to the composite
  `θ ∘ (baseChangeEquiv F a b R).symm : ℍ[R,fa,fb] →ₐ[R] M₂(R)` at `baseChangeEquiv F a b R x`;
  the unit hypotheses transfer because `algebraMap R R` is the identity.

### [CLEANUP-6] `/cleanup` of `Quaternion/BaseChange.lean` (final for the file)

- **Status**: done   (finished 2026-09-23) · **File**: `Quaternion/BaseChange.lean` · **Depends on**: [T015] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-23: module docstring now lists `baseChangeEquiv_tmul`, `continuous_nrdBaseChange` and
  `det_eq_nrdBaseChange`, and gained an **Implementation notes** section recording the hand-built
  base change (Mathlib has none) and the opacity of the scoped right-algebra `•`. One 101-codepoint
  line wrapped; unused simp arguments and an unused binder name cleared; `lake exe runLinter`
  passes and `#print axioms` is standard on all declarations.

### [T016] `finite_residueField_adicCompletionIntegers`

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L6.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.1** `finite_residueField_adicCompletionIntegers` — [RM] Dependencies: "the
  global-number-fields roadmap for the finite adeles". Lean: `Finite (IsLocalRing.ResidueField
  (v.adicCompletionIntegers F))`. Sketch: the composite `𝓞 F → 𝒪_v → 𝒪_v/𝔪_v` is surjective: for
  `x ∈ 𝒪_v` take `y ∈ F` with `v(x − y) < 1` (`HeightOneSpectrum.denseRange_algebraMap`), so
  `v(y) ≤ 1`; write `y = r/s` with `r, s ∈ 𝓞 F`, `s ∉ v` (clear the `v`-part of the denominator with
  `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers` or directly from the
  valuation); `s` is invertible modulo `v`, so `y ≡ r s'` for some `s' ∈ 𝓞 F`. The kernel contains
  `v.asIdeal`, of finite index (`Ideal.finiteQuotientOfFreeOfNeBot`). Attacks: [1] is the residue
  field possibly *larger* than `𝓞 F / v`? No: the map is onto, so `|k_v| ≤ |𝓞 F / v|` ✓ (equality
  is not needed). [4] FLT proves this through `ResidueFieldEquivCompletionResidueField`, absent from
  Mathlib at the pin; ours needs only surjectivity. [5] the three names verified; the "`y = r/s`
  with `s ∉ v`" step is elementary but has no one-line Mathlib form — **the longest leaf of this
  file, estimated 60–80 lines**. SURVIVED.

#### Mathlib lemmas needed

`HeightOneSpectrum.denseRange_algebraMap`, `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers`, `v.asIdeal`, `Ideal.finiteQuotientOfFreeOfNeBot`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.2.1, §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/FiniteAdeles.lean`.

#### Generality decision

Binding decisions of `plan.md`: (11) **The seam with the global-number-fields roadmap is one file**

#### Progress

- 2026-09-29: DONE, ~45 lines, not the estimated 60–80: Mathlib already has the hard step as
  `HeightOneSpectrum.exists_valuation_sub_lt_of_integer` (`x ∈ F`, `v x ≤ 1` ⟹ `∃ a ∈ 𝓞 F`,
  `v (a − x) < γ`). Route: density (`HeightOneSpectrum.denseRange_algebraMap` +
  `mem_closure_iff_nhds` + `Valued.mem_nhds`) gives `y ∈ F` with `v (y − x) < 1`, hence `v y ≤ 1`;
  the Mathlib lemma gives `a`; the ultrametric inequality twice; then `Finite.of_surjective` from
  `𝓞 F ⧸ v.asIdeal` (finite by `Ideal.finiteQuotientOfFreeOfNeBot`) through `Ideal.Quotient.lift`.
- 2026-09-29: TRAPS. (1) `ℤᵐ⁰` needs `open scoped WithZero`; `𝒪[·]`/`𝓀[·]` need `open scoped
  Valued`; coercions need `open scoped algebraMap`. (2) The coercion `F → v.adicCompletion F` is a
  structure literal `{ toCompletion := ↑((WithVal.equiv _).symm k) }`, not `algebraMap`, so
  `valuedAdicCompletion_eq_valuation` (for `𝓞 F`) / `…_valuation'` (for `F`) never fire by `rw`
  on an `algebraMap` term — use them in term mode, `(… k).trans_lt h`, where `exact` unfolds.
  (3) `Valuation.mem_maximalIdeal_iff` is stated for `Valuation.valuationSubring`, and
  `adicCompletionIntegers` is a non-reducible `def` for it: again term mode, not `rw`.

### [T017] `compactSpace_adicCompletionIntegers`, `isCompact_adicCompletionIntegers`, `locallyCompactSpace_adicCompletion`

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: [T016] · **Type**: proof · **Leaves**: L6.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers F) := by
  sorry
theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  sorry
instance locallyCompactSpace_adicCompletion : LocallyCompactSpace (v.adicCompletion F) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.2** `compactSpace_adicCompletionIntegers`, `isCompact_adicCompletionIntegers`,
  `locallyCompactSpace_adicCompletion` — Sketch:
  `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` (complete:
  closed in a complete space; DVR: Mathlib instance; finite residue field: L6.1); local compactness
  from one compact open neighbourhood of `0` in a topological group. Attacks: [5] the criterion is
  stated for `𝒪[K] = Valued.v.integer` and `𝓀[K]`; `adicCompletionIntegers` is
  `Valued.v.valuationSubring` with the same carrier — the transfer is `isCompact_iff_compactSpace` on
  the common underlying set; **flagged for the ticket** as the one defeq seam of the file. The
  criterion needs `[(Valued.v).RankOne]`: Mathlib's `instRankOneAdicCompletion` ✓. SURVIVED.

#### Mathlib lemmas needed

`compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`, `Valued.v.valuationSubring`, `isCompact_iff_compactSpace`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.2.1, §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/FiniteAdeles.lean`.

#### Generality decision

Binding decisions of `plan.md`: (11) **The seam with the global-number-fields roadmap is one file**

#### Progress

- 2026-09-29: DONE. Mathlib's criterion
  `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
  is stated for `𝒪[K] = Valued.integer K` (a `Subring`), not for the `ValuationSubring`
  `adicCompletionIntegers`; the three hypotheses transfer by `inferInstanceAs` / defeq, except
  `CompleteSpace`, which is not an instance for the subtype and comes from closedness
  (`AddSubgroup.isClosed_of_isOpen` + `IsClosed.completeSpace_coe`). `locallyCompactSpace_adicCompletion`
  ports FLT's translate argument: `WeaklyLocallyCompactSpace` from `x +ᵥ 𝒪_v` (compact, open), then
  `infer_instance`.

### [T018] `integralAdeles`, `mem_integralAdeles_iff`, `exists_integralAdeles_eq` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: [T017] · **Type**: proof · **Leaves**: L6.3, L6.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def integralAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
theorem mem_integralAdeles_iff {x : FiniteAdeleRing (𝓞 F) F} :
    x ∈ integralAdeles F ↔ ∀ v, x v ∈ v.adicCompletionIntegers F :=
  Iff.rfl
theorem exists_integralAdeles_eq
    (z : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    ∃ x ∈ integralAdeles F, ∀ v, x v = z v := by
  sorry
theorem isOpen_integralAdeles :
    IsOpen (integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.3** `integralAdeles` (fields), `mem_integralAdeles_iff`, `exists_integralAdeles_eq` — [RM]
  §0.2.3 "`∏_v 𝒪_v`". Every family of local integers is an adele (the restricted-product condition
  holds everywhere). SURVIVED.

- **L6.4** `isCompact_integralAdeles`, `isOpen_integralAdeles` — [Voi21, 27.6.6] "compact open
  subring". Sketch: the range of `RestrictedProduct.structureMap`, the image of the compact
  `∏_v 𝒪_v` (`isCompact_univ_pi`, L6.2) under a continuous map; open by
  `RestrictedProduct.isOpenEmbedding_structureMap`, whose openness hypothesis is Mathlib's `Fact`
  instance. Attacks: [5] both names verified; `structureMap`'s range equals the carrier by `ext`.
  SURVIVED.

#### Mathlib lemmas needed

`isCompact_integralAdeles`, `RestrictedProduct.structureMap`, `isCompact_univ_pi`, `RestrictedProduct.isOpenEmbedding_structureMap`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.3 (module docstring: §0.2.1, §0.2.3).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (11) **The seam with the global-number-fields roadmap is one file**

#### Progress

- 2026-09-29: DONE. The five subring fields are the generic `mul_mem`/`add_mem`/`neg_mem`/
  `one_mem`/`zero_mem` applied pointwise (NOT `ValuationSubring.neg_mem`, whose element argument
  is explicit). `exists_integralAdeles_eq` is `RestrictedProduct.structureMap`. Compactness and
  openness both go through `RestrictedProduct.isOpenEmbedding_structureMap` (explicit hypothesis
  `∀ i, IsOpen (A i)`) and `RestrictedProduct.range_structureMap`, whose right-hand side is
  exactly the carrier; compactness uses `isCompact_range`, which needs
  `CompactSpace ↥(↑(v.adicCompletionIntegers F) : Set _)` — the set-coe form, supplied by
  `inferInstanceAs` from T017's SetLike-coe instance.

### [CLEANUP-7] `/cleanup` of `Adelic/FiniteAdeles.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: [T018] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: folded into the single final pass with CLEANUP-8; see CLEANUP-8.

### [T019] `locallyCompactSpace_finiteAdeleRing`, `t2Space_finiteAdeleRing`, `totallyDisconnectedSpace_finiteAdeleRing`

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: [CLEANUP-7] · **Type**: proof · **Leaves**: L6.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  sorry
instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 F) F) := by
  sorry
instance totallyDisconnectedSpace_finiteAdeleRing :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.5** `locallyCompactSpace_finiteAdeleRing`, `t2Space_finiteAdeleRing`,
  `totallyDisconnectedSpace_finiteAdeleRing` — [RM] §0.2.1 "locally compact totally disconnected".
  Sketch: `RestrictedProduct.locallyCompactSpace_of_group`; T2 and total disconnectedness because
  `RestrictedProduct.continuous_coe` is a continuous injection into the product of the `F_v`, which
  is T2 and totally disconnected (each `F_v` is: a valued field has a basis of clopen balls).
  Attacks: [5] **name miss repaired**: `Function.Injective.totallyDisconnectedSpace` does not exist;
  use `isTotallyDisconnected_of_image` (verified in the file
  `Topology/Connected/TotallyDisconnected.lean`). Total disconnectedness of `F_v` may itself need a
  short proof from `Valued.isClopen_closedBall` — **flagged for the ticket**. SURVIVED.

#### Mathlib lemmas needed

`RestrictedProduct.locallyCompactSpace_of_group`, `RestrictedProduct.continuous_coe`, `Function.Injective.totallyDisconnectedSpace`, `isTotallyDisconnected_of_image`, `Valued.isClopen_closedBall`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1 (module docstring: §0.2.1, §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/FiniteAdeles.lean`.

#### Generality decision

Binding decisions of `plan.md`: (11) **The seam with the global-number-fields roadmap is one file**

#### Progress

- 2026-09-29: DONE. `FiniteAdeleRing` is a non-reducible `def`, so each instance is
  `inferInstanceAs` at the unfolded `Πʳ` type (needs `open scoped RestrictedProduct`). Local
  compactness: Mathlib's `Πʳ` instance from `Fact (∀ i, IsOpen (B i))` + `∀ i, CompactSpace (B i)`.
  T2: Mathlib's `Πʳ` instance. Total disconnectedness: `isTotallyDisconnected_of_image` along the
  continuous injection `RestrictedProduct.continuous_coe` / `DFunLike.coe_injective` into
  `Π v, F_v`, which is totally disconnected because each `F_v` is: Mathlib's
  `NonarchimedeanAddGroup.instTotallySeparated` fires on the valued field — the "short proof from
  `Valued.isClopen_closedBall`" the ticket flagged was not needed.

### [CLEANUP-8] `/cleanup` of `Adelic/FiniteAdeles.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/FiniteAdeles.lean` · **Depends on**: [T019] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: module docstring now lists `finite_residueField_adicCompletionIntegers`,
  `locallyCompactSpace_adicCompletion` and `exists_integralAdeles_eq`, plus an **Implementation
  notes** section (the structure-literal coercion, the `Subring`/`ValuationSubring` split of
  the compactness criterion). One 106-codepoint line wrapped via `open Valued.integer in`;
  deprecated `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; two unused binders → `_`. Gates: 0 sorries,
  0 warnings, `lake exe runLinter` passes, `#print axioms` standard on all 11 declarations.

### [T020] `isOpen_of_isOpen`, `isCompact_of_isCompact`, `incl_injective` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Basic.lean` · **Depends on**: [T012], [T019] · **Type**: proof · **Leaves**: L7.1, L7.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem Units.isOpen_of_isOpen {S : Set M} (hS : IsOpen S) :
    IsOpen {u : Mˣ | (u : M) ∈ S ∧ ((u⁻¹ : Mˣ) : M) ∈ S} := by
  sorry
theorem Units.isCompact_of_isCompact [T1Space M] [ContinuousMul M] {S : Set M}
    (hS : IsCompact S) : IsCompact {u : Mˣ | (u : M) ∈ S ∧ ((u⁻¹ : Mˣ) : M) ∈ S} := by
  sorry
theorem incl_injective : Function.Injective (incl F D) := by
  sorry
theorem unitsIncl_injective : Function.Injective (unitsIncl F D) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.1** `Units.isOpen_of_isOpen`, `Units.isCompact_of_isCompact` — [RM] §0.2.3 "the unit group
  of a compact multiplicatively closed subset is compact because `Units.embedProduct` is a closed
  embedding". [SRC] `04_Level.Units.isOpen_of_isOpen`, `.isCompact_of_isCompact`. Sketch: preimages
  under `Units.continuous_val` and `Units.continuous_coe_inv`; for compactness, the set is the
  preimage of `S ×ˢ (op '' S)` under the closed embedding. Attacks: [3] `T1Space` and
  `ContinuousMul` are the hypotheses of `Units.isClosedEmbedding_embedProduct` ✓. [1] no
  multiplicative closure is needed for the *statement* (it is about a set) ✓. SURVIVED.

- **L7.2** `incl_injective`, `unitsIncl_injective` — [RM] §0.2.1 "`D^× → D_f^×` is an injective
  group homomorphism". Sketch: `D` is free over the field `F`, `F → 𝔸_F^f` is injective (there is a
  finite place, and each `F → F_v` is injective); flatness of a free module. Attacks: [2] does a
  number field have a finite place? `𝓞 F` is a Dedekind domain that is not a field, so
  `HeightOneSpectrum (𝓞 F)` is nonempty ✓. [3] no finiteness of `D` needed ✓. SURVIVED.

#### Mathlib lemmas needed

`Units.embedProduct`, `Units.continuous_val`, `Units.continuous_coe_inv`, `Units.isClosedEmbedding_embedProduct`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1, §0.2.3 (module docstring: §0.2.1).
- Literature: the quotations of the module docstring of `Adelic/Basic.lean`.
- [SRC] (proof idea only, never imported): `04_Level.Units.isOpen_of_isOpen`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right**

#### Progress

- 2026-09-29: DONE on the first build. `Units.isOpen_of_isOpen`: two preimages under
  `Units.continuous_val` / `Units.continuous_coe_inv`. `Units.isCompact_of_isCompact`:
  `Units.isClosedEmbedding_embedProduct.isCompact_preimage` of `S ×ˢ (op '' S)`, then `convert` +
  `simp [Units.embedProduct]`. `incl_injective` = `Algebra.TensorProduct.includeLeft_injective`
  (flatness over the field `F` is automatic), fed by two private helpers:
  `nonempty_heightOneSpectrum` (a maximal ideal of `𝓞 F` is nonzero since `𝓞 F` is not a field)
  and `algebraMap_finiteAdeleRing_injective` (read off one coordinate, where `F → F_v` is a field
  hom). `unitsIncl_injective` = `Units.map_injective`.

### [T021] `locallyCompactSpace_Df`, `t2Space_Df`, `totallyDisconnectedSpace_Df` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Basic.lean` · **Depends on**: [T020] · **Type**: proof · **Leaves**: L7.3, L7.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
instance locallyCompactSpace_Df : LocallyCompactSpace (Df F D) := by
  sorry
instance t2Space_Df : T2Space (Df F D) := by
  sorry
instance totallyDisconnectedSpace_Df : TotallyDisconnectedSpace (Df F D) := by
  sorry
instance locallyCompactSpace_Dfx : LocallyCompactSpace (Dfx F D) := by
  sorry
instance totallyDisconnectedSpace_Dfx : TotallyDisconnectedSpace (Dfx F D) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.3** `locallyCompactSpace_Df`, `t2Space_Df`, `totallyDisconnectedSpace_Df` — [RM] §0.2.1
  "`D_f` is a locally compact totally disconnected topological ring". Sketch: L5.3 for a finite
  basis (`Module.Free.chooseBasis`), L6.5. SURVIVED.

- **L7.4** `locallyCompactSpace_Dfx`, `totallyDisconnectedSpace_Dfx` — [RM] §0.2.1 "`D_f^×` is a
  locally compact totally disconnected group". Sketch: closed embedding into `D_f × D_fᵐᵒᵖ`
  (`Topology.IsClosedEmbedding.locallyCompactSpace`), L7.3. `IsTopologicalGroup (Dfx F D)` is found
  by instance search in the skeleton (the `example` at the end of the file). SURVIVED.

#### Mathlib lemmas needed

`Module.Free.chooseBasis`, `Topology.IsClosedEmbedding.locallyCompactSpace`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1 (module docstring: §0.2.1).
- Literature: the quotations of the module docstring of `Adelic/Basic.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right**

#### Progress

- 2026-09-29: DONE on the first build, five one-term instances. `D_f`: T012's
  `rightCoordsL (Module.Free.chooseBasis F D) : D_f ≃L[𝔸] (ι → 𝔸)` as a homeomorphism —
  `isClosedEmbedding.locallyCompactSpace`, `isEmbedding.t2Space`, and `isTotallyDisconnected_of_image`
  into `ι → 𝔸` (T019 instances on each factor). `D_f^×`: `Units.isClosedEmbedding_embedProduct`
  into `D_f × D_fᵐᵒᵖ` (Mathlib has `LocallyCompactSpace Mᵐᵒᵖ`) for local compactness; total
  disconnectedness through the injective `Units.val` into `D_f` (simpler than the product).

### [CLEANUP-9] `/cleanup` of `Adelic/Basic.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Basic.lean` · **Depends on**: [T021] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: nothing to change — no warnings, no line over 100 codepoints, `lake exe runLinter`
  passes, the module docstring already lists every main declaration, no `private` declaration
  carries a docstring; `#print axioms` standard on all nine public declarations.

### [T022] `toLocal_tmul`, `toLocal_incl`, `continuous_toLocal` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T021] · **Type**: proof · **Leaves**: L8.1, L8.2, L8.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem toLocal_tmul (x : D) (a : FiniteAdeleRing (𝓞 F) F) :
    toLocal F D v (x ⊗ₜ a) = x ⊗ₜ a v := by
  sorry
theorem toLocal_incl (x : D) : toLocal F D v (incl F D x) = x ⊗ₜ 1 := by
  sorry
theorem continuous_toLocal : Continuous (toLocal F D v) := by
  sorry
theorem continuous_toLocalUnits : Continuous (toLocalUnits F D v) := by
  sorry
theorem ext_toLocal [Module.Finite F D] {x y : Df F D}
    (h : ∀ v, toLocal F D v x = toLocal F D v y) : x = y := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.1** `toLocal_tmul`, `toLocal_incl` — API of the component map
  `toLocal = Algebra.TensorProduct.map (AlgHom.id F D) (evalAlgHom F v)`. `simp`. SURVIVED.

- **L8.2** `continuous_toLocal`, `continuous_toLocalUnits` — [RM] §0.2.2 "continuous". L5.4 with
  `RestrictedProduct.continuous_eval`; `Continuous.units_map`. SURVIVED.

- **L8.3** `ext_toLocal` — the components are jointly injective. Sketch: coordinates (L5.2): the
  coordinates of `toLocal v x` are the `v`-components of those of `x` (the statement L9.2), and an
  adele is determined by its components (`RestrictedProduct.ext`). Attacks: [3] `Module.Finite` is
  used only to pick a finite basis; a worker may drop it with `Module.Free.chooseBasis` — left in,
  flagged. SURVIVED.

#### Mathlib lemmas needed

`RestrictedProduct.continuous_eval`, `Continuous.units_map`, `RestrictedProduct.ext`, `Module.Finite`, `Module.Free.chooseBasis`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.2 (module docstring: §0.1.3, §0.2.2).
- Literature: the quotations of the module docstring of `Adelic/Components.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-29: DONE on the first build. `toLocal_tmul`, `toLocal_incl` are `rfl`;
  `continuous_toLocal` is T012's `continuous_map_id` with `RestrictedProduct.continuous_eval`;
  `continuous_toLocalUnits` is `Continuous.units_map`. `ext_toLocal` goes through a private
  `rightBasis_repr_toLocal` (the right-basis coordinates of `toLocal v x` are the `v`-components of
  those of `x`, by `TensorProduct.induction_on` + T011's `rightBasis_repr_tmul`, each case closing by
  `rfl`), then `Finsupp.ext` and `DFunLike.ext` on the adele (`FiniteAdeleRing` has a `DFunLike`
  instance, so no `RestrictedProduct.ext` through the `def` is needed).

### [T023] `RigidificationAt`, `toMatrixHom`, `toGL` and 9 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T022] · **Type**: proof · **Leaves**: L8.4, L8.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
class RigidificationAt : Type _ where
  /-- The splitting isomorphism `θ_v`. -/
  equiv : Dv F D v ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)
def toMatrixHom : Df F D →ₐ[F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  ((RigidificationAt.equiv (F := F) (D := D) (v := v)).toAlgHom.restrictScalars F).comp
    (toLocal F D v)
def toGL : Dfx F D →* GL (Fin 2) (v.adicCompletion F) :=
  Units.map (toMatrixHom F D v).toMonoidHom
def toMatrix : Dfx F D →* Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  (Units.coeHom _).comp (toGL F D v)
theorem coe_toGL (g : Dfx F D) :
    ((toGL F D v g : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = toMatrix F D v g := rfl
theorem toMatrix_apply (g : Dfx F D) :
    toMatrix F D v g =
      RigidificationAt.equiv (F := F) (D := D) (v := v) (toLocal F D v (g : Df F D)) := rfl
theorem toMatrix_det_ne_zero (g : Dfx F D) : (toMatrix F D v g).det ≠ 0 := by
  sorry
theorem RigidificationAt.moduleFinite : Module.Finite F D := by
  sorry
theorem continuous_rigidification :
    Continuous (RigidificationAt.equiv (F := F) (D := D) (v := v)) := by
  sorry
theorem continuous_rigidification_symm :
    Continuous (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm := by
  sorry
theorem continuous_toMatrix : Continuous (toMatrix F D v) := by
  sorry
theorem continuous_toGL : Continuous (toGL F D v) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.4** `RigidificationAt`, `toMatrixHom`, `toGL`, `toMatrix`, `coe_toGL`, `toMatrix_apply`,
  `toMatrix_det_ne_zero`, `RigidificationAt.moduleFinite` — [RM] §0.1.3 "A *rigidification at `𝔭`*
  is a choice of `F_𝔭`-algebra isomorphism `θ_𝔭 : D ⊗_F F_𝔭 ≃ M₂(F_𝔭)` […] carry it as data";
  [Buz07, p. 68] (`buzzard.txt:2627`): "fix an isomorphism `𝒪_D ⊗_{𝒪_F} 𝒪_{F_v} = M₂(𝒪_{F_v})` for
  all finite places `v` of `F` where `D` splits". `moduleFinite`: a linearly independent family of
  `D` stays independent in `D ⊗ F_v` (`rightBasis` of a basis of `D`), and `M₂(F_v)` has rank `4`.
  Attacks: [4] **design change against [SRC]**: [SRC] has an `F`-algebra isomorphism plus the mixin
  `IsCompletionLinear`; the roadmap asks for `F_𝔭`-linearity, which the scoped right algebra makes
  statable (plan.md decision 4). [1] is integrality of `θ` part of the class? No: it is relative to
  an order and is the separate predicate L9.7 ✓. SURVIVED.

- **L8.5** `continuous_rigidification`, `continuous_rigidification_symm`, `continuous_toMatrix`,
  `continuous_toGL` — Sketch: `θ_v` is `F_v`-linear between module-topology modules (`M₂(F_v)` with
  its product topology, `IsModuleTopology.instPi` twice). [SRC]
  `04_Level.continuous_rigidificationEquiv`. Attacks: [5] `Matrix n n R` is a `def` for `n → n → R`;
  the `IsModuleTopology` instance is found after `inferInstanceAs` — **flagged for the ticket**.
  SURVIVED.

#### Mathlib lemmas needed

`IsModuleTopology.instPi`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3 (module docstring: §0.1.3, §0.2.2).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `04_Level.continuous_rigidificationEquiv`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-29: **B2 REPAIRED IN PLACE** (logged in `b2_log.jsonl`): as elaborated,
  `RigidificationAt.moduleFinite : Module.Finite F D` mentions neither `v` nor the rigidification, so
  Lean dropped `[RigidificationAt F D v]` and the statement claimed EVERY `F`-algebra is
  finite-dimensional (false: `F[X]`). Repaired with `include v in` (placed BEFORE the docstring —
  same placement rule as `omit … in`); nothing else in the statement changed.
- 2026-09-29: DONE. `toMatrix_det_ne_zero` via `(toGL g).isUnit.map Matrix.detMonoidHom`;
  `moduleFinite`: `Dv ≃ M₂(F_v)` makes `Dv` finite over `F_v`, so T011's `rightBasis` of
  `Module.Free.chooseBasis F D` has a finite index (`Module.Finite.finite_basis`), and
  `Module.Finite.of_basis`. The four continuity statements are
  `IsModuleTopology.continuous_of_linearMap`; for the inverse, `M₂(F_v)` needs
  `IsModuleTopology` by `inferInstanceAs` at `Fin 2 → Fin 2 → F_v` (the flag in the sketch was
  right).

### [T024] `singleₗ`, `extendZero_mul`, `toLocal_extendZero` and 3 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T023] · **Type**: proof · **Leaves**: L8.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def singleₗ : v.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun a := RestrictedProduct.single
    (fun w : HeightOneSpectrum (𝓞 F) ↦ w.adicCompletionIntegers F) v a
  map_add' := by sorry
  map_smul' := by sorry
theorem extendZero_mul (x y : Dv F D v) :
    extendZero F D v (x * y) = extendZero F D v x * extendZero F D v y := by
  sorry
theorem toLocal_extendZero (x : Dv F D v) : toLocal F D v (extendZero F D v x) = x := by
  sorry
theorem toLocal_extendZero_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (x : Dv F D v) :
    toLocal F D w (extendZero F D v x) = 0 := by
  sorry
theorem extendZero_mul_eq (x : Dv F D v) (g : Df F D) :
    extendZero F D v x * g = extendZero F D v (x * toLocal F D v g) := by
  sorry
theorem mul_extendZero_eq (x : Dv F D v) (g : Df F D) :
    g * extendZero F D v x = extendZero F D v (toLocal F D v g * x) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.6** `singleₗ` (fields), `extendZero_mul`, `toLocal_extendZero`, `toLocal_extendZero_of_ne`,
  `extendZero_mul_eq`, `mul_extendZero_eq` — [RM] §0.2.2 "the inclusion `ι_𝔭 : GL₂(F_𝔭) → D_f^×` of
  elements with trivial components elsewhere". [SRC] `04_UpiElement.singleₗ`, `.iotaV`,
  `.iotaV_mul`, `.toLocal_iotaV`, `.toLocal_iotaV_ne`, and `23_QuaternionData.QMF.
  iotaV_mul_eq_iotaV_mul_toLocal`. Sketch: on pure tensors with `RestrictedProduct.mul_single`,
  `single_mul`, `single_eq_same`, `single_eq_of_ne`. Attacks: [2] `extendZero` is **not** unital:
  `extendZero 1 ≠ 1`, which is why `localIncl` is `1 + extendZero (u − 1)` ✓. [5] four names
  verified; `single` needs `DecidableEq` on the places — `open scoped Classical` in the file ✓.
  SURVIVED.

#### Mathlib lemmas needed

`RestrictedProduct.mul_single`, `single_mul`, `single_eq_same`, `single_eq_of_ne`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.2 (module docstring: §0.1.3, §0.2.2).
- Literature: the quotations of the module docstring of `Adelic/Components.lean`.
- [SRC] (proof idea only, never imported): `04_UpiElement.singleₗ`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-29: DONE. `singleₗ.map_add'` is `Pi.single_add` through `DFunLike.ext` (Mathlib has no
  `RestrictedProduct.singleAddMonoidHom`). `map_smul'`: `RestrictedProduct.mul_single` is stated on
  the raw `Πʳ`, so it is chained with `(Algebra.smul_def (A := FiniteAdeleRing ..) c _).symm` by
  `Eq.trans` — a mixed `HMul (FiniteAdeleRing ..) (Πʳ ..)` does not elaborate, and a type ascription
  `(e : FiniteAdeleRing ..)` does not change the inferred type. The five `extendZero` lemmas are
  `TensorProduct.induction_on` with private `singleₗ_mul`/`mul_singleₗ` (adele extensionality with
  an `eq_or_ne w v` split).

### [CLEANUP-10] `/cleanup` of `Adelic/Components.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T024] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged with CLEANUP-11 into one inline pass over the whole file (T024–T026 had
  been staged into one build; see CLEANUP-11).

### [T025] `localIncl`, `toLocalUnits_localIncl`, `toLocalUnits_localIncl_of_ne` and 5 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [CLEANUP-10] · **Type**: proof · **Leaves**: L8.7, L8.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def localIncl : (Dv F D v)ˣ →* Dfx F D where
  toFun u :=
    ⟨1 + extendZero F D v ((u : Dv F D v) - 1), 1 + extendZero F D v (((u⁻¹ : (Dv F D v)ˣ) :
      Dv F D v) - 1), by sorry, by sorry⟩
  map_one' := by sorry
  map_mul' := by sorry
theorem toLocalUnits_localIncl (u : (Dv F D v)ˣ) :
    toLocalUnits F D v (localIncl F D v u) = u := by
  sorry
theorem toLocalUnits_localIncl_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (u : (Dv F D v)ˣ) : toLocalUnits F D w (localIncl F D v u) = 1 := by
  sorry
theorem localIncl_injective : Function.Injective (localIncl F D v) := by
  sorry
theorem localIncl_commute (u : (Dv F D v)ˣ) {g : Dfx F D} (hg : toLocalUnits F D v g = 1) :
    Commute (localIncl F D v u) g := by
  sorry
theorem localIncl_commute_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (u : (Dv F D v)ˣ) (u' : (Dv F D w)ˣ) :
    Commute (localIncl F D v u) (localIncl F D w u') := by
  sorry
theorem exists_eq_localIncl_mul (g : Dfx F D) :
    ∃ g' : Dfx F D, toLocalUnits F D v g' = 1 ∧
      g = localIncl F D v (toLocalUnits F D v g) * g' := by
  sorry
theorem continuous_localIncl [Module.Finite F D] : Continuous (localIncl F D v) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.7** `localIncl` (fields), `toLocalUnits_localIncl`, `toLocalUnits_localIncl_of_ne`,
  `localIncl_injective` — [RM] §0.2.2 "a group homomorphism with `θ_𝔭 ∘ ι_𝔭 = id` and
  `θ_𝔮 ∘ ι_𝔭 = 1` for `𝔮 ≠ 𝔭`". Sketch: substrate; `map_mul'` is `(1 + e(u−1))(1 + e(u'−1)) =
  1 + e(uu' − 1)` by L8.6. SURVIVED.

- **L8.8** `localIncl_commute`, `localIncl_commute_of_ne`, `exists_eq_localIncl_mul`,
  `continuous_localIncl` — [RM] §0.2.2 "the image of `ι_𝔭` commutes with every element of trivial
  `𝔭`-component". Sketch: substrate; the decomposition `g = ι_v(g_v) · g'` with
  `g' = ι_v(g_v)⁻¹ g`; continuity through coordinates (`extendZero` is `single` coordinatewise).
  Attacks: [3] `continuous_localIncl` keeps `[Module.Finite F D]`: `extendZero` is not semilinear
  along a *unital* ring homomorphism, so L5.4 does not apply and the proof goes through a finite
  basis ✓ (checked, not dropped). [5] continuity of `RestrictedProduct.single` has no verified
  Mathlib name — **flagged for the ticket**: prove it from `RestrictedProduct.continuous_dom`-style
  universal properties or from `isOpenEmbedding_structureMap` on the open subgroup. SURVIVED.

#### Mathlib lemmas needed

`map_mul'`, `RestrictedProduct.single`, `RestrictedProduct.continuous_dom`, `isOpenEmbedding_structureMap`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.2 (module docstring: §0.1.3, §0.2.2).
- Literature: the quotations of the module docstring of `Adelic/Components.lean`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-29: DONE (staged into the T024 build). Private `one_add_extendZero_mul`:
  `(1 + e(x−1))(1 + e(y−1)) = 1 + e(xy−1)` by `noncomm_ring` after splitting `xy − 1`; it gives both
  unit identities and `map_mul'`. Commutation: `e(x)·g = e(x·g_v)` and `g·e(x) = e(g_v·x)` with
  `g_v = 1`. Continuity of `RestrictedProduct.single` (flagged, no Mathlib name): factor through the
  principal-filter restricted product `Πʳ_[𝓟 {v}ᶜ]` (`continuous_rng_of_principal` +
  `continuous_single`) and `continuous_inclusion`; build the element with
  `RestrictedProduct.mk _ (hmem a)` — an anonymous constructor gets the SUBTYPE topology.
  `extendZero` is `single` coordinatewise in `rightBasis` coordinates (`rightCoordsL`), so it is
  continuous under `[Module.Finite F D]` (kept, used).

### [T026] `unitAt`, `toGL_unitAt`, `toGL_unitAt_of_ne` and 6 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T025] · **Type**: proof · **Leaves**: L8.9, L8.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def unitAt : GL (Fin 2) (v.adicCompletion F) →* Dfx F D :=
  (localIncl F D v).comp
    (Units.map (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toAlgHom.toMonoidHom)
theorem toGL_unitAt (m : GL (Fin 2) (v.adicCompletion F)) : toGL F D v (unitAt F D v m) = m := by
  sorry
theorem toGL_unitAt_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w] (hw : w ≠ v)
    (m : GL (Fin 2) (v.adicCompletion F)) : toGL F D w (unitAt F D v m) = 1 := by
  sorry
theorem unitAt_injective : Function.Injective (unitAt F D v) := by
  sorry
theorem unitAt_commute (m : GL (Fin 2) (v.adicCompletion F)) {g : Dfx F D}
    (hg : toLocalUnits F D v g = 1) : Commute (unitAt F D v m) g := by
  sorry
theorem toLocalUnits_eq_one_of_toGL_eq_one {g : Dfx F D} (hg : toGL F D v g = 1) :
    toLocalUnits F D v g = 1 := by
  sorry
theorem continuous_unitAt [Module.Finite F D] : Continuous (unitAt F D v) := by
  sorry
theorem unitsIncl_algebraMap_commute (c : Fˣ) (g : Dfx F D) :
    Commute (unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c)) g := by
  sorry
theorem toMatrix_unitsIncl_algebraMap (c : Fˣ) :
    toMatrix F D v (unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c)) =
      algebraMap F (v.adicCompletion F) (c : F) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.9** `unitAt`, `toGL_unitAt`, `toGL_unitAt_of_ne`, `unitAt_injective`, `unitAt_commute`,
  `toLocalUnits_eq_one_of_toGL_eq_one`, `continuous_unitAt` — `ι_v` through the rigidification.
  [SRC] `04_UpiElement.unitAt`, `.toLocal_unitAt`, `23_QuaternionData.QMF.unitAt_mul`,
  `.unitAt_comm_of_toLocal_eq_one`. SURVIVED.

- **L8.10** `unitsIncl_algebraMap_commute`, `toMatrix_unitsIncl_algebraMap` — global scalars are
  central, and `θ_v(c ⊗ 1) = c • 1` by `F_v`-linearity (`c ⊗ 1 = 1 ⊗ c = algebraMap F_v _ c`). [SRC]
  `23_QuaternionData.QMF.unitsIncl_algebraMap_comm`, `.toMatrix_unitsIncl_algebraMap`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.3, §0.2.2).
- Literature: the quotations of the module docstring of `Adelic/Components.lean`.
- [SRC] (proof idea only, never imported): `04_UpiElement.unitAt`, `23_QuaternionData.QMF.unitsIncl_algebraMap_comm`.

#### Generality decision

Binding decisions of `plan.md`: (1) **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-29: DONE (staged into the T024 build). All through private `unitAt_apply` (rfl) and
  `toLocal_localIncl(_of_ne)` (`congrArg Units.val` of the T025 lemmas); injectivity is
  `Function.LeftInverse.injective (g := toGL F D v)`. Scalars: `↑(unitsIncl (c)) = algebraMap F D_f c`
  by `rfl`, then `Algebra.commutes`; `θ_v(c ⊗ 1) = c • 1` via `c ⊗ 1 = 1 ⊗ c` (`smul_tmul`),
  `right_algebraMap_apply`, `AlgEquiv.commutes`. Axioms standard for all 15 declarations checked.

### [CLEANUP-11] `/cleanup` of `Adelic/Components.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Components.lean` · **Depends on**: [T026] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. File sorry-free; `lake exe runLinter` passes; every line ≤ 100
  codepoints. Module docstring now lists every main definition and result. Docstrings added to
  the substantive public theorems (continuity, splitting, injectivity, `extendZero` lemmas);
  non-terminal `simp; rfl` in `rightBasis_repr_toLocal` replaced by `simp only [...]` + `rfl`;
  `localIncl.map_mul'` golfed to `Units.ext (one_add_extendZero_mul ..).symm`; the unused
  `RestrictedProduct` scope dropped. No unused instance hypotheses (`[Module.Finite F D]` on
  `continuous_localIncl`/`continuous_unitAt` is used; note it is derivable from
  `[RigidificationAt F D v]` for `continuous_unitAt` via `RigidificationAt.moduleFinite`, kept
  since the statement is fixed and the hypothesis is used).

### [T027] `IsOrderBasis`, `orderOf`, `adelicOrder` and 3 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T026] · **Type**: proof · **Leaves**: L9.1, L9.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
structure IsOrderBasis (b : Module.Basis ι F D) : Prop where
  /-- The coordinates of `1` are integers. -/
  one_repr : ∀ i, b.repr 1 i ∈ (algebraMap (𝓞 F) F).range
  /-- The structure constants are integers. -/
  mul_repr : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (𝓞 F) F).range
def orderOf (b : Module.Basis ι F D) (hb : IsOrderBasis b) : Subring D where
  carrier := {x | ∀ i, b.repr x i ∈ (algebraMap (𝓞 F) F).range}
  mul_mem' := by sorry
  one_mem' := hb.one_repr
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
def adelicOrder (b : Module.Basis ι F D) (hb : IsOrderBasis b) : Subring (Df F D) where
  carrier := {x | ∀ i, (rightBasis b).repr x i ∈ FiniteAdeleRing.integralAdeles F}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
def localOrder (b : Module.Basis ι F D) (hb : IsOrderBasis b) (v : HeightOneSpectrum (𝓞 F)) :
    Subring (Dv F D v) where
  carrier := {x | ∀ i, (rightBasis b).repr x i ∈ v.adicCompletionIntegers F}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
def localUnits (b : Module.Basis ι F D) (hb : IsOrderBasis b) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (Dv F D v)ˣ where
  carrier := {u | (u : Dv F D v) ∈ localOrder b hb v ∧
    ((u⁻¹ : (Dv F D v)ˣ) : Dv F D v) ∈ localOrder b hb v}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
theorem rightBasis_repr_toLocal (v : HeightOneSpectrum (𝓞 F)) (x : Df F D) (i : ι) :
    (rightBasis b).repr (toLocal F D v x) i = (rightBasis b).repr x i v := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L9.1** `IsOrderBasis`, `orderOf` (fields), `adelicOrder` (fields), `localOrder` (fields),
  `localUnits` (fields) — [RM] §0.1.4 "An order of `D` is an `𝒪_F`-subalgebra that is a lattice";
  §0.2.3 "`𝒪_D ⊗ ℤ̂ := 𝒪_D ⊗_{𝒪_F} ∏_v 𝒪_v ⊆ D_f`". Lean: coordinates in `𝓞 F`, in `∏ 𝒪_v`, in `𝒪_v`.
  Sketch: closure under multiplication from the structure constants: the `k`-th coordinate of a
  product is `∑_{i,j} c_{ijk} x_i y_j` with `c_{ijk}` integral (`HeightOneSpectrum.
  coe_algebraMap_mem` puts integers of `F` in every `𝒪_v`). Attacks: [4] **generality decision**:
  basis-presented orders only (plan.md decision 5); [SRC] `04_Level.integralTensor` is the same
  choice. [1] is `adelicOrder` independent of the basis presenting a given order? Two bases of one
  order differ by `GL_ι(𝓞 F)`, which preserves integrality of coordinates ✓ (not needed, not
  ticketed). SURVIVED.

- **L9.2** `rightBasis_repr_toLocal` — the coordinates commute with the components. `induction_on`
  + L5.2. SURVIVED.

#### Mathlib lemmas needed

`induction_on`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4, §0.2.3 (module docstring: §0.1.4 (orders), §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/IntegralAdeles.lean`.
- [SRC] (proof idea only, never imported): `04_Level.integralTensor`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-29: DONE. Private `repr_mul_mem` (any basis `c` of an `R`-algebra, any `SubringClass`
  `S`): the `k`-th coordinate of `x * y` is `∑ xᵢ yⱼ c_{ijk}` over the `Finsupp` supports (NO
  `Fintype` needed, which keeps `orderOf` free of `[Fintype ι]` as `mem_orderOf_iff`'s `omit`
  requires). `rightBasis` structure constants are `algebraMap F R c_{ijk}` (`tmul_mul_tmul`,
  `rightBasis_repr_tmul`), integral in `∏ 𝒪_v`/`𝒪_v` by `HeightOneSpectrum.coe_algebraMap_mem`.
  `rightBasis_repr_toLocal`: `induction_on` (same proof as Components' private copy). New public
  `mem_adelicOrder_iff`, `mem_localOrder_iff` (`Iff.rfl`, docstrings). Mathlib renames met:
  `Finsupp.finsetSum_apply` (was `finset_sum_apply`).

### [T028] `mem_adelicOrder_iff_forall`, `incl_mem_adelicOrder_iff`

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T027] · **Type**: proof · **Leaves**: L9.3, L9.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem mem_adelicOrder_iff_forall {x : Df F D} :
    x ∈ adelicOrder b hb ↔ ∀ v, toLocal F D v x ∈ localOrder b hb v := by
  sorry
theorem incl_mem_adelicOrder_iff {x : D} : incl F D x ∈ adelicOrder b hb ↔ x ∈ orderOf b hb := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L9.3** `mem_adelicOrder_iff_forall` — membership is local. Immediate from L9.2 and
  `mem_integralAdeles_iff`. [SRC] `2_LevelTopology.forall_toLocal_mem_localOrder_iff`. SURVIVED.

- **L9.4** `incl_mem_adelicOrder_iff` — [RM] §0.2.1 "`D^× ∩ U₀(1)` is the finite unit group of a
  definite order". Lean: `x ⊗ 1 ∈ 𝒪_D ⊗ ℤ̂ ↔ x ∈ 𝒪_D`. Sketch: an element of `F` integral at every
  finite place is in `𝓞 F` (`HeightOneSpectrum.mem_integers_of_valuation_le_one`). [SRC]
  `2_Level.mem_hurwitzOrder_of_forall_local`. Attacks: [5] the Mathlib lemma is stated for the
  valuation on `K`, ours for `Valued.v` on the completion; bridge by
  `valuedAdicCompletion_eq_valuation'` (verified) ✓. SURVIVED.

#### Mathlib lemmas needed

`HeightOneSpectrum.mem_integers_of_valuation_le_one`, `Valued.v`, `valuedAdicCompletion_eq_valuation'`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1 (module docstring: §0.1.4 (orders), §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/IntegralAdeles.lean`.
- [SRC] (proof idea only, never imported): `2_Level.mem_hurwitzOrder_of_forall_local`, `2_LevelTopology.forall_toLocal_mem_localOrder_iff`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-29: DONE (staged with T027). Locality: `simp only` with `rightBasis_repr_toLocal`, then
  `forall_comm`. Global points: `x ⊗ 1` has coordinates `algebraMap F 𝔸 (b.repr x i)`; an `F`-element
  integral at every `v` is in `𝓞 F` by `HeightOneSpectrum.mem_integers_of_valuation_le_one F c`,
  bridged by `(valuedAdicCompletion_eq_valuation' (v := v) c).symm.trans_le` (term mode).

### [T029] `isCompact_adelicOrder`, `isOpen_adelicOrder`, `isCompact_localOrder` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T028] · **Type**: proof · **Leaves**: L9.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem isCompact_adelicOrder : IsCompact (adelicOrder b hb : Set (Df F D)) := by
  sorry
theorem isOpen_adelicOrder : IsOpen (adelicOrder b hb : Set (Df F D)) := by
  sorry
theorem isCompact_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (localOrder b hb v : Set (Dv F D v)) := by
  sorry
theorem isOpen_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (localOrder b hb v : Set (Dv F D v)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L9.5** `isCompact_adelicOrder`, `isOpen_adelicOrder`, `isCompact_localOrder`,
  `isOpen_localOrder` — [RM] §0.2.3 (route quoted in the substrate). Sketch: preimage of
  `Set.pi univ (fun _ ↦ integralAdeles)` under the homeomorphism L5.3; L6.4; `isCompact_univ_pi`,
  `isOpen_set_pi`. [SRC] `04_Level.isCompact_integralTensor`, `2_LevelTopology.
  isOpen_integralTensor`. SURVIVED.

#### Mathlib lemmas needed

`isCompact_univ_pi`, `isOpen_set_pi`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.3 (module docstring: §0.1.4 (orders), §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/IntegralAdeles.lean`.
- [SRC] (proof idea only, never imported): `04_Level.isCompact_integralTensor`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-29: DONE (staged with T027). Private `coe_adelicOrder`/`coe_localOrder`: the order is
  `rightCoordsL b ⁻¹' univ.pi (fun _ ↦ 𝒪)`; compact via `toHomeomorph.isCompact_preimage` +
  `isCompact_univ_pi`, open via `isOpen_set_pi Set.finite_univ` + `.preimage`.

### [CLEANUP-12] `/cleanup` of `Adelic/IntegralAdeles.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T029] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-13's single inline pass (T027–T031 were staged into one
  build).

### [T030] `U0`, `mem_U0_iff`, `isCompact_U0` and 4 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [CLEANUP-12] · **Type**: proof · **Leaves**: L9.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def U0 : Subgroup (Dfx F D) where
  carrier := {g | (g : Df F D) ∈ adelicOrder b hb ∧ ((g⁻¹ : Dfx F D) : Df F D) ∈ adelicOrder b hb}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
theorem mem_U0_iff {g : Dfx F D} :
    g ∈ U0 b hb ↔
      (g : Df F D) ∈ adelicOrder b hb ∧ ((g⁻¹ : Dfx F D) : Df F D) ∈ adelicOrder b hb :=
  Iff.rfl
theorem isCompact_U0 : IsCompact (U0 b hb : Set (Dfx F D)) := by
  sorry
theorem isOpen_U0 : IsOpen (U0 b hb : Set (Dfx F D)) := by
  sorry
theorem mem_U0_iff_forall {g : Dfx F D} :
    g ∈ U0 b hb ↔ ∀ v, toLocalUnits F D v g ∈ localUnits b hb v := by
  sorry
theorem unitsIncl_mem_U0_iff {x : Dˣ} :
    unitsIncl F D x ∈ U0 b hb ↔ (x : D) ∈ orderOf b hb ∧ ((x⁻¹ : Dˣ) : D) ∈ orderOf b hb := by
  sorry
theorem localIncl_mem_U0_iff (v : HeightOneSpectrum (𝓞 F)) {u : (Dv F D v)ˣ} :
    localIncl F D v u ∈ U0 b hb ↔ u ∈ localUnits b hb v := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L9.6** `U0` (fields), `mem_U0_iff`, `isCompact_U0`, `isOpen_U0`, `mem_U0_iff_forall`,
  `unitsIncl_mem_U0_iff`, `localIncl_mem_U0_iff` — [RM] §0.2.3 "its unit group
  `U₀(1) := (𝒪_D ⊗ ℤ̂)^×` is a compact open subgroup of `D_f^×`". Sketch: L7.1 with L9.5;
  locality from L9.3 applied to `g` and `g⁻¹`, stated with `localUnits`. Attacks: [2] at `w ≠ v`
  the component of `ι_v(u)` is `1 ∈ localUnits` ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.3 (module docstring: §0.1.4 (orders), §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/IntegralAdeles.lean`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-29: DONE (staged with T027). `isCompact_U0`: `Units.isCompact_of_isCompact` (T020) with
  `Module.Finite.of_basis b` supplying the `T1Space`/`ContinuousMul` instances of `D_f`;
  `mem_U0_iff_forall` = `(and_congr ..).trans forall_and.symm` (term mode, by defeq);
  `localIncl_mem_U0_iff` via `toLocalUnits_localIncl(_of_ne)` and an `eq_or_ne` split.

### [T031] `integralMatrices`, `integralGL`, `mem_integralGL_iff` and 5 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T030] · **Type**: proof · **Leaves**: L9.7, L9.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def integralMatrices : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) where
  carrier := {m | ∀ i j, m i j ∈ v.adicCompletionIntegers F}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
def integralGL : Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈ integralMatrices v ∧
    ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈
      integralMatrices v}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
theorem mem_integralGL_iff {g : GL (Fin 2) (v.adicCompletion F)} :
    g ∈ integralGL v ↔
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈ integralMatrices v ∧
        Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  sorry
def RigidificationAt.IsIntegral : Prop :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)) '' (localOrder b hb v : Set (Dv F D v)) =
    (integralMatrices v : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
theorem toGL_mem_integralGL (hint : RigidificationAt.IsIntegral b hb v) {g : Dfx F D}
    (hg : g ∈ U0 b hb) : toGL F D v g ∈ integralGL v := by
  sorry
theorem unitAt_mem_U0_iff (hint : RigidificationAt.IsIntegral b hb v)
    {m : GL (Fin 2) (v.adicCompletion F)} : unitAt F D v m ∈ U0 b hb ↔ m ∈ integralGL v := by
  sorry
theorem mem_U0_of_toGL (hint : RigidificationAt.IsIntegral b hb v) {g : Dfx F D}
    (hv : toGL F D v g ∈ integralGL v)
    (haway : ∀ w, w ≠ v → toLocalUnits F D w g ∈ localUnits b hb w) : g ∈ U0 b hb := by
  sorry
theorem det_rigidification_mem (hint : RigidificationAt.IsIntegral b hb v) {x : Dv F D v}
    (hx : x ∈ localOrder b hb v) :
    (RigidificationAt.equiv (F := F) (D := D) (v := v) x).det ∈ v.adicCompletionIntegers F := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L9.7** `integralMatrices`, `integralGL` (fields), `mem_integralGL_iff`,
  `RigidificationAt.IsIntegral` — [RM] §0.1.3 "carrying `𝒪_D ⊗ 𝒪_𝔭` onto `M₂(𝒪_𝔭)`". Lean:
  `θ_v '' localOrder = integralMatrices`. `mem_integralGL_iff`: `g, g⁻¹` integral iff `g` integral
  with `v(det g) = 1` (`Matrix.adjugate_fin_two`). SURVIVED.

- **L9.8** `toGL_mem_integralGL`, `unitAt_mem_U0_iff`, `mem_U0_of_toGL`, `det_rigidification_mem` —
  [RM] §0.2.3 "at a split place with rigidification its `v`-component is `GL₂(𝒪_v)`"; §0.1.3 "the
  reduced norm of `𝒪_D ⊗ 𝒪_𝔭` lands in `𝒪_𝔭`". [SRC] `2_Level.unitAt_mem_U0`,
  `.mem_U0_of_toMatrix`. Attacks: [4] the reduced norm clause is rendered as
  `det (θ_v x) ∈ 𝒪_v`, the form in which it is consumed; with L3.5 it is the reduced norm when
  `D = ℍ[F,a,b]` ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.adjugate_fin_two`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3, §0.2.3 (module docstring: §0.1.4 (orders), §0.2.3).
- Literature: the quotations of the module docstring of `Adelic/IntegralAdeles.lean`.
- [SRC] (proof idea only, never imported): `2_Level.unitAt_mem_U0`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (12) **One conclusion per declaration.**

#### Progress

- 2026-09-29: DONE (staged with T027). `mem_integralGL_iff`: `det` of an integral 2×2 matrix is
  integral (`det_fin_two`); `v(det g)·v(det g⁻¹) = 1` with both `≤ 1` forces `= 1`
  (`Left.mul_lt_one_of_lt_of_le`); conversely `g⁻¹ = (det g)⁻¹ • adj g` (`Matrix.coe_units_inv`,
  `inv_def`, `Ring.inverse_eq_inv`) with `adjugate_fin_two` entries. `IsIntegral` (a `Prop` def) is
  used through `Set.ext_iff.mp hint` (elaborates by unfolding; `rw [hint]` would not see an `Eq`).
  Trap: `show Valued.v _ ≤ 1` defaults `1 : ℕ` (stuck `Valued ?m ℕ`) — write the term.

### [CLEANUP-13] `/cleanup` of `Adelic/IntegralAdeles.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/IntegralAdeles.lean` · **Depends on**: [T031] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, axioms standard (19 declarations checked), `runLinter`
  passes, no build warnings, lines ≤ 100 codepoints. Unused `[Fintype ι]` REMOVED (`omit … in`,
  before the docstring) from `rightBasis_repr_toLocal`, `mem_adelicOrder_iff_forall`,
  `incl_mem_adelicOrder_iff`, `mem_U0_iff_forall`, `unitsIncl_mem_U0_iff`, `localIncl_mem_U0_iff`,
  `toGL_mem_integralGL`, `unitAt_mem_U0_iff`, `mem_U0_of_toGL`, `det_rigidification_mem` (only the
  compactness/openness statements use finiteness of `ι`). Module docstring lists every main
  declaration; docstrings added to `isOpen_localOrder`, `unitAt_mem_U0_iff`.

### [T032] `ideleNorm`, `ideleNorm_apply`, `finite_mulSupport_norm` and 3 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T031], [T015], [T006] · **Type**: proof · **Leaves**: L10.1, L10.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def ideleNorm : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℝ where
  toFun x := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖
  map_one' := by sorry
  map_mul' := by sorry
theorem ideleNorm_apply (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F x = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := rfl
theorem finite_mulSupport_norm (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦
      ‖(x : FiniteAdeleRing (𝓞 F) F) v‖).Finite := by
  sorry
theorem ideleNorm_pos (x : (FiniteAdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x := by
  sorry
theorem exists_rat_ideleNorm (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ q : ℚ, 0 < q ∧ ideleNorm F x = (q : ℝ) := by
  sorry
theorem ideleNorm_eq_one_of_forall_norm_eq_one {x : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hx : ∀ v, ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ = 1) : ideleNorm F x = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L10.1** `ideleNorm` (fields), `ideleNorm_apply`, `finite_mulSupport_norm`, `ideleNorm_pos` —
  [RM] §0.2.4 "`|nrd(g)|_f := ∏_v |nrd(g)_v|_v`"; [Voi21, 27.6.12] (quoted). Sketch: all but
  finitely many components of a unit adele have valuation `1`
  (`FiniteAdeleRing.unitsEquiv_finite_valued_eq_one`), hence norm `1`
  (`Valued.toNormedField.norm_le_one_iff` both ways); `finprod_mul_distrib`. Attacks: [2] target
  `ℝ` as a multiplicative monoid: `map_one'` is `finprod_eq_one_of_forall_eq_one` ✓. [4] the target
  is `ℝ` with a positivity lemma rather than `ℝ_{>0}`, to keep `MonoidHom` composition with
  `Units.map` cheap ✓. SURVIVED.

- **L10.2** `exists_rat_ideleNorm`, `ideleNorm_eq_one_of_forall_norm_eq_one` — [RM] §0.2.4
  "`∈ ℚ_{>0}`". Sketch: each local norm is a power of `(absNorm v)⁻¹`
  (`rankOne_hom'_def`, `toNNReal`). SURVIVED.

#### Mathlib lemmas needed

`FiniteAdeleRing.unitsEquiv_finite_valued_eq_one`, `Valued.toNormedField.norm_le_one_iff`, `finprod_mul_distrib`, `map_one'`, `finprod_eq_one_of_forall_eq_one`, `rankOne_hom'_def`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.4 (module docstring: §0.2.4).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-29: DONE. The norm on `F_v` is `Valued.toNormedField`'s; integrality ↔ `‖·‖ ≤ 1` via
  `Valued.toNormedField.norm_le_one_iff (Γ₀ := WithZero (Multiplicative ℤ))`. A component whose value
  and inverse are integral has norm `1` (product of the two norms is `1`); finiteness of the
  `mulSupport` from the restricted-product property of `x` and `x⁻¹` (`(x : 𝔸).2.and …`,
  `Filter.eventually_cofinite`) — `unitsEquiv_finite_valued_eq_one` not needed. `map_mul'` by
  `finprod_mul_distrib` (`HasFiniteMulSupport` is a def, unfolds). Rationality: `FinitePlace.norm_def`
  + `WithZeroMulInt.toNNReal_neg_apply` give `‖z‖ = absNorm(v)^n`; `choose` + `MonoidHom.map_finprod`
  for `Rat.castHom`. Trap: after `push_cast` the two sides are syntactically equal but differ in
  instance paths (NNReal/Rat casts) — close with a default-transparency `rfl`.

### [T033] `continuous_ideleNorm`, `ideleNorm_algebraMap`

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T032] · **Type**: proof · **Leaves**: L10.3, L10.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem continuous_ideleNorm : Continuous (ideleNorm F) := by
  sorry
theorem ideleNorm_algebraMap (x : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom x) =
      (|(Algebra.norm ℚ (x : F) : ℚ)| : ℝ)⁻¹ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L10.3** `continuous_ideleNorm` — [RM] §0.2.4 "a continuous character". Sketch: trivial on the
  open subgroup `{x | x, x⁻¹ ∈ ∏ 𝒪_v}` (L7.1, L6.4), and a homomorphism that is trivial on an open
  subgroup is continuous. SURVIVED.

- **L10.4** `ideleNorm_algebraMap` — [RM] §0.2.4 "by the product formula". Lean: for `x : Fˣ`,
  `|x|_f = |N_{F/ℚ} x|⁻¹`. Sketch: `FinitePlace.prod_eq_inv_abs_norm`, reindexed along
  `FinitePlace.equivHeightOneSpectrum` (`finprod_comp_equiv`), with `FinitePlace.norm_embedding`.
  Attacks: [5] three names verified; the reindexing is the proof of Mathlib's own lemma, read
  backwards ✓. SURVIVED.

#### Mathlib lemmas needed

`FinitePlace.prod_eq_inv_abs_norm`, `FinitePlace.equivHeightOneSpectrum`, `finprod_comp_equiv`, `FinitePlace.norm_embedding`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.4 (module docstring: §0.2.4).
- Literature: the quotations of the module docstring of `Adelic/Norm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-29: DONE. Continuity: `continuous_of_continuousAt_one` + `ContinuousAt.congr` with the
  constant `1` on the open subgroup `{x | x, x⁻¹ ∈ ∏ 𝒪_v}` (`Units.isOpen_of_isOpen`, T020). Product
  formula: `FinitePlace.prod_eq_inv_abs_norm`, reindexed by `finprod_comp_equiv
  FinitePlace.equivHeightOneSpectrum.symm` and `equivHeightOneSpectrum_symm_apply`; Mathlib's RHS
  has the cast outside `|·|⁻¹`, so `push_cast` + `rfl`.

### [T034] `adelicNrd`, `coe_adelicNrd_unitsIncl`, `adelicNrd_apply` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T033] · **Type**: proof · **Leaves**: L10.5, L10.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def adelicNrd : Dfx F ℍ[F,a,b] →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (nrdBaseChange F a b (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
theorem coe_adelicNrd_unitsIncl (x : (ℍ[F,a,b])ˣ) :
    ((adelicNrd F a b (unitsIncl F ℍ[F,a,b] x) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (nrd (x : ℍ[F,a,b])) := by
  sorry
theorem adelicNrd_apply (g : Dfx F ℍ[F,a,b]) (v : HeightOneSpectrum (𝓞 F)) :
    ((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      nrdBaseChange F a b (v.adicCompletion F) (toLocal F ℍ[F,a,b] v (g : Df F ℍ[F,a,b])) := by
  sorry
theorem adelicNrd_apply_eq_det (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (g : Dfx F ℍ[F,a,b]) :
    ((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (toMatrix F ℍ[F,a,b] v g).det := by
  sorry
theorem det_toMatrix_unitsIncl (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (x : (ℍ[F,a,b])ˣ) :
    (toMatrix F ℍ[F,a,b] v (unitsIncl F ℍ[F,a,b] x)).det =
      algebraMap F (v.adicCompletion F) (nrd (x : ℍ[F,a,b])) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L10.5** `adelicNrd`, `coe_adelicNrd_unitsIncl`, `adelicNrd_apply` — [RM] §0.2.4 "The reduced
  norm extends to `nrd : D_f^× →* (𝔸_F^f)^×`". `Units.map` of L3.3; components by L3.3's
  `nrdBaseChange_map` at `f = evalAlgHom F v`. SURVIVED.

- **L10.6** `adelicNrd_apply_eq_det`, `det_toMatrix_unitsIncl` — [RM] §0.2.4 "with
  `nrd ∘ ι_𝔭 = det` at `𝔭`"; §0.1.3 "`det (θ_𝔭 x) = nrd x` for `x ∈ D`". Sketch: L3.5 at
  `R = F_v`: `2`, `a`, `b` are units of the field `F_v` because `F → F_v` is injective and `F` has
  characteristic `0`. Attacks: [3] `a ≠ 0`, `b ≠ 0` are necessary for L1.6 and automatic when a
  rigidification exists (a degenerate algebra is not split) — kept explicit, cheaper than deriving.
  SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3, §0.2.4 (module docstring: §0.2.4).
- Literature: the quotations of the module docstring of `Adelic/Norm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-29: DONE. `coe_adelicNrd_unitsIncl` = `nrdBaseChange_tmul_one`; `adelicNrd_apply` =
  `(nrdBaseChange_map (evalAlgHom F v) _).symm` (by defeq of `toLocal`); `adelicNrd_apply_eq_det` via
  `det_eq_nrdBaseChange` with `2, a, b` units of `F_v` (injectivity of `F → F_v`, `map_ofNat`).

### [CLEANUP-14] `/cleanup` of `Adelic/Norm.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T034] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-15 (T032–T036 written in one pass).

### [T035] `continuous_adelicNrd`, `normClass`, `continuous_normClass` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [CLEANUP-14] · **Type**: proof · **Leaves**: L10.7, L10.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem continuous_adelicNrd : Continuous (adelicNrd F a b) := by
  sorry
def normClass : Dfx F ℍ[F,a,b] →* ℝ := (ideleNorm F).comp (adelicNrd F a b)
theorem continuous_normClass : Continuous (normClass F a b) := by
  sorry
theorem normClass_pos (g : Dfx F ℍ[F,a,b]) : 0 < normClass F a b g := by
  sorry
theorem normClass_eq_one_of_isCompact {U : Subgroup (Dfx F ℍ[F,a,b])}
    (hU : IsCompact (U : Set (Dfx F ℍ[F,a,b]))) {g : Dfx F ℍ[F,a,b]} (hg : g ∈ U) :
    normClass F a b g = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L10.7** `continuous_adelicNrd`, `normClass`, `continuous_normClass`, `normClass_pos` — L3.4 +
  `Continuous.units_map`; L10.3. SURVIVED.

- **L10.8** `normClass_eq_one_of_isCompact` — [RM] §0.2.4 "trivial on `U₀(1)` and on every compact
  open subgroup". Sketch: the image of a compact subgroup under a continuous homomorphism to
  `(ℝ, ·)` with positive values is a compact subgroup of `ℝ_{>0}`; if it contained `c ≠ 1`, the
  powers `c^n`, `n ∈ ℤ`, would be unbounded or accumulate at `0 ∉` image. Attacks: [1] is openness
  needed? No — compactness alone ✓ (the roadmap's "compact open" is weakened to "compact"). [4]
  avoids the integrality of `nrd` on an order, which for a general basis-presented order would need
  L2.4 over `𝓞 F`. SURVIVED.

#### Mathlib lemmas needed

`Continuous.units_map`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.4 (module docstring: §0.2.4).
- Literature: the quotations of the module docstring of `Adelic/Norm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-29: DONE. `continuous_adelicNrd` = `Continuous.units_map` of `continuous_nrdBaseChange`.
  Compact subgroups: the image under the continuous `normClass` is `BddAbove`; a value `> 1` has
  unbounded powers (`pow_unbounded_of_one_lt`), so every value is `≤ 1`, and `c(g⁻¹)·c(g) = 1`
  forces `c(g) = 1` (openness not needed, as planned).

### [T036] `normClass_unitAt`, `normClass_eq_prod_mul_finprod`, `normClass_unitsIncl` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T035] · **Type**: proof · **Leaves**: L10.9, L10.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem normClass_unitAt (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    [RigidificationAt F ℍ[F,a,b] v] (m : GL (Fin 2) (v.adicCompletion F)) :
    normClass F a b (unitAt F ℍ[F,a,b] v m) =
      ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ := by
  sorry
theorem normClass_eq_prod_mul_finprod (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : Dfx F ℍ[F,a,b]) :
    normClass F a b g =
      (∏ v ∈ S, ‖((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) :
        FiniteAdeleRing (𝓞 F) F) v‖) *
      ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S),
        ‖((adelicNrd F a b g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ := by
  sorry
theorem normClass_unitsIncl (x : (ℍ[F,a,b])ˣ) :
    normClass F a b (unitsIncl F ℍ[F,a,b] x) =
      (|(Algebra.norm ℚ (nrd (x : ℍ[F,a,b])) : ℚ)| : ℝ)⁻¹ := by
  sorry
theorem normClass_unitsIncl_rat {a b : ℚ} (h : IsTotallyDefinite a b) (x : (ℍ[ℚ,a,b])ˣ) :
    normClass ℚ a b (unitsIncl ℚ ℍ[ℚ,a,b] x) = ((nrd (x : ℍ[ℚ,a,b]) : ℚ) : ℝ)⁻¹ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.2 The adelic group", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L10.9** `normClass_unitAt`, `normClass_eq_prod_mul_finprod` — [RM] §0.2.4
  "`|nrd(g)|_f = ∏_{v ∤ p} |nrd(g)_v|_v · ∏_{𝔭 ∈ 𝔓} |det θ_𝔭(g)|_𝔭`". Lean: the split of the
  `finprod` at a finite set `S`; with L10.6 the first factor is the product of `‖det θ_v g‖`.
  Attacks: [5] **name miss repaired**: `finprod_mem_mul_finprod_mem_compl` does not exist; route:
  `finprod_eq_prod_of_mulSupport_subset` on `S ∪ supp`, then `Finset.prod_sdiff` — to be verified at
  ticket time. SURVIVED.

- **L10.10** `normClass_unitsIncl`, `normClass_unitsIncl_rat` — [RM] §0.2.4
  "`|nrd(γ)|_f = N_{F/ℚ}(nrd γ)^{−1}` for `γ ∈ D^×`; for `F = ℚ` […]". Sketch: L10.5, L10.4;
  `Algebra.norm_self` and positivity of `nrd` (L2.1 at `σ = Rat.castHom ℝ`). Attacks: [4] **roadmap
  wording**: the README writes the `F = ℚ` case as "`|nrd(γ)|_f · det θ_p(γ) = 1`", mixing a real and
  a `p`-adic number; the Lean statement is `normClass γ = (nrd γ)⁻¹` in `ℝ`, and
  `det θ_p(γ) = nrd γ` is L10.6 — no defect, the README sentence is loose, not false. SURVIVED.

#### Mathlib lemmas needed

`finprod_mem_mul_finprod_mem_compl`, `finprod_eq_prod_of_mulSupport_subset`, `Finset.prod_sdiff`, `Algebra.norm_self`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.4 (module docstring: §0.2.4).
- Literature: the quotations of the module docstring of `Adelic/Norm.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-29: DONE. `normClass_unitAt`: `finprod_eq_single` at `v` (away from `v` the component
  is `nrd(1) = 1` by `toLocalUnits_localIncl_of_ne`), then `adelicNrd_apply_eq_det`, `coe_toGL`,
  `toGL_unitAt`. Split: private `finprod_eq_prod_mul_finprod_notMem` via
  `finprod_mem_union' disjoint_compl_right` + `finprod_mem_coe_finset` (the planning-time name
  `finprod_mem_mul_finprod_mem_compl` indeed does not exist). `normClass_unitsIncl_rat`: the
  `Algebra ℚ ℚ` instance in the statement is the general-`F` one, not `Algebra.id` — rewrite through
  `Subsingleton.elim` before `Algebra.norm_self`; the `|·|` sits inside the cast to `ℝ`.

### [CLEANUP-15] `/cleanup` of `Adelic/Norm.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Adelic/Norm.lean` · **Depends on**: [T036] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, axioms standard (12 declarations), `runLinter` passes, no
  build warnings, lines ≤ 100; module docstring lists every main result; docstrings added to
  `ideleNorm_pos`, `continuous_adelicNrd`, `normClass_pos`. Rebuilt clean after the docstring edit.

### [T037] `monoidM`, `mem_monoidM_iff`, `iwahori` and 8 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L11.1, L11.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def monoidM (γ : Γ₀) (hγ : γ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ γ ∧ Valued.v (g 1 1) = 1 ∧
    g.det ≠ 0}
  mul_mem' := by sorry
  one_mem' := by sorry
theorem mem_monoidM_iff {γ : Γ₀} {hγ : γ < 1} {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ monoidM K γ hγ ↔
      (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ γ ∧ Valued.v (g 1 1) = 1 ∧ g.det ≠ 0 :=
  Iff.rfl
def iwahori (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | (∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1) ∧
    Valued.v (g : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ≤ γ}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
def iwahoriOne (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ iwahori K γ ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ γ}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
def iwahoriPrincipal (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ iwahori K γ ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ≤ γ ∧
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ γ}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
theorem iwahori_mono {γ γ' : Γ₀} (h : γ ≤ γ') : iwahori K γ ≤ iwahori K γ' := by
  sorry
theorem monoidM_mono {γ γ' : Γ₀} (hγ : γ < 1) (hγ' : γ' < 1) (h : γ ≤ γ') :
    monoidM K γ hγ ≤ monoidM K γ' hγ' := by
  sorry
theorem coe_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {g : GL (Fin 2) K} (hg : g ∈ iwahori K γ) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ := by
  sorry
theorem mem_iwahori_iff {γ : Γ₀} (hγ : γ < 1) {g : GL (Fin 2) K} :
    g ∈ iwahori K γ ↔ (g : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ ∧
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ := by
  sorry
theorem iwahoriPrincipal_le_iwahoriOne (γ : Γ₀) : iwahoriPrincipal K γ ≤ iwahoriOne K γ := by
  sorry
theorem iwahoriOne_le_iwahori (γ : Γ₀) : iwahoriOne K γ ≤ iwahori K γ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.1** `monoidM` (fields), `mem_monoidM_iff` — [RM] §0.4.1 "the monoid
  `M_t := {γ ∈ M₂(𝒪) | ϖ^t ∣ c, ϖ ∤ d, det γ ≠ 0}` (Buzzard §9, p. 68: '`M_t` is a monoid under
  multiplication')". Lean: over `[Valued K Γ₀]`, threshold `γ < 1`: entries `≤ 1`, `v(c) ≤ γ`,
  `v(d) = 1`, `det ≠ 0`. Sketch: substrate; `v(cb' + dd') = 1` by the ultrametric equality
  (`Valuation.map_add_eq_of_lt_left`-style) since `v(cb') ≤ γ < 1 = v(dd')`. Attacks: [3] `γ < 1` is
  necessary: at `γ = 1` both `((0 1), (1 1))` and `((1 1), (1 −1))` satisfy the four conditions,
  and their product has lower-right entry `1·1 + 1·(−1) = 0`, so the monoid law fails; hypothesis
  kept. [4] [SRC] `QMF/Slash/01_Sigma0.Sigma0'` is this monoid. SURVIVED.

- **L11.2** `iwahori`, `iwahoriOne`, `iwahoriPrincipal` (fields), the three inclusions,
  `iwahori_mono`, `monoidM_mono`, `coe_mem_monoidM`, `mem_iwahori_iff` — [RM] §0.4.1
  "`Iw(𝔭^t) := {γ ∈ GL₂(𝒪) | ϖ^t ∣ c}` […] `Iw(𝔭^t) ⊆ M_t`, `M_{t+1} ⊆ M_t`". Lean: `Iw(γ)` is
  "integral, `v(det) = 1`, `v(c) ≤ γ`"; `Iw₁`: also `v(d − 1) ≤ γ`; `Iw₁₁`: also `v(a − 1) ≤ γ`.
  Sketch: inverse by `Matrix.adjugate_fin_two`; for `Iw₁`, `(g⁻¹)_{11} − 1 = (a(1 − d) + bc)/det`;
  for `Iw₁₁`, `(g⁻¹)_{00} − 1 = (d(1 − a) + bc)/det`. `mem_iwahori_iff` (`γ < 1`): the units of
  `M(γ)` — from `v(det) = 1` and `v(bc) < 1`, `v(ad) = 1`. Attacks: [2] `γ = 0`: `c = 0`, the Borel
  subgroup, still a subgroup ✓. `γ > 1`: the condition on `c` is implied by integrality ✓. [3]
  `iwahori` needs no bound on `γ`; only `coe_mem_monoidM` and `mem_iwahori_iff` need `γ < 1` ✓.
  SURVIVED.

#### Mathlib lemmas needed

`Valuation.map_add_eq_of_lt_left`, `Matrix.adjugate_fin_two`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.1 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.
- [SRC] (proof idea only, never imported): `QMF/Slash/01_Sigma0.Sigma0'`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE (all of Level/Local.lean T037–T043 in one pass; 3 fix rounds). Valuation
  arithmetic by private `v_add_le`/`v_sub_le`/`v_mul_le_left/right`; inverse entries via
  `Matrix.coe_units_inv` + `inv_def` + `adjugate_fin_two` (`rfl` entry lemmas). `M(γ)` closed under
  products by `Valuation.map_add_eq_of_lt_right` (`v(cb') ≤ γ < 1 = v(dd')`). `mem_iwahori_iff`: `v(d) = 1`
  from `v(det) = 1` and `v(bc) < 1`; the converse from `v(det g)·v(det g⁻¹) = 1`.

### [T038] `iwahoriOne_normal`, `iwahoriPrincipal_normal`, `ballIdeal` and 3 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T037] · **Type**: proof · **Leaves**: L11.3, L11.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem iwahoriOne_normal (γ : Γ₀) : ((iwahoriOne K γ).subgroupOf (iwahori K γ)).Normal := by
  sorry
theorem iwahoriPrincipal_normal (γ : Γ₀) :
    ((iwahoriPrincipal K γ).subgroupOf (iwahori K γ)).Normal := by
  sorry
def ballIdeal (γ : Γ₀) : Ideal (Valued.v : Valuation K Γ₀).integer where
  carrier := {x | Valued.v (x : K) ≤ γ}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
def lowerRightResidue (γ : Γ₀) :
    iwahori K γ →* ((Valued.v : Valuation K Γ₀).integer ⧸ ballIdeal K γ)ˣ where
  toFun g :=
    ⟨Ideal.Quotient.mk _ ⟨(g : GL (Fin 2) K).1 1 1, by sorry⟩,
      Ideal.Quotient.mk _ ⟨((g : GL (Fin 2) K)⁻¹).1 1 1, by sorry⟩, by sorry, by sorry⟩
  map_one' := by sorry
  map_mul' := by sorry
theorem ker_lowerRightResidue (γ : Γ₀) :
    (lowerRightResidue K γ).ker = (iwahoriOne K γ).subgroupOf (iwahori K γ) := by
  sorry
theorem lowerRightResidue_surjective {γ : Γ₀} (hγ : γ < 1) :
    Function.Surjective (lowerRightResidue K γ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.3** `iwahoriOne_normal`, `iwahoriPrincipal_normal` — [RM] §0.3.1 "`U₁(𝔫) ⊴ U₀(𝔫)`". Kernels
  of L11.4's character and of its two-entry analogue; or directly: conjugation preserves the
  diagonal residues. SURVIVED.

- **L11.4** `ballIdeal` (fields), `lowerRightResidue` (fields), `ker_lowerRightResidue`,
  `lowerRightResidue_surjective` — [RM] §0.3.1 "with quotient `(𝒪_F / 𝔫)^×` via
  `((a b), (c d)) ↦ d`". Lean: `Iw(γ) →* (𝒪/𝔞_γ)^×`, kernel `Iw₁(γ)`, surjective for `γ < 1`.
  Sketch: multiplicative because `cb' ∈ 𝔞_γ`; inverse `(g⁻¹)_{11}` because `(g⁻¹)_{10} b ∈ 𝔞_γ`;
  surjective through `diag(1, d)`, a lift `d` of a unit being a unit since `𝔞_γ ⊆ 𝔪`. Attacks: [2]
  `γ ≥ 1`: `𝔞_γ = ⊤`, the quotient is the zero ring, whose unit group is trivial; the kernel
  statement still holds, surjectivity is trivially true but stated for `γ < 1` only ✓. [4] **scope**:
  the target is local, `(𝒪_v/𝔞)^×`, not `(𝒪_F/𝔫)^×` (plan.md decision 6). SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.1 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. The diagonal residues are multiplicative on `Iw(γ)`:
  `v((xy)₁₁ − x₁₁y₁₁) ≤ γ` (and `₀₀`); closure of `Iw₁`/`Iw₁₁` and NORMALITY follow by explicit `ring`
  identities (no residue homomorphism needed before its definition). `lowerRightResidue` fields via
  `Ideal.Quotient.eq`; surjectivity through `diag(1, d)` with `v(d) = 1` forced by `v(de − 1) ≤ γ < 1`.

### [T039] `diagonal_mem_monoidM`, `smul_one_mem_monoidM_iff`, `isOpen_iwahori` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T038] · **Type**: proof · **Leaves**: L11.5, L11.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem diagonal_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {x d : K} (hx : Valued.v x ≤ 1) (hx0 : x ≠ 0)
    (hd : Valued.v d = 1) : Matrix.diagonal ![x, d] ∈ monoidM K γ hγ := by
  sorry
theorem smul_one_mem_monoidM_iff {γ : Γ₀} (hγ : γ < 1) {x : K} :
    x • (1 : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ ↔ Valued.v x = 1 := by
  sorry
theorem isOpen_iwahori {γ : Γ₀} (hγ : γ ≠ 0) : IsOpen (iwahori K γ : Set (GL (Fin 2) K)) := by
  sorry
theorem isOpen_iwahoriOne {γ : Γ₀} (hγ : γ ≠ 0) :
    IsOpen (iwahoriOne K γ : Set (GL (Fin 2) K)) := by
  sorry
theorem isOpen_iwahoriPrincipal {γ : Γ₀} (hγ : γ ≠ 0) :
    IsOpen (iwahoriPrincipal K γ : Set (GL (Fin 2) K)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.5** `diagonal_mem_monoidM`, `smul_one_mem_monoidM_iff` — [RM] §0.4.1 "the diagonal matrices
  `diag(a, d)` with `a ≠ 0` and `d` a unit lie in `M_t`"; §0.4.4 "the scalars `ι_𝔭(u · 1)` for
  `u ∈ 𝒪^×` lie in `Δ_t` […] `ι_𝔭(ϖ · 1)` does not". Attacks: [1] the roadmap's "`a ≠ 0`" omits
  integrality of `a`; the Lean statement has `v(x) ≤ 1` — **roadmap looseness recorded**, the
  statement is the correct one (`diag(ϖ⁻¹, 1) ∉ M_t`). SURVIVED.

- **L11.6** `isOpen_iwahori`, `isOpen_iwahoriOne`, `isOpen_iwahoriPrincipal` — for `γ ≠ 0`. Sketch:
  entries and determinant are continuous on `GL₂(K)` (units topology); `{x | v x ≤ γ}` is open for
  `γ ≠ 0` (`Valued.isClopen_closedBall`) and `{x | v x = 1}` is open. Attacks: [3] `γ ≠ 0` is
  necessary: the Borel subgroup is not open ✓. SURVIVED.

#### Mathlib lemmas needed

`Valued.isClopen_closedBall`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.1, §0.4.4 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE, WITH A B2 REPAIRED IN PLACE (logged): `isOpen_iwahori*` were false for general
  `Γ₀` (Mathlib's `Valued` topology is generated by `ValueGroup₀`); hypothesis now
  `∃ x : K, x ≠ 0 ∧ Valued.v x ≤ γ`. Openness of `{v ≤ γ}`, `{v = 1}` via `Valued.mem_nhds` +
  `Units.mk0 (v.restrict x)` + `Valuation.restrict_lt_iff`; entries and `det` continuous
  (`Continuous.matrix_elem`, `matrix_det`). Rename met: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`.

### [CLEANUP-16] `/cleanup` of `Level/Local.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T039] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-18 (whole file written and cleaned in one pass).

### [T040] `etaGL`, `lowerUnip`, `etaRep` and 7 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [CLEANUP-16] · **Type**: proof · **Leaves**: L11.7, L11.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def etaGL (ϖ : K) (hϖ : ϖ ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![ϖ, 1]) (by sorry)
def lowerUnip (c : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; c, 1] (by sorry)
def etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) : GL (Fin 2) K :=
  etaGL ϖ hϖ * lowerUnip (α * ϖ ^ t)
def upperRep (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![ϖ, β; 0, 1] (by sorry)
theorem coe_etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K) = !![ϖ, 0; α * ϖ ^ t, 1] := by
  sorry
theorem det_etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K).det = ϖ := by
  sorry
theorem coe_etaGL_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ ≤ 1) :
    (etaGL ϖ hϖ : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ := by
  sorry
theorem etaGL_not_unit {γ : Γ₀} (hγ : γ < 1) {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) :
    ((etaGL ϖ hϖ)⁻¹ : GL (Fin 2) K).1 ∉ monoidM K γ hγ := by
  sorry
theorem lowerUnip_mem_iwahoriPrincipal {γ : Γ₀} {c : K} (hc : Valued.v c ≤ γ) (hγ : γ ≤ 1) :
    lowerUnip c ∈ iwahoriPrincipal K γ := by
  sorry
theorem coe_etaRep_mem_monoidM {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {α : K} (hα : Valued.v α ≤ 1) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K) ∈
      monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.7** `etaGL`, `lowerUnip`, `etaRep`, `upperRep` (the `det ≠ 0` fields), `coe_etaRep`,
  `det_etaRep` — [RM] §0.4.2 "The representatives are `x_α := η u_α` with
  `u_α := ((1 0), (α ϖ^t 1)) ∈ U_𝔭`, so that `x_α = ((ϖ 0), (α ϖ^t 1))`, `det x_α = ϖ`".
  `Matrix.det_fin_two`. SURVIVED.

- **L11.8** `coe_etaGL_mem_monoidM`, `etaGL_not_unit`, `lowerUnip_mem_iwahoriPrincipal`,
  `coe_etaRep_mem_monoidM` — [RM] §0.4.1 "`η := diag(ϖ, 1) ∈ M_t` is not a unit of `M_t`"; §0.4.2
  "`x_α ∈ M_t`". `η⁻¹ = diag(ϖ⁻¹, 1)` has `v(ϖ⁻¹) > 1`. Attacks: [3] `etaGL_not_unit` needs
  `v ϖ < 1` strictly (for `v ϖ = 1`, `η ∈ Iw`) ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.det_fin_two`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.1, §0.4.2 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. Private `coe_etaGL`/`coe_lowerUnip`/`coe_upperRep` (`rfl`) and `det_*`. Trap:
  `Matrix.cons_val_one` now gives `vecCons a u 1 = u 0`, so `![ϖ, 1] 1` needs `cons_val_zero` next.

### [T041] `inv_mul_etaGL_mul_mem_iwahoriPrincipal`, `existsUnique_etaRep`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T040] · **Type**: proof · **Leaves**: L11.9, L11.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem inv_mul_etaGL_mul_mem_iwahoriPrincipal {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    {t : ℕ} (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {α : K}
    (hα : Valued.v α ≤ 1)
    (h : etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹ ∈ iwahori K (Valued.v ϖ ^ t)) :
    u⁻¹ * (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹) ∈ iwahoriPrincipal K (Valued.v ϖ ^ t) := by
  sorry
theorem existsUnique_etaRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) {u : GL (Fin 2) K}
    (hu : u ∈ U) : ∃! i, etaGL ϖ hϖ * u * (etaRep ϖ hϖ t (r i))⁻¹ ∈ U := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.9** `inv_mul_etaGL_mul_mem_iwahoriPrincipal` — substrate: the correction factor is
  principal. Lean: for `u ∈ Iw(γ)`, `γ = v(ϖ)^t`, `t ≥ 1`, `v α ≤ 1`, if
  `η u x_α⁻¹ ∈ Iw(γ)` then `u⁻¹ (η u x_α⁻¹) ∈ Iw₁₁(γ)`. Sketch: both factors are in `Iw(γ)`, and the
  diagonal residues are multiplicative there (L11.4 and its `a`-analogue); `u' := η u x_α⁻¹` has
  diagonal `(a − bαϖ^t, d)`. Attacks: [3] `v α ≤ 1` is used (`bαϖ^t ∈ 𝔞_γ`) ✓. Added by the
  adversarial pass as the hinge of L11.10 and L14.8. SURVIVED.

- **L11.10** `existsUnique_etaRep` — [RM] §0.4.2 "`U_𝔭 η U_𝔭 = ∐_{α ∈ 𝒪/𝔭} U_𝔭 · ((ϖ 0), (α ϖ^t 1))`
  as right cosets"; [Buz07, proof of Lemma 12.1] (quoted). Lean: for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`, a
  uniformiser `ϖ` (`hunif : v x < 1 → v x ≤ v ϖ`), `t ≥ 1`, and a residue system `r`
  (`∀ x, v x ≤ 1 → ∃! i, v (x − r i) < 1`): `∀ u ∈ U, ∃! i, η u (x_{r i})⁻¹ ∈ U`. Sketch:
  substrate; existence: the residue of `c/(dϖ^t)`, then L11.9 and `hlow`; uniqueness: membership in
  `U ≤ Iw(γ)` forces the congruence, `hr`. Attacks: [4] **roadmap defect found and fixed**: the
  README asked for `Iw(𝔭^{t'}) ⊆ U ⊆ Iw(𝔭^t)`. Counterexample to the README's form: `U = Iw(𝔭^{t+1})`
  satisfies it (`t' = t + 1`), but for `α` a unit the claimed representative `x_α = η u_α` is not in
  `U η U`: for every `u' ∈ U` the lower-left entry of `η u_α u'⁻¹ η⁻¹` has valuation exactly
  `v(ϖ)^{t−1}`. And `U₁`-type subgroups contain no `Iw(𝔭^{t'})` at all. Correct hypothesis: `Iw₁₁(𝔭^t) ⊆ U` (plan.md decision 8). [3] `hunif` is
  necessary: it converts `v(y) < 1` into `v(y) ≤ v(ϖ)`, false for a non-uniformiser. `t ≥ 1` is
  necessary: at `t = 0` the double coset `GL₂(𝒪) η GL₂(𝒪)` has `q + 1` right cosets. [2] `u = 1`:
  `i` is the class of `0` ✓. [SRC] `3_EtaDecomposition.exists_etaRep_mem` (`p = 3`, `t = 2`),
  `23_QuaternionData.bijOn_vRepQ` (`F = ℚ`, `t = 1`). SURVIVED after the edit.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.2 (module docstring: §0.4.1, §0.4.2).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `3_EtaDecomposition.exists_etaRep_mem`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. Entries of `u' = η u x_α⁻¹` from `u' · x_α = diag(ϖ,1) · u` (no inverse formula):
  `u'₀₁ = ϖb`, `u'₁₁ = d`, `u'₀₀ = a − bαϖ^t`, `u'₁₀·ϖ = c − dαϖ^t`, by `change` (defeq entry evaluation) +
  `linear_combination`. With `x₀ = c(dϖ^t)⁻¹`: `v(u'₁₀)·v(ϖ) = v(ϖ)^t·v(x₀ − α)`, so `u' ∈ Iw ⟺
  v(x₀ − α) ≤ v(ϖ)`; cancellation `mul_le_mul_iff_left₀/right₀`. GENERALISED (noted, not a B2): the
  unused hypotheses `hϖ1 : v ϖ < 1` and `ht : 1 ≤ t` were REMOVED from
  `inv_mul_etaGL_mul_mem_iwahoriPrincipal` (the congruence only needs `v α ≤ 1`), and the theorem was
  moved before `existsUnique_etaRep`, which uses it.

### [T042] `etaRep_mem_doubleCoset`, `etaRep_injective`, `existsUnique_upperRep` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T041] · **Type**: proof · **Leaves**: L11.11, L11.12, L11.13

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem etaRep_mem_doubleCoset {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U) (r : ι → K)
    (hr : ∀ i, Valued.v (r i) ≤ 1) (i : ι) :
    etaRep ϖ hϖ t (r i) ∈ ({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) * (U : Set (GL (Fin 2) K)) := by
  sorry
theorem etaRep_injective {ϖ : K} (hϖ : ϖ ≠ 0) (t : ℕ) (r : ι → K)
    (hr : Function.Injective r) : Function.Injective fun i ↦ etaRep ϖ hϖ t (r i) := by
  sorry
theorem existsUnique_upperRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) {u : GL (Fin 2) K}
    (hu : u ∈ U) : ∃! i, (upperRep ϖ hϖ (r i))⁻¹ * u * etaGL ϖ hϖ ∈ U := by
  sorry
theorem bijOn_etaRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K) (hr1 : ∀ i, Valued.v (r i) ≤ 1)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) :
    Set.BijOn (Quotient.mk'' : GL (Fin 2) K → Quotient (QuotientGroup.rightRel U))
      (Set.range fun i ↦ etaRep ϖ hϖ t (r i))
      ((Quotient.mk'' : GL (Fin 2) K → Quotient (QuotientGroup.rightRel U)) ''
        (({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) * (U : Set (GL (Fin 2) K)))) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.11** `etaRep_mem_doubleCoset`, `etaRep_injective` — `x_α = η u_α ∈ η U` by L11.8 and
  `hlow`; injectivity from `ϖ ≠ 0` and `Function.Injective r`. SURVIVED.

- **L11.12** `existsUnique_upperRep` — [RM] §0.4.2 "and correspondingly
  `= ∐_β ((ϖ β), (0 1)) U_𝔭` as left cosets". Substrate, last computation; the unique `β` is
  integral automatically (`v(b/d − β) < 1`, `v(b/d) ≤ 1`). Attacks: [1] the same hypothesis on `U`
  suffices: the diagonal of the correction is `(a − βc, d) ≡ (a, d)` ✓. SURVIVED.

- **L11.13** `bijOn_etaRep` — the form consumed by a Hecke operator ([SRC]
  `3_EtaDecomposition.bijOn_etaRep`). Lean: the classes of the `x_{r i}` are exactly the right
  cosets in `η U`, injectively on the range. Attacks: [1] **succeeded**: without `∀ i, v (r i) ≤ 1`
  the statement is false. Take `ι = Option (𝒪/ϖ)`, `r none = ϖ⁻¹`: `hr` still holds (`none` is never
  the unique residue, since `v(x − ϖ⁻¹) > 1`), but `x_{ϖ⁻¹} ∉ η U`, so `MapsTo` fails. Hypothesis
  `hr1` added, here and in L14.9 (plan.md decision 10). With `hr1`, `InjOn` follows from the
  uniqueness in `hr` at `x = r i`. SURVIVED after the edit.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.2 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.
- [SRC] (proof idea only, never imported): `3_EtaDecomposition.bijOn_etaRep`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. `bijOn_etaRep`: MapsTo by `etaRep_mem_doubleCoset`; InjOn from the uniqueness
  in `existsUnique_etaRep` at `u = lowerUnip(r i ϖ^t)` (`x_{r i} x_{r j}⁻¹ ∈ U`); SurjOn from existence.
  `existsUnique_upperRep` by the same scheme with `R · W = u · diag(ϖ,1)`, `y₀ = b d⁻¹`.

### [CLEANUP-17] `/cleanup` of `Level/Local.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T042] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-18.

### [T043] `valued_det_of_mem_doubleCoset`, `mem_monoidM_iff_norm`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [CLEANUP-17] · **Type**: proof · **Leaves**: L11.14, L11.15

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem valued_det_of_mem_doubleCoset {ϖ : K} (hϖ : ϖ ≠ 0) {γ : Γ₀}
    {U : Subgroup (GL (Fin 2) K)} (hup : U ≤ iwahori K γ) {x : GL (Fin 2) K}
    (hx : x ∈ (U : Set (GL (Fin 2) K)) * ({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) *
      (U : Set (GL (Fin 2) K))) :
    Valued.v (x : Matrix (Fin 2) (Fin 2) K).det = Valued.v ϖ := by
  sorry
theorem mem_monoidM_iff_norm {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : Matrix (Fin 2) (Fin 2) K} :
    letI := Valued.toNormedField K Γ₀
    g ∈ monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ‖ϖ‖ ^ t ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L11.14** `valued_det_of_mem_doubleCoset` — [RM] §0.4.3 "every `x` in `U η_𝔭 U` has
  `‖det θ_𝔭(x)‖ = ‖ϖ‖`", local form: `det (u η u') = det u · ϖ · det u'`. Attacks: [3] any `γ`
  works, only `U ≤ Iw(γ)` is used ✓. SURVIVED.

- **L11.15** `mem_monoidM_iff_norm` — [RM] §0.4.1 "state the dictionary with the norm form
  `‖c‖ ≤ ‖ϖ‖^t`, `‖d‖ = 1` (Layer 1's `SigmaNorm`)". Lean: under `[(Valued.v).RankOne]` and
  `letI := Valued.toNormedField K Γ₀`. Sketch: the norm is a strictly monotone function of the
  valuation (`Valued.toNormedField.norm_le_iff`, `norm_le_one_iff`). SURVIVED.

#### Mathlib lemmas needed

`Valued.toNormedField.norm_le_iff`, `norm_le_one_iff`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.1, §0.4.3 (module docstring: §0.4.1, §0.4.2).
- Literature: the quotations of the module docstring of `Level/Local.lean`.

#### Generality decision

Binding decisions of `plan.md`: (7) **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`** (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. `mem_monoidM_iff_norm`: the statement's `letI` is already inlined, so the proof
  re-introduces `letI := Valued.toNormedField K Γ₀` (else `norm_pow` finds no `NormedDivisionRing`).

### [CLEANUP-18] `/cleanup` of `Level/Local.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Local.lean` · **Depends on**: [T043] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, axioms standard, `runLinter` passes, no build warnings,
  lines ≤ 100; module docstring lists every main declaration; docstrings added to `monoidM_mono`,
  `isOpen_iwahoriOne/Principal`, `det_etaRep`, `lowerUnip_mem_iwahoriPrincipal`, `etaRep_injective`.

### [T044] `levelThreshold`, `levelThreshold_lt_one`, `levelThreshold_ne_zero` and 6 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Standard.lean` · **Depends on**: [T031], [T043] · **Type**: proof · **Leaves**: L12.1, L12.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def levelThreshold (t : ℕ) : ℤᵐ⁰ := WithZero.exp (-(t : ℤ))
theorem levelThreshold_lt_one {t : ℕ} (ht : 1 ≤ t) : levelThreshold t < 1 := by
  sorry
theorem levelThreshold_ne_zero (t : ℕ) : levelThreshold t ≠ 0 := by
  sorry
theorem valued_pow_eq_levelThreshold (v : HeightOneSpectrum (𝓞 F)) {ϖ : v.adicCompletion F}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (t : ℕ) : Valued.v ϖ ^ t = levelThreshold t := by
  sorry
def levelAt (H : Subgroup (GL (Fin 2) (v.adicCompletion F))) : Subgroup (Dfx F D) :=
  H.comap (toGL F D v)
theorem mem_levelAt_iff {H : Subgroup (GL (Fin 2) (v.adicCompletion F))} {g : Dfx F D} :
    g ∈ levelAt F D v H ↔ toGL F D v g ∈ H :=
  Iff.rfl
theorem isOpen_levelAt {H : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    (hH : IsOpen (H : Set (GL (Fin 2) (v.adicCompletion F)))) :
    IsOpen (levelAt F D v H : Set (Dfx F D)) := by
  sorry
theorem unitAt_mem_levelAt_iff {H : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    {m : GL (Fin 2) (v.adicCompletion F)} : unitAt F D v m ∈ levelAt F D v H ↔ m ∈ H := by
  sorry
theorem unitAt_mem_levelAt_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w]
    (hw : w ≠ v) (H : Subgroup (GL (Fin 2) (v.adicCompletion F)))
    (m : GL (Fin 2) (w.adicCompletion F)) : unitAt F D w m ∈ levelAt F D v H := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L12.1** `levelThreshold`, `levelThreshold_lt_one`, `levelThreshold_ne_zero`,
  `valued_pow_eq_levelThreshold` — the value `v(ϖ)^t = exp(−t) ∈ ℤᵐ⁰`. `WithZero.exp_lt_exp`.
  SURVIVED.

- **L12.2** `levelAt`, `mem_levelAt_iff`, `isOpen_levelAt`, `unitAt_mem_levelAt_iff`,
  `unitAt_mem_levelAt_of_ne` — `H.comap (toGL F D v)`; open by L8.5. SURVIVED.

#### Mathlib lemmas needed

`WithZero.exp_lt_exp`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.3.1).
- Literature: the quotations of the module docstring of `Level/Standard.lean`.

#### Generality decision

Binding decisions of `plan.md`: (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-29: DONE (all of Level/Standard.lean T044–T046 in one pass). `levelThreshold` via
  `WithZero.exp_lt_exp`/`exp_le_exp`/`exp_nsmul`; the B2-repaired `isOpen_iwahori` hypothesis is
  discharged by `v.valuation_exists_uniformizer F` (private `exists_ne_zero_valued_le_levelThreshold`).

### [T045] `standardLevel`, `U0Level`, `U1Level` and 10 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Standard.lean` · **Depends on**: [T044] · **Type**: proof · **Leaves**: L12.3, L12.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def standardLevel (H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))) :
    Subgroup (Dfx F D) :=
  U0 b hb ⊓ ⨅ k, levelAt F D (w k) (H k)
def U0Level (t : κ → ℕ) : Subgroup (Dfx F D) :=
  standardLevel b hb w fun k ↦ iwahori ((w k).adicCompletion F) (levelThreshold (t k))
def U1Level (t : κ → ℕ) : Subgroup (Dfx F D) :=
  standardLevel b hb w fun k ↦ iwahoriOne ((w k).adicCompletion F) (levelThreshold (t k))
theorem standardLevel_le_U0 (H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))) :
    standardLevel b hb w H ≤ U0 b hb := by
  sorry
theorem isOpen_standardLevel
    {H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))}
    (hH : ∀ k, IsOpen (H k : Set (GL (Fin 2) ((w k).adicCompletion F)))) :
    IsOpen (standardLevel b hb w H : Set (Dfx F D)) := by
  sorry
theorem isCompact_standardLevel
    {H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))}
    (hH : ∀ k, IsOpen (H k : Set (GL (Fin 2) ((w k).adicCompletion F)))) :
    IsCompact (standardLevel b hb w H : Set (Dfx F D)) := by
  sorry
theorem U1Level_le_U0Level (t : κ → ℕ) : U1Level b hb w t ≤ U0Level b hb w t := by
  sorry
theorem U0Level_anti {t t' : κ → ℕ} (h : t ≤ t') : U0Level b hb w t' ≤ U0Level b hb w t := by
  sorry
theorem U1Level_normal (t : κ → ℕ) :
    ((U1Level b hb w t).subgroupOf (U0Level b hb w t)).Normal := by
  sorry
theorem isOpen_U0Level (t : κ → ℕ) :
    IsOpen (U0Level b hb w t : Set (Dfx F D)) := by
  sorry
theorem isCompact_U0Level (t : κ → ℕ) :
    IsCompact (U0Level b hb w t : Set (Dfx F D)) := by
  sorry
theorem isOpen_U1Level (t : κ → ℕ) :
    IsOpen (U1Level b hb w t : Set (Dfx F D)) := by
  sorry
theorem isCompact_U1Level (t : κ → ℕ) :
    IsCompact (U1Level b hb w t : Set (Dfx F D)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L12.3** `standardLevel`, `U0Level`, `U1Level`, `standardLevel_le_U0`, `isOpen_standardLevel`,
  `isCompact_standardLevel`, and the four corollaries — [RM] §0.3.1 "define `U₀(𝔫)`,
  `U₁(𝔫) ⊆ U₀(1)` […] prove they are compact open"; [Buz07, p. 69] (quoted). Sketch: a finite
  intersection of open subgroups is open (`κ` finite); an open subgroup is closed
  (`Subgroup.isClosed_of_isOpen`), and a closed subset of the compact `U₀(1)` is compact. Attacks:
  [3] `Finite κ` is used for openness only ✓. [4] `𝔫` is rendered as the family `(w k, t k)`; places
  must be split (they carry rigidifications), which is the roadmap's "prime to the discriminant".
  SURVIVED.

- **L12.4** `U1Level_le_U0Level`, `U0Level_anti`, `U1Level_normal` — [RM] §0.3.1 "`U₁(𝔫) ⊴ U₀(𝔫)`";
  "`U₀(𝔫) ∩ U₀(𝔭^t)` and `U₁(𝔫) ∩ U₀(𝔭^t)` are the levels of Buzzard's §§12–13" (these are
  `standardLevel` for a mixed family `H`). L11.3 componentwise. SURVIVED.

#### Mathlib lemmas needed

`Subgroup.isClosed_of_isOpen`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.1 (module docstring: §0.3.1).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-29: DONE. `isOpen_standardLevel` by `Subgroup.coe_inf`/`coe_iInf`; compactness as a closed
  subgroup of `U₀(1)` (needs `Module.Finite.of_basis b` for the topological-group instances).

### [T046] `lowerRightResidueLevel`, `iInf_ker_lowerRightResidueLevel`, `lowerRightResidueLevel_surjective`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Standard.lean` · **Depends on**: [T045] · **Type**: proof · **Leaves**: L12.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def lowerRightResidueLevel (t : κ → ℕ) (k : κ) :
    U0Level b hb w t →*
      ((Valued.v : Valuation ((w k).adicCompletion F) ℤᵐ⁰).integer ⧸
        ballIdeal ((w k).adicCompletion F) (levelThreshold (t k)))ˣ :=
  (lowerRightResidue ((w k).adicCompletion F) (levelThreshold (t k))).comp
    { toFun := fun g ↦ ⟨toGL F D (w k) (g : Dfx F D), by sorry⟩
      map_one' := by sorry
      map_mul' := by sorry }
theorem iInf_ker_lowerRightResidueLevel (t : κ → ℕ) :
    ⨅ k, (lowerRightResidueLevel b hb w t k).ker =
      (U1Level b hb w t).subgroupOf (U0Level b hb w t) := by
  sorry
theorem lowerRightResidueLevel_surjective (hw : Function.Injective w)
    (hint : ∀ k, RigidificationAt.IsIntegral b hb (w k)) {t : κ → ℕ} (ht : ∀ k, 1 ≤ t k) :
    Function.Surjective fun (g : U0Level b hb w t) (k : κ) ↦
      lowerRightResidueLevel b hb w t k g := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L12.5** `lowerRightResidueLevel` (fields), `iInf_ker_lowerRightResidueLevel`,
  `lowerRightResidueLevel_surjective` — the quotient `U₀(𝔫)/U₁(𝔫)`. Surjectivity: lift each residue
  to a unit `d_k` (L11.4), take the product of the commuting elements `ι_{w k}(diag(1, d_k))`
  (`Finset.noncommProd`, L8.8), which lies in `U₀(1)` by integrality (L9.8). Attacks: [3] `w`
  injective is necessary: with `w 1 = w 2` and different exponents the two residues at one place are
  linked. `1 ≤ t k` is used by L11.4. SURVIVED.

#### Mathlib lemmas needed

`Finset.noncommProd`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.3.1).
- Literature: the quotations of the module docstring of `Level/Standard.lean`.

#### Generality decision

Binding decisions of `plan.md`: (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-29: DONE. Joint surjectivity by `Finset.induction_on` (no `noncommProd`): insert
  `ι_{w k}(m_k)` on the left; components at other places stay `1` (`toLocalUnits_localIncl_of_ne`,
  `w` injective); private `toGL_eq_one_of_toLocalUnits_eq_one`. Kernel: `ker_lowerRightResidue` through
  `SetLike.ext_iff`.

### [CLEANUP-19] `/cleanup` of `Level/Standard.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/Standard.lean` · **Depends on**: [T046] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, axioms standard, `runLinter` passes, no warnings; unused
  `[Fintype ι]`/`[Finite κ]` omitted on 6 statements (`omit … in` before the docstring); docstrings and
  module docstring completed.

### [T047] `relIndex_ne_zero_of_isCompact_of_isOpen`, `commensurable_of_isCompact_of_isOpen`, `classSet` and 3 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T031], [T006] · **Type**: proof · **Leaves**: L13.1, L13.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen {U V : Subgroup G}
    (hU : IsCompact (U : Set G)) (hV : IsOpen (V : Set G)) : V.relIndex U ≠ 0 := by
  sorry
theorem Subgroup.commensurable_of_isCompact_of_isOpen {U V : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) (hVc : IsCompact (V : Set G))
    (hVo : IsOpen (V : Set G)) : Subgroup.Commensurable U V := by
  sorry
abbrev classSet (U : Subgroup (Dfx F D)) : Type _ :=
  DoubleCoset.Quotient ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D)) (U : Set (Dfx F D))
class HasFiniteClassSets : Prop where
  finite_classSet : ∀ U : Subgroup (Dfx F D), IsOpen (U : Set (Dfx F D)) → Finite (classSet F D U)
theorem finite_classSet [HasFiniteClassSets F D] {U : Subgroup (Dfx F D)}
    (hU : IsOpen (U : Set (Dfx F D))) : Finite (classSet F D U) :=
  HasFiniteClassSets.finite_classSet U hU
theorem classSet_mk_eq_iff {U : Subgroup (Dfx F D)} {g g' : Dfx F D} :
    (DoubleCoset.mk _ _ g : classSet F D U) = DoubleCoset.mk _ _ g' ↔
      ∃ d ∈ globalUnits F D, ∃ u ∈ U, g' = d * g * u := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L13.1** `Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen`,
  `Subgroup.commensurable_of_isCompact_of_isOpen` — [RM] §0.3.1 "Every compact open subgroup of
  `D_f^×` is commensurable with `U₀(1)`". Substrate, last paragraph. Attacks: [3] only `U` compact
  and `V` open are used for `V.relIndex U ≠ 0` ✓ (stated that way). SURVIVED.

- **L13.2** `classSet`, `HasFiniteClassSets`, `finite_classSet`, `classSet_mk_eq_iff` — [RM] §0.3.3
  "Define `classSet U := D^× \ D_f^× / U` (Mathlib's `DoubleCoset.Quotient`)"; §0.3.2 Fujisaki's
  lemma; [Loe11, Proposition 3.1.1] (quoted). Lean: the class is a `Prop`-valued class whose one
  field is the conclusion. `classSet_mk_eq_iff` is `DoubleCoset.eq`. Attacks: [4] **this is the
  API gap of the layer** (plan.md decision 2): the theorem is FLT's; here it is a hypothesis, with
  an instance for `ℍ[ℚ]` (L18.6). [1] is the class inhabited for a non-division `D`? For
  `D = M₂(F)` the class sets of `GL₂` are also finite, so the class is not vacuous there; nothing
  here assumes division. SURVIVED.

#### Mathlib lemmas needed

`DoubleCoset.Quotient`, `DoubleCoset.eq`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.1, §0.3.2, §0.3.3 (module docstring: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3).
- Literature: [Loe11]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-29: DONE (all of Level/ClassSet.lean T047–T051 in one pass; 3 fix rounds).
  `relIndex_ne_zero_of_isCompact_of_isOpen`: `isCompact_iff_compactSpace` + `Subgroup.quotient_finite_of_isOpen`
  + `Subgroup.index_ne_zero_iff_finite`; `classSet_mk_eq_iff := DoubleCoset.eq _ _ g g'`.

### [T048] `finite_classSet_of_le`, `finite_classSet_of_relIndex_ne_zero`, `hasFiniteClassSets_of_finite` and 4 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T047] · **Type**: proof · **Leaves**: L13.3, L13.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem finite_classSet_of_le {U U' : Subgroup (Dfx F D)} (hle : U ≤ U')
    [Finite (classSet F D U)] : Finite (classSet F D U') := by
  sorry
theorem finite_classSet_of_relIndex_ne_zero {U U' : Subgroup (Dfx F D)} (hle : U ≤ U')
    (hfi : U.relIndex U' ≠ 0) [Finite (classSet F D U')] : Finite (classSet F D U) := by
  sorry
theorem hasFiniteClassSets_of_finite [Module.Finite F D] {U₀ : Subgroup (Dfx F D)}
    (hc : IsCompact (U₀ : Set (Dfx F D))) (ho : IsOpen (U₀ : Set (Dfx F D)))
    [Finite (classSet F D U₀)] : HasFiniteClassSets F D := by
  sorry
def IsCompleteFamily (c : ι → Dfx F D) (U : Subgroup (Dfx F D)) : Prop :=
  ∀ g : Dfx F D, ∃ i, ∃ d ∈ globalUnits F D, ∃ u ∈ U, g = d * c i * u
def IsSection (c : ι → Dfx F D) (U : Subgroup (Dfx F D)) : Prop :=
  Function.Bijective fun i ↦ (DoubleCoset.mk _ _ (c i) : classSet F D U)
theorem isSection_iff {c : ι → Dfx F D} {U : Subgroup (Dfx F D)} :
    IsSection c U ↔ IsCompleteFamily c U ∧
      ∀ i j, (∃ d ∈ globalUnits F D, ∃ u ∈ U, c j = d * c i * u) → i = j := by
  sorry
theorem exists_isSection (U : Subgroup (Dfx F D)) :
    ∃ c : classSet F D U → Dfx F D, IsSection c U := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L13.3** `finite_classSet_of_le`, `finite_classSet_of_relIndex_ne_zero`,
  `hasFiniteClassSets_of_finite` — finiteness at one compact open level gives it everywhere.
  Sketch: `U ≤ U'` gives a surjection of class sets; if `[U' : U] < ∞` the fibres of
  `classSet U → classSet U'` are images of `U'/U`; for an open `U`, `U ∩ U₀` has finite index in the
  compact `U₀` (L13.1). Attacks: [1] is the fibre bound right for a *double* quotient? The fibre
  over `D^× g U'` is `{D^× g u' U : u' ∈ U'}`, a quotient of `U'/U` ✓. SURVIVED.

- **L13.4** `IsCompleteFamily`, `IsSection`, `isSection_iff`, `exists_isSection` — [RM] §0.3.3 "a
  *section* is a family `c : ι → D_f^×` bijective onto `classSet U`, and a *complete family* one
  that meets every double coset". SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.3 (module docstring: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3).
- Literature: the quotations of the module docstring of `Level/ClassSet.lean`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-29: DONE. `finite_classSet_of_le` by `Quotient.map' id` + `DoubleCoset.rel_iff`.
  GENERALISED (noted, not a B2): the unused `hle : U ≤ U'` was REMOVED from
  `finite_classSet_of_relIndex_ne_zero` — the surjection `classSet U' × U' ⧸ (U ∩ U') → classSet U`,
  `(q, c) ↦ [q.out · c.out]`, needs no inclusion; the one caller updated. Traps: `QuotientGroup.eq.mp` given
  an expected type unified with the quotient of the ambient group → state it without expected type, then
  `Subgroup.mem_subgroupOf` + `simpa`; `finite_classSet_of_le inf_le_left` left `Finite (classSet (U ⊓ ?m))`
  stuck → `(U := U ⊓ U₀)`.

### [T049] `stabilizer`, `mem_stabilizer_iff`, `stabilizer_le` and 5 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T048] · **Type**: proof · **Leaves**: L13.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def stabilizer (c : Dfx F D) (U : Subgroup (Dfx F D)) : Subgroup (Dfx F D) where
  carrier := {u | u ∈ U ∧ c * u * c⁻¹ ∈ globalUnits F D}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
theorem mem_stabilizer_iff {c u : Dfx F D} {U : Subgroup (Dfx F D)} :
    u ∈ stabilizer c U ↔ u ∈ U ∧ c * u * c⁻¹ ∈ globalUnits F D :=
  Iff.rfl
theorem stabilizer_le (c : Dfx F D) (U : Subgroup (Dfx F D)) : stabilizer c U ≤ U := by
  sorry
def globalStabilizer (c : Dfx F D) (U : Subgroup (Dfx F D)) : Subgroup Dˣ :=
  U.comap ((MulAut.conj c⁻¹).toMonoidHom.comp (unitsIncl F D))
theorem mem_globalStabilizer_iff {c : Dfx F D} {U : Subgroup (Dfx F D)} {x : Dˣ} :
    x ∈ globalStabilizer c U ↔ c⁻¹ * unitsIncl F D x * c ∈ U := by
  sorry
def stabilizerEquiv (c : Dfx F D) (U : Subgroup (Dfx F D)) :
    stabilizer c U ≃* globalStabilizer c U := by
  sorry
theorem unitsIncl_algebraMap_mem_stabilizer (c : Dfx F D) {U : Subgroup (Dfx F D)} {z : Fˣ}
    (hz : unitsIncl F D (Units.map (algebraMap F D).toMonoidHom z) ∈ U) :
    unitsIncl F D (Units.map (algebraMap F D).toMonoidHom z) ∈ stabilizer c U := by
  sorry
theorem stabilizer_mul (c : Dfx F D) (U : Subgroup (Dfx F D)) {d u : Dfx F D}
    (hd : d ∈ globalUnits F D) (hu : u ∈ U) :
    stabilizer (d * c * u) U = (stabilizer c U).map (MulAut.conj u⁻¹).toMonoidHom := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L13.5** `stabilizer` (fields), `mem_stabilizer_iff`, `stabilizer_le`, `globalStabilizer`,
  `mem_globalStabilizer_iff`, `stabilizerEquiv`, `unitsIncl_algebraMap_mem_stabilizer`,
  `stabilizer_mul` — [RM] §0.3.3 "`Γ_λ := c_λ^{−1} D^× c_λ ∩ U` […] a subgroup of `U` isomorphic to
  `D^× ∩ c_λ U c_λ^{−1}` […] it contains `𝒪_F^× ∩ U`"; [Buz07, p. 68] (quoted). `stabilizer_mul`:
  changing the representative within its class conjugates the stabiliser by an element of `U`.
  Attacks: [1] is `stabilizer` = `c⁻¹ D^× c ∩ U`? `u ∈ c⁻¹D^×c ⟺ c u c⁻¹ ∈ D^×` ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.3 (module docstring: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-29: DONE. `stabilizer` fields and `stabilizer_mul` by explicit `group` identities;
  `stabilizerEquiv := (MulEquiv.ofBijective φ ⟨inj, surj⟩).symm`, `φ x = c⁻¹ ι(x) c`. Trap: in a structure
  instance `{ toFun … ⏎ map_one' := … }`, a field line indented DEEPER than the first field is parsed as an
  application argument (`expected '}'` at `:=`) → align the fields with `toFun`.

### [CLEANUP-20] `/cleanup` of `Level/ClassSet.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T049] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-21 (whole file written and cleaned in one pass).

### [T050] `finite_units_orderOf`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [CLEANUP-20] · **Type**: proof · **Leaves**: L13.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem finite_units_orderOf (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) : Finite (orderOf β hβ)ˣ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L13.6** `finite_units_orderOf` — [RM] §0.2.1 "`D^× ∩ U₀(1)` is the finite unit group of a
  definite order". Lean: `F = ℚ`, `(a, b)` totally definite, `β` an order basis. Sketch: a unit `u`
  has `nrd u, nrd u⁻¹ ∈ ℤ` (L2.4: `orderOf` is a finitely generated subring) and positive (L2.1),
  so `nrd u = 1`; the standard coordinates of `u` are then bounded (`re² ≤ 1`, `|a| imI² ≤ 1`, …)
  and lie in `(1/N)ℤ` for a common denominator `N` of the basis, a finite set. Attacks: [3]
  definiteness is necessary (`M₂(ℤ)^×` is infinite) ✓. [4] no [SRC]: new; the Hurwitz case is L4.4.
  SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1 (module docstring: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3).
- Literature: the quotations of the module docstring of `Level/ClassSet.lean`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-29: DONE. Units have `nrd = 1` (`exists_int_nrd_of_fg`, `Int.eq_one_of_mul_eq_one_right`);
  `nrd x = 1` bounds each quaternion coordinate (`x₀² + (−a)x₁² + (−b)x₂² + ab·x₃² = 1`), hence each
  `β`-coordinate; the integer coordinates lie in a box (`Set.finite_Icc` on `ι → ℤ`). Traps: `exact_mod_cast`
  does not see through `Rat.castHom ℝ a` → `simpa`; `AddSubgroup.subset_closure ⟨i, rfl⟩` has no determined
  expected type → `Set.mem_range_self (f := β) i`; `congrArg Subtype.val huv` was elaborated against the
  `Units` coercion → `(congrArg Subtype.val huv :)`.

### [T051] `discreteTopology_globalUnits`, `finite_stabilizer`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T050] · **Type**: proof · **Leaves**: L13.7, L13.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem discreteTopology_globalUnits (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) : DiscreteTopology (globalUnits ℚ ℍ[ℚ,a,b]) := by
  sorry
theorem finite_stabilizer (h : IsTotallyDefinite a b) {β : Module.Basis ι ℚ ℍ[ℚ,a,b]}
    (hβ : IsOrderBasis β) (c : Dfx ℚ ℍ[ℚ,a,b]) {U : Subgroup (Dfx ℚ ℍ[ℚ,a,b])}
    (hU : IsCompact (U : Set (Dfx ℚ ℍ[ℚ,a,b]))) : Finite (stabilizer c U) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L13.7** `discreteTopology_globalUnits` — [RM] §0.2.1 "Its image `Γ := D^×` is discrete when
  `F = ℚ` and `D` is definite"; [Loe11, Proposition 3.1.2] (quoted). Sketch: `D^× ∩ U₀(1)` is the
  image of `𝒪_D^×` (L9.6), finite (L13.6); in a T1 group a subgroup meeting an open neighbourhood of
  `1` in a finite set is discrete. Attacks: [4] the roadmap's warning is respected: nothing is
  claimed for a general totally real `F`. SURVIVED.

- **L13.8** `finite_stabilizer` — [RM] §0.3.3 "which is discrete (§0.2.1) and compact, hence
  **finite**, when `D` is totally definite and `F = ℚ`". Sketch: `globalStabilizer c U` injects into
  `D^× ∩ c U c⁻¹`, a discrete closed subgroup (`Subgroup.isClosed_of_discrete`) inside a compact
  set. Attacks: [3] only compactness of `U` is used, not openness ✓. SURVIVED.

#### Mathlib lemmas needed

`Subgroup.isClosed_of_discrete`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.2.1, §0.3.3 (module docstring: §0.2.1 (discreteness), §0.3.1 (commensurability), §0.3.2, §0.3.3).
- Literature: [Loe11]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-29: DONE. `W = D^× ∩ U₀(1)` is open and finite (units of the order), so
  `{1} = W \ (W \ {1})` is open; `discreteTopology_of_isOpen_singleton_one`. `finite_stabilizer`:
  `Subgroup.isClosed_of_discrete`, `IsClosed.isClosedEmbedding_subtypeVal`, `IsCompact.finite_of_discrete`.
  Renames met: `Set.diff_diff_cancel_left` → `Set.sdiff_sdiff_cancel_left` (still in `Set`),
  `Set.diff_subset` → `Set.sdiff_subset`.

### [CLEANUP-21] `/cleanup` of `Level/ClassSet.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/ClassSet.lean` · **Depends on**: [T051] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, `#print axioms` standard on 13 declarations, `runLinter`
  passes, no build warnings, lines ≤ 100; module docstring lists every main declaration; docstrings added to
  `finite_classSet`, `isSection_iff`, `mem_stabilizer_iff`, `stabilizer_le`, `mem_globalStabilizer_iff`; the
  one opaque `nlinarith` replaced by `mul_le_mul_of_nonneg_left` + `abs_mul_abs_self` + `linarith`.

### [T052] `isCompact_doubleCoset`, `isOpen_doubleCoset`, `finite_rightCosets_doubleCoset` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T046], [T051] · **Type**: proof · **Leaves**: L14.1, L14.2, L14.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem Subgroup.isCompact_doubleCoset {U : Subgroup G} (hU : IsCompact (U : Set G)) (η : G) :
    IsCompact ((U : Set G) * {η} * (U : Set G)) := by
  sorry
theorem Subgroup.isOpen_doubleCoset {U : Subgroup G} (hU : IsOpen (U : Set G)) (η : G) :
    IsOpen ((U : Set G) * {η} * (U : Set G)) := by
  sorry
theorem Subgroup.finite_rightCosets_doubleCoset {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (η : G) :
    ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel U)) ''
      (({η} : Set G) * (U : Set G))).Finite := by
  sorry
theorem Subgroup.finite_leftCosets_doubleCoset {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (η : G) :
    ((QuotientGroup.mk : G → G ⧸ U) '' ((U : Set G) * ({η} : Set G))).Finite := by
  sorry
theorem Subgroup.ncard_rightCosets_doubleCoset (U : Subgroup G) (η : G) :
    ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel U)) ''
      (({η} : Set G) * (U : Set G))).ncard = (MulAut.conj η⁻¹ • U).relIndex U := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.1** `Subgroup.isCompact_doubleCoset`, `Subgroup.isOpen_doubleCoset` — [RM] §0.3.4 "the
  double coset `U η U` is compact and open". Image of `U × U` under `(u, u') ↦ u η u'`; a union of
  translates of `U`. SURVIVED.

- **L14.2** `Subgroup.finite_rightCosets_doubleCoset`, `Subgroup.finite_leftCosets_doubleCoset` —
  [RM] §0.3.4 "hence a finite union of right cosets `U x_t` and of left cosets `x_t' U`";
  [Buz07, p. 69] (quoted). Substrate. [SRC] `2_LevelTopology.finite_image_doubleCoset_U1_9`
  (the special case). SURVIVED.

- **L14.3** `Subgroup.ncard_rightCosets_doubleCoset` — the number of right cosets is
  `[U : U ∩ η⁻¹ U η]`. Pure group theory: `U η u = U η u' ⟺ u u'⁻¹ ∈ η⁻¹ U η`. Attacks: [4]
  **roadmap defect found and fixed**: the README had `[U : U ∩ η U η⁻¹]`, which counts the *left*
  cosets `x U`. Check at `U = Iw(ϖ^t)`, `η = diag(ϖ, 1)`: `η⁻¹ u η = ((a, b/ϖ), (cϖ, d))`, index
  `q` (condition `ϖ ∣ b`); `η u η⁻¹ = ((a, bϖ), (c/ϖ, d))`, index `q` (condition `ϖ^{t+1} ∣ c`) —
  equal here, as in every unimodular group, but only the corrected index is what the elementary
  bijection gives (plan.md decision 9). [2] infinite case: `Set.ncard = 0 = relIndex` ✓, so no
  finiteness hypothesis is needed. SURVIVED after the edit.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.4 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `2_LevelTopology.finite_image_doubleCoset_U1_9`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE (all of Level/HeckePair.lean T052–T057 in one pass; 2 fix rounds).
  Compactness/openness by `IsCompact.mul`, `IsOpen.mul_left`. `ncard_rightCosets_doubleCoset` MOVED before
  the two finiteness theorems (they use it): `W u ↦ U η u` (`Quotient.map'`) is injective from
  `Quotient (rightRel W)`, `W = (η⁻¹ U η).subgroupOf U`, onto the right cosets in `U η U`
  (`Set.ncard_range_of_injective`, `quotientRightRelEquivQuotientLeftRel`); `x ∈ conj η⁻¹ • U ↔ η x η⁻¹ ∈ U` by
  `mem_pointwise_smul_iff_inv_smul_mem` + `← map_inv MulAut.conj` + `MulAut.smul_def`. Right-coset finiteness:
  `ncard ≠ 0` (`Set.finite_of_ncard_ne_zero`) from `relIndex_ne_zero_of_isCompact_of_isOpen`; left cosets by
  `QuotientGroup.discreteTopology` + `IsCompact.finite_of_discrete`. Group-theoretic lemmas carry
  `omit [TopologicalSpace G] [IsTopologicalGroup G] in`.

### [T053] `commensurator_eq_top_of_isCompact_of_isOpen`, `isHeckeTriple_of_isCompact_of_isOpen`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T052] · **Type**: proof · **Leaves**: L14.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem Subgroup.commensurator_eq_top_of_isCompact_of_isOpen {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    Subgroup.Commensurable.commensurator U = ⊤ := by
  sorry
theorem Subgroup.isHeckeTriple_of_isCompact_of_isOpen {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) {Δ : Submonoid G}
    (hle : U.toSubmonoid ≤ Δ) : IsHeckeTriple Δ U U := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.4** `Subgroup.commensurator_eq_top_of_isCompact_of_isOpen`,
  `Subgroup.isHeckeTriple_of_isCompact_of_isOpen` — [RM] §0.3.4 "for a submonoid `Δ ⊆ D_f^×`
  containing `U`, the pair `(Δ, U)` is a Hecke triple in the sense of Mathlib's `IsHeckeTriple`".
  L13.1 for the conjugates of `U`; `IsHeckeTriple.of_diagonal`. SURVIVED.

#### Mathlib lemmas needed

`IsHeckeTriple.of_diagonal`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.4 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: the quotations of the module docstring of `Level/HeckePair.lean`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. Conjugates of `U` are compact open (`Subgroup.coe_pointwise_smul`,
  `IsCompact.smul`, `IsOpen.smul` for the `ConjAct` action), hence commensurable with `U`;
  `IsHeckeTriple.of_diagonal`.

### [T054] `wildMonoid`, `mem_wildMonoid_iff`, `etaAdelic` and 10 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T053] · **Type**: proof · **Leaves**: L14.5, L14.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def wildMonoid (γ : ℤᵐ⁰) (hγ : γ < 1) : Submonoid (Dfx F D) :=
  (monoidM (v.adicCompletion F) γ hγ).comap (toMatrix F D v)
theorem mem_wildMonoid_iff {γ : ℤᵐ⁰} {hγ : γ < 1} {g : Dfx F D} :
    g ∈ wildMonoid F D v γ hγ ↔ toMatrix F D v g ∈ monoidM (v.adicCompletion F) γ hγ :=
  Iff.rfl
def etaAdelic (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) : Dfx F D :=
  unitAt F D v (etaGL ϖ hϖ)
def etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ) (α : v.adicCompletion F) :
    Dfx F D :=
  unitAt F D v (etaRep ϖ hϖ t α)
def diamond (d : (v.adicCompletion F)ˣ) : Dfx F D :=
  unitAt F D v (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, (d : _)])
    (by sorry))
theorem toMatrix_etaAdelic (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) :
    toMatrix F D v (etaAdelic F D v ϖ hϖ) = Matrix.diagonal ![ϖ, 1] := by
  sorry
theorem toMatrix_etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ)
    (α : v.adicCompletion F) :
    toMatrix F D v (etaAdelicRep F D v ϖ hϖ t α) = !![ϖ, 0; α * ϖ ^ t, 1] := by
  sorry
theorem det_toMatrix_etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ)
    (α : v.adicCompletion F) :
    (toMatrix F D v (etaAdelicRep F D v ϖ hϖ t α)).det = ϖ := by
  sorry
theorem etaAdelic_mem_wildMonoid {γ : ℤᵐ⁰} (hγ : γ < 1) {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ ≤ 1) : etaAdelic F D v ϖ hϖ ∈ wildMonoid F D v γ hγ := by
  sorry
theorem etaAdelic_mem_wildMonoid_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w]
    (hw : w ≠ v) {γ : ℤᵐ⁰} (hγ : γ < 1) (ϖ : w.adicCompletion F) (hϖ : ϖ ≠ 0) :
    etaAdelic F D w ϖ hϖ ∈ wildMonoid F D v γ hγ := by
  sorry
theorem unitAt_smul_one_mem_wildMonoid_iff {γ : ℤᵐ⁰} (hγ : γ < 1) (u : (v.adicCompletion F)ˣ) :
    unitAt F D v (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((u : v.adicCompletion F) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (by sorry)) ∈
        wildMonoid F D v γ hγ ↔ Valued.v (u : v.adicCompletion F) = 1 := by
  sorry
theorem diamond_commute_etaAdelic (d : (v.adicCompletion F)ˣ) (ϖ : v.adicCompletion F)
    (hϖ : ϖ ≠ 0) : Commute (diamond F D v d) (etaAdelic F D v ϖ hϖ) := by
  sorry
theorem diamond_mem_wildMonoid {γ : ℤᵐ⁰} (hγ : γ < 1) {d : (v.adicCompletion F)ˣ}
    (hd : Valued.v (d : v.adicCompletion F) = 1) : diamond F D v d ∈ wildMonoid F D v γ hγ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.5** `wildMonoid`, `mem_wildMonoid_iff`, `etaAdelic`, `etaAdelicRep`, `diamond` (field),
  `toMatrix_etaAdelic`, `toMatrix_etaAdelicRep`, `det_toMatrix_etaAdelicRep` — [RM] §0.4.3 "Define
  `η_𝔭 := ι_𝔭(η) ∈ D_f^×`, the unit with `𝔭`-component `diag(ϖ, 1)` and trivial components
  elsewhere (`etaAdelic`) […] with `θ_𝔭` of the representatives the matrices of clause 2 and
  `det θ_𝔭 = ϖ`". L8.9, L11.7. [SRC] `04_UpiElement.toMatrix_etaAdelic`. SURVIVED.

- **L14.6** `etaAdelic_mem_wildMonoid`, `etaAdelic_mem_wildMonoid_of_ne`,
  `unitAt_smul_one_mem_wildMonoid_iff`, `diamond_commute_etaAdelic`, `diamond_mem_wildMonoid` —
  [RM] §0.4.4 "`δ_d := ι_𝔭(diag(1, d))` normalises `U₁(𝔭^t)`-type levels and commutes with `η_𝔭`; the
  scalars `ι_𝔭(u · 1)` for `u ∈ 𝒪^×` lie in `Δ_t` […] `ι_𝔭(ϖ · 1)` does not lie in `Δ_t`". L11.5,
  L11.8. Attacks: [4] "normalises `U₁`-type levels" is L12.4 (`δ_d ∈ U₀(𝔫)` and `U₁ ⊴ U₀`), not
  restated. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.3, §0.4.4 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: the quotations of the module docstring of `Level/HeckePair.lean`.
- [SRC] (proof idea only, never imported): `04_UpiElement.toMatrix_etaAdelic`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. The two `(by sorry)` det obligations in statements discharged
  (`det_diagonal`, `Matrix.det_smul`). Everything through `← coe_toGL, toGL_unitAt` plus a private `rfl` lemma
  `coe_mkOfDetNeZero` (Mathlib has no coercion lemma for `mkOfDetNeZero`); `diamond_commute_etaAdelic` by
  `Commute.map (Units.ext _)` and `diagonal_mul_diagonal`; away from `v`: `toGL_unitAt_of_ne`.

### [CLEANUP-22] `/cleanup` of `Level/HeckePair.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T054] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-29: DONE, merged into CLEANUP-23 (whole file written and cleaned in one pass).

### [T055] `wildMonoidOf`, `HasWildLevel`, `etaAdelic_mem_wildMonoidOf` and 2 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [CLEANUP-22] · **Type**: proof · **Leaves**: L14.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def wildMonoidOf (γ : κ → ℤᵐ⁰) (hγ : ∀ k, γ k < 1) : Submonoid (Dfx F D) :=
  ⨅ k, wildMonoid F D (w k) (γ k) (hγ k)
def HasWildLevel (U : Subgroup (Dfx F D)) (γ : κ → ℤᵐ⁰) (hγ : ∀ k, γ k < 1) : Prop :=
  U.toSubmonoid ≤ wildMonoidOf F D w γ hγ
theorem etaAdelic_mem_wildMonoidOf (hw : Function.Injective w) {γ : κ → ℤᵐ⁰}
    (hγ : ∀ k, γ k < 1) (k : κ) {ϖ : (w k).adicCompletion F} (hϖ : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ ≤ 1) : etaAdelic F D (w k) ϖ hϖ ∈ wildMonoidOf F D w γ hγ := by
  sorry
theorem hasWildLevel_U0Level [Finite κ] {ι : Type*} [Fintype ι] {b : Module.Basis ι F D}
    {hb : IsOrderBasis b} {t : κ → ℕ} (ht : ∀ k, 1 ≤ t k) :
    HasWildLevel F D w (U0Level b hb w t) (fun k ↦ levelThreshold (t k))
      (fun k ↦ levelThreshold_lt_one (ht k)) := by
  sorry
theorem isHeckeTriple_wildMonoidOf [Module.Finite F D] {U : Subgroup (Dfx F D)}
    (hUc : IsCompact (U : Set (Dfx F D))) (hUo : IsOpen (U : Set (Dfx F D))) {γ : κ → ℤᵐ⁰}
    {hγ : ∀ k, γ k < 1} (hU : HasWildLevel F D w U γ hγ) :
    IsHeckeTriple (wildMonoidOf F D w γ hγ) U U := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.7** `wildMonoidOf`, `HasWildLevel`, `etaAdelic_mem_wildMonoidOf`, `hasWildLevel_U0Level`,
  `isHeckeTriple_wildMonoidOf` — [RM] §0.4.3 "for `t ∈ ℕ_{≥1}^𝔓` the monoid
  `Δ_t := θ_p^{−1}(∏_𝔭 M_{t_𝔭}) ⊆ D_f^×` (Buzzard's 'wild level'); a compact open `U` *has wild level
  `≥ 𝔭^t`* if `U ⊆ Δ_t` […] Prove that `η_𝔭 ∈ Δ_t` for every `t`"; §0.4.5 "`(Δ_t, U)` is a Hecke
  triple"; [Buz07, p. 68] (`buzzard.txt:2656`): "we say that a compact open subgroup `U ⊂ D_f^×` has
  wild level `≥ π^t` if the projection `U → D_p^×` is contained within `M_t`". Attacks: [3]
  `etaAdelic_mem_wildMonoidOf` needs `w` injective (at a repeated place with a different threshold
  nothing breaks, but the proof by cases `k' = k` / `w k' ≠ w k` needs it) ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.3, §0.4.5 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: [Buz07]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. `Submonoid.mem_iInf` + case split `k' = k` (uses `w` injective);
  `hasWildLevel_U0Level` by `coe_mem_monoidM` on the `w k`-component; `isHeckeTriple_wildMonoidOf` is
  T053 directly (`[Module.Finite F D]` is used: the topological-group instance on `D_f^×` needs it).

### [T056] `existsUnique_etaAdelicRep`, `bijOn_etaAdelicRep`, `unitAt_iwahoriPrincipal_le_U1Level`

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T055] · **Type**: proof · **Leaves**: L14.8, L14.9

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem existsUnique_etaAdelicRep {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : v.adicCompletion F, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ}
    (ht : 1 ≤ t) {U : Subgroup (Dfx F D)}
    (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) (Valued.v ϖ ^ t)))
    (hlow : (iwahoriPrincipal (v.adicCompletion F) (Valued.v ϖ ^ t)).map (unitAt F D v) ≤ U)
    (r : ι → v.adicCompletion F)
    (hr : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1)
    {u : Dfx F D} (hu : u ∈ U) :
    ∃! i, etaAdelic F D v ϖ hϖ * u * (etaAdelicRep F D v ϖ hϖ t (r i))⁻¹ ∈ U := by
  sorry
theorem bijOn_etaAdelicRep {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : v.adicCompletion F, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ}
    (ht : 1 ≤ t) {U : Subgroup (Dfx F D)}
    (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) (Valued.v ϖ ^ t)))
    (hlow : (iwahoriPrincipal (v.adicCompletion F) (Valued.v ϖ ^ t)).map (unitAt F D v) ≤ U)
    (r : ι → v.adicCompletion F) (hr1 : ∀ i, Valued.v (r i) ≤ 1)
    (hr : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) :
    Set.BijOn (Quotient.mk'' : Dfx F D → Quotient (QuotientGroup.rightRel U))
      (Set.range fun i ↦ etaAdelicRep F D v ϖ hϖ t (r i))
      ((Quotient.mk'' : Dfx F D → Quotient (QuotientGroup.rightRel U)) ''
        (({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) * (U : Set (Dfx F D)))) := by
  sorry
theorem unitAt_iwahoriPrincipal_le_U1Level {κ : Type*} [Finite κ]
    {w : κ → HeightOneSpectrum (𝓞 F)} [∀ k, RigidificationAt F D (w k)]
    (hw : Function.Injective w) {ι' : Type*} [Fintype ι'] {b : Module.Basis ι' F D}
    {hb : IsOrderBasis b} (hint : ∀ k, RigidificationAt.IsIntegral b hb (w k)) (t : κ → ℕ)
    (k : κ) :
    (iwahoriPrincipal ((w k).adicCompletion F) (levelThreshold (t k))).map
      (unitAt F D (w k)) ≤ U1Level b hb w t := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.8** `existsUnique_etaAdelicRep` — [RM] §0.4.3 "the decomposition
  `U η_𝔭 U = ∐_α U · ι_𝔭(x_α)` holds in `D_f^×`". Lean: hypotheses `θ_v(U) ⊆ Iw(γ)` and
  `ι_v(Iw₁₁(γ)) ⊆ U`. Sketch: for `u ∈ U` apply L11.10 to `θ_v(u)` with the local group `Iw(γ)`;
  then `η_v u ι_v(x_α)⁻¹ = u · ι_v(θ_v(u)⁻¹ · (η θ_v(u) x_α⁻¹))` — the two sides have the same
  components everywhere (L8.3, L8.7) — and the last factor is in `ι_v(Iw₁₁)` by L11.9. Uniqueness
  from the local uniqueness. Attacks: [4] the roadmap's "`U = U^{(p)} × ∏_𝔭 U_𝔭`" is replaced by the
  two hypotheses, which a product level satisfies and which are what the proof uses; [SRC]'s two
  instances (`U₁(9)`; `levelOf Kt`) both satisfy them. [1] is `ι_v(Iw₁₁) ⊆ U` really needed? For
  `U = U₀(1) ∩ θ_v⁻¹(Iw)` intersected with a condition at `v` that is *not* a diagonal-residue
  condition (e.g. `b ≡ 0 mod ϖ`), the decomposition fails, and `ι_v(Iw₁₁) ⊄ U` there ✓. SURVIVED.

- **L14.9** `bijOn_etaAdelicRep`, `unitAt_iwahoriPrincipal_le_U1Level` — the bijective form (with
  `hr1`, L11.13), and the standard levels satisfy the lower hypothesis at an integral place (L9.8,
  L12.2). SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.4.3 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: the quotations of the module docstring of `Level/HeckePair.lean`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. Private `unitAt_mul_eq`: `ι_v(g) u = u ι_v(θ_v(u)⁻¹ g θ_v(u))` (split
  `u = ι_v(θ_v u) u'` with `u'` of trivial `v`-component, which commutes with `ι_v(·)`). Existence: local
  `existsUnique_etaRep` with `U := Iw(γ)`, then `η_v u x_α⁻¹ = u · ι_v(m⁻¹ η m x_α⁻¹)` and
  `inv_mul_etaGL_mul_mem_iwahoriPrincipal`, whose `v(α) ≤ 1` comes from the NEW public
  `LocalLevel.valued_le_one_of_etaConj_mem` added to `Level/Local.lean` (with private `v_ratio_le_one`, also
  used by `existsUnique_etaRep`). Uniqueness: `θ_v` of the condition is the local one. Trap: `∃!` goals and
  set-membership destructuring leave beta-redexes `(fun i ↦ …) j`, `(fun x1 x2 ↦ x1 * x2) e u` → `beta_reduce`
  before `rw`.

### [T057] `valued_det_toMatrix_of_mem_doubleCoset`, `valued_det_toMatrix_of_mem_doubleCoset_of_ne`, `heckeElement` and 1 more

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T056] · **Type**: proof · **Leaves**: L14.10, L14.11

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem valued_det_toMatrix_of_mem_doubleCoset {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) {γ : ℤᵐ⁰}
    {U : Subgroup (Dfx F D)} (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) γ))
    {x : Dfx F D}
    (hx : x ∈ (U : Set (Dfx F D)) * ({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) *
      (U : Set (Dfx F D))) :
    Valued.v (toMatrix F D v x).det = Valued.v ϖ := by
  sorry
theorem valued_det_toMatrix_of_mem_doubleCoset_of_ne {w : HeightOneSpectrum (𝓞 F)}
    [RigidificationAt F D w] (hw : w ≠ v)
    {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) {U : Subgroup (Dfx F D)}
    (hU : IsCompact (U : Set (Dfx F D))) {x : Dfx F D}
    (hx : x ∈ (U : Set (Dfx F D)) * ({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) *
      (U : Set (Dfx F D))) :
    Valued.v (toMatrix F D w x).det = 1 := by
  sorry
def heckeElement (η : Dfx F D) (hη : η ∈ Δ) : HeckeRing Δ U ℤ :=
  HeckeCosetModule.of (Finsupp.single (HeckeCoset.mk U U ⟨η, hη⟩) 1)
theorem heckeElement_eq_of_mem_doubleCoset {η η' : Dfx F D} (hη : η ∈ Δ) (hη' : η' ∈ Δ)
    (h : η' ∈ (U : Set (Dfx F D)) * ({η} : Set (Dfx F D)) * (U : Set (Dfx F D))) :
    (heckeElement η' hη' : HeckeRing Δ U ℤ) = heckeElement η hη := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.3–§0.4 Levels, class sets and the Hecke pair", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L14.10** `valued_det_toMatrix_of_mem_doubleCoset`,
  `valued_det_toMatrix_of_mem_doubleCoset_of_ne` — [RM] §0.4.3 "every `x` in `U η_𝔭 U` has
  `‖det θ_𝔭(x)‖ = ‖ϖ‖` and `det θ_𝔮(x) ∈ 𝒪_𝔮^×` for `𝔮 ≠ 𝔭`". Second statement, for `U` compact:
  `g ↦ v(det θ_w g)` is a continuous homomorphism to the discrete value group, so its image on a
  compact subgroup is a finite subgroup of `ℤ`, trivial. Attacks: [1] is compactness needed? Yes:
  for `U = D_f^×` the statement is false ✓. [3] `Module.Finite` dropped (continuity of `toGL` needs
  none). SURVIVED.

- **L14.11** `heckeElement`, `heckeElement_eq_of_mem_doubleCoset` — [RM] §0.3.4 "every `η ∈ Δ`
  defines an element of `HeckeRing Δ U ℤ`"; §0.4.5 "`U η_𝔭 U`, `U η_𝔮 U`, `U ϖ_𝔮 U` and the diamond
  cosets are elements of `HeckeRing Δ_t U ℤ`". `HeckeCosetModule.of (Finsupp.single (HeckeCoset.mk
  U U ⟨η, hη⟩) 1)`; equality by `Quotient.sound`. Attacks: [4] no `IsHeckeTriple` instance is needed
  to *form* the element; it is needed for the ring structure, which Layer 3 uses ✓. SURVIVED.

#### Mathlib lemmas needed

`Module.Finite`, `Quotient.sound`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.4, §0.4.3, §0.4.5 (module docstring: §0.3.4, §0.4.3, §0.4.4, §0.4.5).
- Literature: the quotations of the module docstring of `Level/HeckePair.lean`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (9) **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-29: DONE. Private `valued_det_toMatrix_eq_one_of_isCompact`: some power `u^n`, `n > 0`,
  lies in the open subgroup `θ_w⁻¹ GL₂(𝒪_w)` (`Subgroup.exists_pow_mem_of_index_ne_zero`), and `ℤᵐ⁰` has
  no torsion (`pow_lt_one₀`/`one_lt_pow₀`) — no openness lemma for `{v = 1}` needed. `heckeElement_eq_…` by
  `Quotient.sound` + `DoubleCoset.rel_iff`.

### [CLEANUP-23] `/cleanup` of `Level/HeckePair.lean` (final for the file)

- **Status**: done   (finished 2026-09-29) · **File**: `Level/HeckePair.lean` · **Depends on**: [T057] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-29: DONE inline. Sorry-free, `#print axioms` standard on 15 declarations, `runLinter`
  passes on Local/Standard/HeckePair, no build warnings, lines ≤ 100; module docstring lists every main
  declaration; docstrings added to `mem_wildMonoid_iff`, `toMatrix_etaAdelic(Rep)`, and (missed by
  CLEANUP-18/19) to `Local.mem_monoidM_iff`, `iwahoriPrincipal_le_iwahoriOne`, `iwahoriOne_le_iwahori`,
  `iwahoriPrincipal_normal`, `coe_etaRep`, `Standard.standardLevel_le_U0`, `U1Level_le_U0Level`.
  `runLinter` (`unusedArguments`) found `[Finite κ]` + `[Fintype ι]` unused in the fixed statement of
  `hasWildLevel_U0Level` and `[Finite κ]` + `[Fintype ι']` in `unitAt_iwahoriPrincipal_le_U1Level`: REMOVED
  (no callers; the standard levels need neither).

### [CLEANUP-ALL-1] `/cleanup-all` before milestone M1

- **Status**: done   (finished 2026-10-01) · **Depends on**: [T057] and every cleanup ticket above · **Type**: cleanup

Project-wide pass over `Quaternion/`, `Adelic/`, `Level/`: naming consistency across files, duplicated helpers merged, import
minimisation (replace `import Mathlib` by the needed modules), `#lint` clean.

#### Progress

- 2026-10-01: DONE inline (together with the import part of CLEANUP-ALL-2). The four `import Mathlib`
  roots (`Level/Local`, `Quaternion/ReducedNorm`, `Adelic/RightBaseChange`, `Adelic/FiniteAdeles`) replaced by
  per-file Mathlib imports: `lake shake` refuses non-`module` files, so a metaprogram listed, for every
  board module, the modules of the constants its declarations use (instances excluded: with full
  Mathlib, typeclass search had picked e.g. `SimplexCategory` `Fintype` instances and `Field.henselian`),
  and the minimal antichain over the new import graph was written into each file; the build then asked
  for four instance-only modules (`RingTheory.TensorProduct.Finite`, `NumberField.Completion.FinitePlace`,
  `MetricSpace.Ultra.TotallySeparated`, `Data.Pi.Interval`). Whole chain rebuilt: 0 errors, 0 warnings,
  `runLinter` passes on all 22 modules, 54 axiom checks standard. Builds are now seconds per file.

### [M1] Milestone: the general theory of Layer 0

- **Status**: done   (finished 2026-10-01) · **Depends on**: [CLEANUP-ALL-1] · **Type**: milestone

#### Statement

`lake build PhD.TauCeti.Code.OverconvergentForms.Level.HeckePair` and `….Adelic.Norm` succeed with no
`sorry`; `#print axioms` on `AdelicAlgebra.bijOn_etaAdelicRep`, `AdelicAlgebra.isHeckeTriple_wildMonoidOf`,
`AdelicAlgebra.normClass_unitsIncl`, `AdelicAlgebra.hasFiniteClassSets_of_finite` and
`AdelicAlgebra.finite_stabilizer` shows the standard axioms only. Record the declaration count and the
result in `plan.md`. Nothing is proved in this ticket.

#### Progress

- 2026-10-01: DONE. `Level.HeckePair` and `Adelic.Norm` build sorry-free (0 warnings); the five named
  declarations depend on `[propext, Classical.choice, Quot.sound]` only; 482 declarations (321 public) in
  the 14 general-theory files. Recorded in `plan.md` (§ Milestones).

### [T058] `splitHom`, `splitHom_apply`, `splitEquiv` and 1 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Splitting.lean` · **Depends on**: [T015] · **Type**: proof · **Leaves**: L15.1, L15.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def splitHom (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) : ℍ[R] →ₐ[R] Matrix (Fin 2) (Fin 2) S := by
  sorry
theorem splitHom_apply (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (x : ℍ[R]) :
    splitHom ν ξ h x =
      !![algebraMap R S x.re + algebraMap R S x.imI * ν + algebraMap R S x.imK * ξ,
        algebraMap R S x.imI * ξ - algebraMap R S x.imJ - algebraMap R S x.imK * ν;
        algebraMap R S x.imI * ξ + algebraMap R S x.imJ - algebraMap R S x.imK * ν,
        algebraMap R S x.re - algebraMap R S x.imI * ν - algebraMap R S x.imK * ξ] := by
  sorry
def splitEquiv (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (h2 : IsUnit (2 : S)) :
    ℍ[R] ⊗[R] S ≃ₐ[S] Matrix (Fin 2) (Fin 2) S := by
  sorry
theorem splitEquiv_tmul (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (h2 : IsUnit (2 : S)) (x : ℍ[R])
    (s : S) : splitEquiv (R := R) ν ξ h h2 (x ⊗ₜ s) = s • splitHom ν ξ h x := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L15.1** `splitHom`, `splitHom_apply` — [RM] §0.1.3 "a rigidification is
  `a + bi + cj + dk ↦ ((a + bν + dξ, bξ − c − dν), (bξ + c − dν, a − bν − dξ))` for `ν, ξ ∈ ℤ_q` with
  `ν² + ξ² = −1` (Jacobs, §1.4)". Lean: for every commutative `R`-algebra `S`. Sketch:
  `QuaternionAlgebra.Basis.liftHom` with `i := I`, `j := J`, `k := IJ`; the relations are in the
  substrate. [SRC] `1_Setting.thetaBasis` (`ξ = 1`). Attacks: [1] the `k`-column of the formula is
  `(dξ, −dν; −dν, −dξ)`, and `IJ = ((ξ, −ν), (−ν, −ξ))` ✓ matches. SURVIVED.

- **L15.2** `splitEquiv`, `splitEquiv_tmul` — `ℍ[R] ⊗[R] S ≃ₐ[S] M₂(S)` for `IsUnit (2 : S)`.
  Sketch: substrate — a linear map sending a basis (`rightBasis (basisOneIJK …)`) to a basis is
  bijective; or Jacobs's explicit inverse ([SRC] `1_Setting`, "Surjectivity of `thetaK`"). Attacks:
  [3] `IsUnit 2` is necessary: over `S = 𝔽₂`-algebras the image is commutative. The coordinate
  determinant is `±4`, so the hypothesis is sharp ✓. SURVIVED.

#### Mathlib lemmas needed

`QuaternionAlgebra.Basis.liftHom`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3 (module docstring: §0.1.2, §0.1.3, Examples).
- Literature: the quotations of the module docstring of `Hamilton/Splitting.lean`.
- [SRC] (proof idea only, never imported): `1_Setting`, `1_Setting.thetaBasis`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-30: DONE (Hamilton/Splitting.lean T058–T060 in one pass; 4 fix rounds). `splitHom` =
  `QuaternionAlgebra.Basis.liftHom` of `I = ((ν, ξ), (ξ, −ν))`, `J = ((0, −1), (1, 0))`, `K = IJ`;
  `splitHom_apply` by a definitional `change` (rewriting with `liftHom_apply` fails: `ℍ[R]`'s instances are
  not syntactically those of `ℍ[R,-1,0,-1]`). `splitEquiv` = `AlgEquiv.ofBijective` of the `S`-algebra map
  built as in `Quaternion/BaseChange` (`TensorProduct.lift`, then `commutes'` for `S`): SURJECTIVE by an
  explicit preimage for any `t` with `2t = 1`, INJECTIVE by the Orzech property
  (`OrzechProperty.injective_of_surjective_of_injective` against a basis equivalence). NEW public
  `splitEquiv_symm_apply` (the explicit inverse, consumed by `theta3_isIntegral`). TRAPS: a quaternion
  literal `⟨0, 1, 0, 0⟩ : ℍ[R]` infers type `ℍ[R,-1,0,-1]`, which simp/rw cannot assign to an `x : ℍ[R]`
  pattern variable (`Quaternion` is not reducible) → put the literals in a vector
  `![(1 : ℍ[R]), ⟨0, 1, 0, 0⟩, …] n`, whose entries have type `ℍ[R]`, and sum over `Fin 4`;
  `first | ring | …` never falls through (`ring` falls back to `ring_nf` without failing) → `ring1`;
  `Algebra.smul_def` fires at the matrix level before `Matrix.smul_apply` → `Algebra.smul_def (A := S)`.

### [T059] `exists_sq_add_sq_eq_neg_one`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Splitting.lean` · **Depends on**: [T058] · **Type**: proof · **Leaves**: L15.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_sq_add_sq_eq_neg_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ ν ξ : ℤ_[q], ν ^ 2 + ξ ^ 2 = -1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L15.3** `exists_sq_add_sq_eq_neg_one` — [RM] §0.1.3 "which exists by Hensel's lemma"; Examples
  "split at every odd prime". Lean: `∃ ν ξ : ℤ_[q], ν² + ξ² = −1` for `q` odd. Sketch: modulo `q`
  by `ZMod.sq_add_sq` (every element of `ZMod q` is a sum of two squares); one of the two is
  nonzero modulo `q`, say `ν₀`; `hensels_lemma` for `X² + ξ₀² + 1` at `ν₀`, derivative `2ν₀` a unit.
  Attacks: [2] `q = 2` excluded ✓ (L15.4 shows it must be). [5] both names verified. SURVIVED.

#### Mathlib lemmas needed

`ZMod.sq_add_sq`, `hensels_lemma`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3 (module docstring: §0.1.2, §0.1.3, Examples).
- Literature: the quotations of the module docstring of `Hamilton/Splitting.lean`.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-30: DONE. `ZMod.sq_add_sq` modulo `q`, lifted by `hensels_lemma` at `X² + c`,
  `c = ξ₀² + 1` kept opaque (else simp expands `C (ξ₀² + 1)`); `‖x‖ < 1 ↔ toZMod x = 0` by `ker_toZMod`,
  `mem_maximalIdeal`, `mem_nonunits`; `2 ≠ 0` in `ZMod q` by `Ring.two_ne_zero` + `ZMod.ringChar_zmod_n`.

### [T060] `nrd_eq_zero_iff_of_padic_two`, `not_exists_sq_add_sq_eq_neg_one_padic_two`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Splitting.lean` · **Depends on**: [T059] · **Type**: proof · **Leaves**: L15.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem nrd_eq_zero_iff_of_padic_two (x : ℍ[ℚ_[2]]) : QuaternionAlgebra.nrd x = 0 ↔ x = 0 := by
  sorry
theorem not_exists_sq_add_sq_eq_neg_one_padic_two : ¬ ∃ ν ξ : ℚ_[2], ν ^ 2 + ξ ^ 2 = -1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L15.4** `nrd_eq_zero_iff_of_padic_two`, `not_exists_sq_add_sq_eq_neg_one_padic_two` — [RM]
  Examples "ramified at `2` (the Hilbert symbol `(−1, −1)_q`)"; [Jac03, Lemma 1.19] (quoted). Lean:
  the reduced norm of `ℍ[ℚ_[2]]` is anisotropic. Sketch: scale a nontrivial zero to `ℤ₂⁴` with one
  odd coordinate; a sum of four squares with an odd term is `≢ 0 mod 8` (squares are `0, 1, 4`; the
  sums with at least one `1` are `1,…,7`). `decide` on `ZMod 8`. Attacks: [1] `1 + 1 + 1 + 1 = 4`,
  `1 + 1 + 1 + 4 = 7`, `1 + 1 + 4 + 4 = 2`, `1 + 4 + 4 + 4 = 5` mod 8 — none is `0` ✓. [4] the
  roadmap's "ramified" is rendered as "the base change is a division algebra" (anisotropic norm),
  the form L1.5 turns into `IsUnit x ↔ x ≠ 0`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.2, §0.1.3, Examples).
- Literature: [Jac03]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (3) **The reduced norm lives on Mathlib's `ℍ[R,a,b]`**

#### Progress

- 2026-09-30: DONE. Divide by the coordinate of largest norm (`Finset.exists_max_image` on
  `Fin 4`): the others become `ℤ_2`-integral (named by `obtain` so that they have type `ℤ_[2]`, not the
  unfolded subtype) and `1 + a² + b² + c² ≠ 0` modulo `8` by `decide` on `ZMod 8`. Traps: `map_zero` at the
  `Quaternion` zero needs `exact`; `rw [← hx]` with `hx : nrd x = 0` abstracts the `0` inside
  `ℍ[ℚ_2,-1,0,-1]` → rewrite `nrd_apply` in a copy instead.

### [CLEANUP-24] `/cleanup` of `Hamilton/Splitting.lean` (final for the file)

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Splitting.lean` · **Depends on**: [T060] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline (see T058–T060). Sorry-free, standard axioms, `runLinter` passes, no
  warnings, lines ≤ 100; docstrings added to `splitHom_apply`, `splitEquiv_tmul`; module docstring lists
  every main declaration.

### [T061] `padicPlace`, `valued_natCast_padicPlace`, `valued_intCast_eq_one`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Setting.lean` · **Depends on**: [T060], [T026] · **Type**: proof · **Leaves**: L16.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def padicPlace (q : ℕ) [Fact q.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, Fact.out⟩
theorem valued_natCast_padicPlace (q : ℕ) [Fact q.Prime] :
    Valued.v ((q : ℚ) : (padicPlace q).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  sorry
theorem valued_intCast_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) :
    Valued.v ((n : ℚ) : (padicPlace q).adicCompletion ℚ) = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L16.1** `padicPlace`, `valued_natCast_padicPlace`, `valued_intCast_eq_one` — `q` is a
  uniformiser at the place `q` of `ℚ`. [SRC] `1_Setting.norm_three_lt_one`, `2_PadicEmbedding.
  norm_three_eq`. Sketch: `Rat.HeightOneSpectrum.natGenerator`, `span_natGenerator`,
  `valuedAdicCompletion_eq_valuation'`, `intValuation` of a generator. Attacks: [5] **known seam**
  ([SRC] module docstring): `Algebra ℚ (v.adicCompletion ℚ)` has two instance paths,
  `DivisionRing.toRatAlgebra` and the adic one, equal but not syntactically; the skeleton writes
  every rational cast as `((n : ℚ) : K)` through the adic coercion so that only one path occurs.
  SURVIVED.

#### Mathlib lemmas needed

`Rat.HeightOneSpectrum.natGenerator`, `span_natGenerator`, `valuedAdicCompletion_eq_valuation'`, `DivisionRing.toRatAlgebra`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.3, §0.5).
- Literature: the quotations of the module docstring of `Hamilton/Setting.lean`.
- [SRC] (proof idea only, never imported): `1_Setting.norm_three_lt_one`.

#### Generality decision

Binding decisions of `plan.md`: (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-30: DONE (Hamilton/Setting.lean T061–T063 in one pass; 4 fix rounds). KEY FINDING: the
  skeleton's `((n : ℚ) : ℚ_q)` elaborates to `Rat.cast`, NOT the adic coercion (`Coe K (adicCompletion K v)`
  has priority 99) — contrary to the planning note. NEW public bridge `valued_ratCast :
  Valued.v (r : ℚ_w) = w.valuation ℚ r` (via `algebraMap_adicCompletion`, `rfl`, and `eq_ratCast`); then
  `valuation_of_algebraMap`, `intValuation_singleton` with `𝔭 = (q)` from `span_natGenerator`
  (`comap_map_of_bijective`, `← Ideal.map_symm`).

### [T062] `exists_sq_add_sq_eq_neg_one_adicCompletion`, `rigidificationOfOdd`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Setting.lean` · **Depends on**: [T061] · **Type**: proof · **Leaves**: L16.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_sq_add_sq_eq_neg_one_adicCompletion (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ ν ξ : (padicPlace q).adicCompletion ℚ, ν ^ 2 + ξ ^ 2 = -1 ∧ Valued.v ν ≤ 1 ∧
      Valued.v ξ ≤ 1 := by
  sorry
abbrev rigidificationOfOdd (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    RigidificationAt ℚ ℍ[ℚ] (padicPlace q) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L16.2** `exists_sq_add_sq_eq_neg_one_adicCompletion`, `rigidificationOfOdd` — [RM] Examples
  "`ℍ[ℚ]` split at every odd prime". L15.3 transported along `Padic.adicCompletionEquiv`
  (a ring isomorphism preserving integrality), then L15.2. SURVIVED.

#### Mathlib lemmas needed

`Padic.adicCompletionEquiv`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.1.3, §0.5).
- Literature: the quotations of the module docstring of `Hamilton/Setting.lean`.

#### Generality decision

Binding decisions of `plan.md`: (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-30: DONE. `PadicInt.adicCompletionIntegersEquiv` carries the `ℤ_q` solution with its
  integrality; its codomain is ASCRIBED `(padicPlace q).adicCompletionIntegers ℚ` (else equations live at
  `primesEquiv.symm ⟨q, _⟩` and `simpa`/`rw` do not match through `padicPlace`). `IsUnit 2` by a private
  `isUnit_two` (a multi-line `by simpa using …` term inside `⟨…⟩` broke the parser).

### [T063] `exists_sqrt_neg_two`, `ν₃`, `sq_ν₃` and 5 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Setting.lean` · **Depends on**: [T062] · **Type**: proof · **Leaves**: L16.3, L16.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_sqrt_neg_two : ∃ x : K₃, x ^ 2 = -2 ∧ Valued.v (x - 1) < 1 := by
  sorry
def ν₃ : K₃ := exists_sqrt_neg_two.choose
theorem sq_ν₃ : ν₃ ^ 2 = -2 := exists_sqrt_neg_two.choose_spec.1
theorem valued_ν₃_sub_one : Valued.v (ν₃ - 1) < 1 := exists_sqrt_neg_two.choose_spec.2
theorem valued_ν₃ : Valued.v ν₃ = 1 := by
  sorry
theorem valued_ν₃_sub_twentyTwo : Valued.v (ν₃ - 22) ≤ Valued.v ((27 : ℚ) : K₃) := by
  sorry
instance theta3 : RigidificationAt ℚ ℍ[ℚ] v₃ where
  equiv := Quaternion.splitEquiv ν₃ 1 (by sorry) (by sorry)
theorem toMatrix_unitsIncl (x : (ℍ[ℚ])ˣ) :
    toMatrix ℚ ℍ[ℚ] v₃ (unitsIncl ℚ ℍ[ℚ] x) =
      Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) (by sorry) (x : ℍ[ℚ]) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L16.3** `exists_sqrt_neg_two`, `ν₃`, `sq_ν₃`, `valued_ν₃_sub_one`, `valued_ν₃`,
  `valued_ν₃_sub_twentyTwo` — [RM] §0.5 "`ν = √−2 ∈ ℤ_3` (the root that is `≡ 1 mod 3`)". Sketch:
  Hensel at `1` for `X² + 2` (`1 + 2 = 3 ≡ 0`, derivative `2`); `22² = 484 = −2 + 2·3⁵` and
  `ν₃ + 22 ≡ 2 mod 3` is a unit, so `v(ν₃ − 22) = v(ν₃² − 484) ≤ v(3)⁵ ≤ v(27)`. [SRC]
  `1_Setting.ν₃`, `5_Factorisations.norm_ν₃_sub_22`. Attacks: [2] `22 ≡ 1 mod 3` ✓ the right root.
  SURVIVED.

- **L16.4** `theta3` (the two proof fields), `toMatrix_unitsIncl` — [RM] §0.5 "the rigidification
  `θ₃` of §0.1.3". `ν₃² + 1² = −1`; `2` is a unit of the field `K₃`. `θ₃(x ⊗ 1) = splitHom ν₃ 1 x` by
  L15.2. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3, §0.5 (module docstring: §0.1.3, §0.5).
- Literature: the quotations of the module docstring of `Hamilton/Setting.lean`.
- [SRC] (proof idea only, never imported): `1_Setting.ν₃`.

#### Generality decision

Binding decisions of `plan.md`: (4) **`RigidificationAt` is an `F_v`-algebra isomorphism**

#### Progress

- 2026-09-30: DONE. Hensel for `X² + 2` at `1` in `ℤ_3`, transported; `z − 1 = 3w` gives
  `v(ν₃ − 1) ≤ v(3) < 1`. Trap: simp does not evaluate `E 2`, `E 3` through the integer equivalence → write
  the literals as `1 + 1 (+ 1)` before transporting. `valued_ν₃_sub_twentyTwo`: `(ν₃ − 22)(ν₃ + 22) = −2·3⁵`
  with `ν₃ + 22 = (ν₃ − 1) + 23` a unit. `Valuation.map_add_eq_of_lt_right` takes the valuation explicitly
  (and an inline `by` proof of its hypothesis is postponed inside `rw` → state it with `have`).
  `mul_le_mul_left'` no longer exists → `mul_le_mul' le_rfl`. Public helpers `valued_three`,
  `valued_ofNat_eq_one` (used by Level).

### [CLEANUP-25] `/cleanup` of `Hamilton/Setting.lean` (final for the file)

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Setting.lean` · **Depends on**: [T063] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline (see T061–T063). Sorry-free, standard axioms, `runLinter` passes, no
  warnings, lines ≤ 100; docstrings added to `sq_ν₃`, `valued_ν₃_sub_one`, `valued_ν₃`; module docstring
  lists every main declaration.

### [T064] `hurwitzBasis`, `hurwitzBasis_apply`, `isOrderBasis_hurwitzBasis` and 2 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Level.lean` · **Depends on**: [T063], [T010], [T057] · **Type**: proof · **Leaves**: L17.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def hurwitzBasis : Module.Basis (Fin 4) ℚ ℍ[ℚ] := by
  sorry
theorem hurwitzBasis_apply (i : Fin 4) :
    hurwitzBasis i = ![(1 : ℍ[ℚ]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, hurwitzOmega] i := by
  sorry
theorem isOrderBasis_hurwitzBasis : IsOrderBasis hurwitzBasis := by
  sorry
theorem orderOf_hurwitzBasis : orderOf hurwitzBasis isOrderBasis_hurwitzBasis = hurwitzOrder := by
  sorry
theorem unitsIncl_mem_U0_iff {x : (ℍ[ℚ])ˣ} :
    unitsIncl ℚ ℍ[ℚ] x ∈ U0 ↔
      (x : ℍ[ℚ]) ∈ hurwitzOrder ∧ ((x⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) ∈ hurwitzOrder := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L17.1** `hurwitzBasis`, `hurwitzBasis_apply`, `isOrderBasis_hurwitzBasis`,
  `orderOf_hurwitzBasis`, `unitsIncl_mem_U0_iff` — [RM] §0.5 "`𝒪_D` the Hurwitz order". The basis
  `1, i, j, ω`; structure constants from `ω² = ω − 1`, `iω = −1 − j + ω`, … (sixteen products, by
  `ext <;> norm_num`); `(algebraMap (𝓞 ℚ) ℚ).range = ℤ` (`Rat.ringOfIntegersEquiv`); L4.1.
  [SRC] `2_LevelTopology.hurwitzBasis`, `2_Level.mem_hurwitzOrder_iff_coords`. SURVIVED.

#### Mathlib lemmas needed

`Rat.ringOfIntegersEquiv`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5 (module docstring: §0.5).
- Literature: the quotations of the module docstring of `Hamilton/Level.lean`.
- [SRC] (proof idea only, never imported): `2_LevelTopology.hurwitzBasis`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-30: DONE (Hamilton/Level.lean T064–T066 in one pass). `hurwitzBasis` =
  `Module.Basis.ofEquivFun` of a private linear equivalence `hurwitzCoords` with coordinates
  `(re − k, i − k, j − k, 2k)` in the basis `1, I, J, ω`; its inverse is a private `rfl` lemma (simp does not
  evaluate `hurwitzCoords.symm`). `IsOrderBasis`/`orderOf = hurwitzOrder` from the coordinate criterion;
  public `exists_int_of_mem_range`, `imI/imJ/imK/hurwitzOmega_mem_hurwitzOrder` (explicit `IsHurwitz`
  witnesses: `zero_mul` does not fire on quaternion literals), `tmul_mem_localOrder`. TRAP: `norm_num`
  cannot evaluate the basis vector after `fin_cases` → dedicated membership lemmas closed by `exacts`.

### [T065] `theta3_isIntegral`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Level.lean` · **Depends on**: [T064] · **Type**: proof · **Leaves**: L17.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem theta3_isIntegral :
    RigidificationAt.IsIntegral hurwitzBasis isOrderBasis_hurwitzBasis v₃ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L17.2** `theta3_isIntegral` — [RM] §0.1.3 "carrying `𝒪_D ⊗ 𝒪_𝔭` onto `M₂(𝒪_𝔭)`". Sketch: `2` is
  a unit of `ℤ₃`, so `𝒪 ⊗ ℤ₃` has the `ℤ₃`-basis `1, i, j, k`; `θ₃` sends it to `1, I, J, IJ`,
  integral matrices (`ν₃` integral, L16.3) forming a `ℤ₃`-basis of `M₂(ℤ₃)` (substrate: coordinate
  determinant a unit). [SRC] `2_Level.theta_localOrder`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.3 (module docstring: §0.5).
- Literature: the quotations of the module docstring of `Hamilton/Level.lean`.
- [SRC] (proof idea only, never imported): `2_Level.theta_localOrder`.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-30: DONE. `⊆`: expand in `rightBasis`, the images `1, I, J, ω` of the basis are
  integral since `ν₃` and `1/2` are (`apply_rules` over the entries after `fin_cases`); `⊇`: the explicit
  inverse `Quaternion.splitEquiv_symm_apply` (with `t = 2⁻¹`) has integral Hurwitz coordinates, closed by
  `sum_mem` + `tmul_mem_localOrder` with EXPLICIT membership terms (`apply_rules` hit heartbeat timeouts on
  `adicCompletionIntegers` membership).

### [T066] `U1_9`, `valued_nine`, `mem_U1_9_iff` and 4 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Level.lean` · **Depends on**: [T065] · **Type**: proof · **Leaves**: L17.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def U1_9 : Subgroup (Dfx ℚ ℍ[ℚ]) :=
  U1Level hurwitzBasis isOrderBasis_hurwitzBasis (fun _ : Unit ↦ v₃) fun _ ↦ 2
theorem valued_nine : Valued.v ((9 : ℚ) : K₃) = levelThreshold 2 := by
  sorry
theorem mem_U1_9_iff {g : Dfx ℚ ℍ[ℚ]} :
    g ∈ U1_9 ↔ g ∈ U0 ∧ Valued.v (toMatrix ℚ ℍ[ℚ] v₃ g 1 0) ≤ Valued.v ((9 : ℚ) : K₃) ∧
      Valued.v (toMatrix ℚ ℍ[ℚ] v₃ g 1 1 - 1) ≤ Valued.v ((9 : ℚ) : K₃) := by
  sorry
theorem U1_9_le_U0 : U1_9 ≤ U0 := by
  sorry
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (Dfx ℚ ℍ[ℚ])) := by
  sorry
theorem isOpen_U1_9 : IsOpen (U1_9 : Set (Dfx ℚ ℍ[ℚ])) := by
  sorry
theorem mem_U1_9_of_toGL {g : Dfx ℚ ℍ[ℚ]}
    (h3 : toGL ℚ ℍ[ℚ] v₃ g ∈ LocalLevel.iwahoriOne K₃ (levelThreshold 2))
    (haway : ∀ w, w ≠ v₃ →
      toLocalUnits ℚ ℍ[ℚ] w g ∈ localUnits hurwitzBasis isOrderBasis_hurwitzBasis w) :
    g ∈ U1_9 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L17.3** `U1_9`, `valued_nine`, `mem_U1_9_iff`, `U1_9_le_U0`, `isCompact_U1_9`, `isOpen_U1_9`,
  `mem_U1_9_of_toGL` — [RM] §0.5 "`U₁(9)` has `3`-component
  `{((a b), (c d)) ∈ GL₂(ℤ_3) | 9 ∣ c, d ≡ 1 mod 9}`"; [Jac03, Definition 1.20, Proposition 1.21]
  (`jacobs_thesis.txt:525`, `:590`): "For all `n ∈ ℕ`, `U₀(pⁿ)` and `U₁(pⁿ)` are open compact
  subgroups of `D_f^×`." `U1Level` at `κ = Unit`; L12.3; `mem_U1_9_iff` by L9.8 (integrality and
  unit determinant are automatic on `U₀(1)`). Attacks: [4] Jacobs takes at `q = 2` "the group of
  units in any fixed maximal order of `D₂`"; ours is the local Hurwitz order, a maximal order ✓.
  SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5 (module docstring: §0.5).
- Literature: [Jac03]; quoted verbatim in the module docstring and the section substrate.

#### Generality decision

Binding decisions of `plan.md`: (5) **Orders are presented by a basis** (6) **Levels are `U₀(1)` cut down at finitely many places**

#### Progress

- 2026-09-30: DONE. `valued_nine` by `valued_three` and `exp_nsmul`; `mem_U1_9_iff` unfolds
  `U1Level`/`standardLevel`/`mem_levelAt_iff`; `isCompact_U1_9`/`isOpen_U1_9` from the general `U1Level`
  lemmas; `mem_U1_9_of_toGL` via `mem_U0_of_toGL`. Trap: `toGL_mem_integralGL` and `mem_U0_of_toGL` take
  the place `v₃` EXPLICITLY.

### [CLEANUP-26] `/cleanup` of `Hamilton/Level.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/Level.lean` · **Depends on**: [T066] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Sorry-free, standard axioms, 0 warnings, lines ≤ 100, docstrings on every
  public declaration, module docstring lists every main declaration. `runLinter` flagged
  `Hamilton.U1_9` (`defsWithUnderscore`): the name is fixed by the skeleton and used downstream, so it
  carries `@[nolint defsWithUnderscore]`; `runLinter` then passes.

### [T067] `exists_intCast_mul_mem_integralAdeles`, `exists_intCast_smul_toLocal_mem`, `exists_intCast_approx`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [T066] · **Type**: proof · **Leaves**: L18.1, L18.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_intCast_mul_mem_integralAdeles (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ((N : ℚ) : v.adicCompletion ℚ) * a v ∈ v.adicCompletionIntegers ℚ := by
  sorry
theorem exists_intCast_smul_toLocal_mem (x : Df ℚ ℍ[ℚ]) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ w, toLocal ℚ ℍ[ℚ] w ((N : ℚ) • x) ∈ 𝒪loc w := by
  sorry
theorem exists_intCast_approx {w : HeightOneSpectrum (𝓞 ℚ)}
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hw : w ∉ T) (c : w.adicCompletionIntegers ℚ) {M : ℤ}
    (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - ((z : ℚ) : w.adicCompletion ℚ)) ≤
        Valued.v (((M : ℚ)) : w.adicCompletion ℚ) ∧
      ∀ v ∈ T, Valued.v (((z : ℚ)) : v.adicCompletion ℚ) ≤
        Valued.v (((M : ℚ)) : v.adicCompletion ℚ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L18.1** `exists_intCast_mul_mem_integralAdeles`, `exists_intCast_smul_toLocal_mem` — clearing
  denominators. [SRC] `CN1/3_AdeleIntegrality.exists_intCast_mul_mem_adicCompletionIntegers_forall`,
  `.exists_intCast_smul_toLocal_mem`. `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers`
  at each of the finitely many bad places, product of the integers. SURVIVED.

- **L18.2** `exists_intCast_approx` — integer approximation: `c ∈ ℤ_w` is congruent modulo `M` to an
  integer divisible by `M` at the places of `T ∌ w`. [SRC] `CN1/3_LocalApprox.exists_intCast_approx`
  (density of `ℤ` in `ℤ_w` and the Chinese remainder theorem in `ℤ`). SURVIVED.

#### Mathlib lemmas needed

`adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.3.5, §0.5.1).
- Literature: the quotations of the module docstring of `Hamilton/ClassNumberOne.lean`.
- [SRC] (proof idea only, never imported): `CN1/3_AdeleIntegrality.exists_intCast_mul_mem_adicCompletionIntegers_forall`, `CN1/3_LocalApprox.exists_intCast_approx`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE (Hamilton/ClassNumberOne.lean T067–T070 in one pass). Clearing denominators
  through `FiniteAdeleRing` integrality at all but finitely many places; `exists_intCast_approx` =
  density of `ℚ` in `ℚ_w` (`denseRange_algebraMap`) + `exists_valuation_sub_lt_of_integer`, times an
  integer that is a `w`-unit and divisible by `M` at the places of `T` (induction on `T`, prime avoidance
  `SetLike.not_le_iff_exists` between distinct maximal ideals). Bridge: `valued_ratCast` + `eq_ratCast`.

### [T068] `denominatorIdeal`, `denominatorIdeal_ne_bot`, `exists_mem_denominatorIdeal_sub_smul`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [T067] · **Type**: proof · **Leaves**: L18.3, L18.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def denominatorIdeal (g : Dfx ℚ ℍ[ℚ]) : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder where
  carrier := {y | ∀ w : HeightOneSpectrum (𝓞 ℚ),
    toLocal ℚ ℍ[ℚ] w ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) * ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1) ∈ 𝒪loc w}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
theorem denominatorIdeal_ne_bot (g : Dfx ℚ ℍ[ℚ]) : denominatorIdeal g ≠ ⊥ := by
  sorry
theorem exists_mem_denominatorIdeal_sub_smul {g : Dfx ℚ ℍ[ℚ]} {N : ℤ} (hN : N ≠ 0)
    (hNmem : ((N : ℤ) : hurwitzOrder) ∈ denominatorIdeal g) {w : HeightOneSpectrum (𝓞 ℚ)}
    {ξ : Dv ℚ ℍ[ℚ] w} (hξ : ξ ∈ 𝒪loc w)
    (hξg : toLocal ℚ ℍ[ℚ] w ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) * ξ ∈ 𝒪loc w) :
    ∃ y ∈ denominatorIdeal g, ∃ δ ∈ 𝒪loc w, ξ - (y : ℍ[ℚ]) ⊗ₜ[ℚ] 1 = (N : ℚ) • δ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L18.3** `denominatorIdeal` (fields), `denominatorIdeal_ne_bot` — [Voi21, Lemma 27.6.8]
  "we recover `I = α̂ Ô ∩ B`". [SRC] `CN1/4_Dictionary.latticeOf`, `.latticeOf_ne_bot`. Right
  `𝒪`-stability: `g⁻¹ (y r) = (g⁻¹ y) r` and `r ⊗ 1` is locally integral. Nonzero: a common
  denominator of `g⁻¹` (L18.1) lies in it. SURVIVED.

- **L18.4** `exists_mem_denominatorIdeal_sub_smul` — the local lattice is generated modulo `N` by
  global elements. [SRC] `CN1/4_Dictionary.exists_mem_latticeOf_sub_smul`: coordinates of `ξ` in
  the basis, L18.2 coordinatewise at modulus `N²` with `T` the bad places of `g⁻¹` away from `w`.
  Attacks: [3] the square is needed (slack that makes both the error at `w` and the approximations
  at `T` divisible by `N`) ✓ as in [SRC]. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.3.5, §0.5.1).
- Literature: [Voi21]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `CN1/4_Dictionary.exists_mem_latticeOf_sub_smul`, `CN1/4_Dictionary.latticeOf`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `denominatorIdeal g` is a `Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder` (a right
  ideal); nonzero because it contains a nonzero rational integer (clear denominators, T067);
  `exists_mem_denominatorIdeal_sub_smul` by `exists_intCast_approx` place by place in the finite set of
  places where `g` is not integral.

### [T069] `exists_eq_generator_mul`, `exists_factor_of_forall_mem`, `exists_factor`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [T068] · **Type**: proof · **Leaves**: L18.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem exists_eq_generator_mul {g : Dfx ℚ ℍ[ℚ]}
    (hg : ∀ w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w) {x : hurwitzOrder}
    (hx : denominatorIdeal g = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x})
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ζ ∈ 𝒪loc w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) = ((x : ℍ[ℚ]) ⊗ₜ[ℚ] 1) * ζ := by
  sorry
theorem exists_factor_of_forall_mem {g : Dfx ℚ ℍ[ℚ]}
    (hg : ∀ w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w) :
    ∃ d ∈ globalUnits ℚ ℍ[ℚ], ∃ u ∈ U0, g = d * u := by
  sorry
theorem exists_factor (g : Dfx ℚ ℍ[ℚ]) : ∃ d ∈ globalUnits ℚ ℍ[ℚ], ∃ u ∈ U0, g = d * u := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L18.5** `exists_eq_generator_mul`, `exists_factor_of_forall_mem`, `exists_factor` — [RM] §0.3.5
  "`D_f^× = D^× · U₀(1)` for `D = ℍ[ℚ]` with the Hurwitz order: every right ideal of a
  right-Euclidean order is principal (§0.1.4), and the idelic dictionary […] (Voight, Lemma 27.6.8)
  turns this into the triviality of the class set. ⚠ Jacobs (Lemma 1.22) derives this from the
  absence of weight-two cusp forms through Jacquet–Langlands; the route above is the one to
  formalise". [SRC] `CN1/4_Dictionary.exists_eq_generator_mul`, `.exists_factor_of_forall_mem`,
  `.hClassNumberOne` (sorry-free on standard axioms). Attacks: [4] **JL audit**: no leaf of this
  file, nor of its imports, mentions modular forms; the JL route of [Jac03] is quoted above only to
  be set aside ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.1.4, §0.3.5 (module docstring: §0.3.5, §0.5.1).
- Literature: [Jac03]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `CN1/4_Dictionary.exists_eq_generator_mul`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `exists_eq_generator_mul` from `right_ideal_principal` (the Hurwitz order is
  right-Euclidean), then `x⁻¹ g` everywhere a unit (`exists_factor_of_forall_mem`), and `exists_factor`
  reduces to integral `g` by multiplying with the global unit `N` (clearing denominators). Trap:
  `show Valued.v _ ≤ 1` elaborated the `1` in `ℕ` → state the membership term explicitly.

### [CLEANUP-27] `/cleanup` of `Hamilton/ClassNumberOne.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [T069] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-30: DONE inline together with CLEANUP-28 (file finished in one pass).

### [T070] `subsingleton_classSet_U0`, `hasFiniteClassSets`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [CLEANUP-27] · **Type**: proof · **Leaves**: L18.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem subsingleton_classSet_U0 : Subsingleton (classSet ℚ ℍ[ℚ] U0) := by
  sorry
instance hasFiniteClassSets : HasFiniteClassSets ℚ ℍ[ℚ] := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L18.6** `subsingleton_classSet_U0`, `hasFiniteClassSets` — [RM] §0.5.1 "The class set of `U₀(1)`
  is trivial"; §0.3.2 (the conclusion of Fujisaki's lemma, for `ℍ[ℚ]`). L18.5; L13.3 with `U₀(1)`
  compact open. Attacks: [4] this is where plan.md decision 2 pays off: every open subgroup of
  `ℍ[ℚ]_f^×` has a finite class set with no Haar measure. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.3.2, §0.5.1 (module docstring: §0.3.5, §0.5.1).
- Literature: the quotations of the module docstring of `Hamilton/ClassNumberOne.lean`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `subsingleton_classSet_U0` from `exists_factor`; the instance
  `hasFiniteClassSets` = `hasFiniteClassSets_of_finite` at the compact open `U₀(1)`, whose class set is
  a point (`Module.Finite ℚ ℍ[ℚ]` from `hurwitzBasis`).

### [CLEANUP-28] `/cleanup` of `Hamilton/ClassNumberOne.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/ClassNumberOne.lean` · **Depends on**: [T070] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Sorry-free, standard axioms (23 declarations of Splitting/Setting/Level/
  ClassNumberOne checked), `runLinter` passes, 0 warnings, lines ≤ 100, module docstring lists every main
  declaration. `Quaternion/Hurwitz.lean`: `ofTuple` and its coordinate lemmas, `unitTuples`,
  `ofTuple_mem_of_mem_unitTuples`, `isUnit_ofTuple`, `exists_tuple_of_unit` made public (with docstrings)
  for the orbit computation of `Hamilton/ClassSet.lean`.

### [T071] `classDiag`, `diagGL`, `classRep` and 3 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T070] · **Type**: proof · **Leaves**: L19.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def classDiag : Fin 3 → ℤ × ℤ := ![(1, 1), (5, 2), (7, 4)]
def diagGL (x y : ℤ) (hx : ¬ (3 : ℤ) ∣ x) (hy : ¬ (3 : ℤ) ∣ y) : GL (Fin 2) K₃ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![((x : ℚ) : K₃), ((y : ℚ) : K₃)]) (by sorry)
def classRep (i : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  unitAt ℚ ℍ[ℚ] v₃ (diagGL (classDiag i).1 (classDiag i).2 (by sorry) (by sorry))
theorem classRep_zero : classRep 0 = 1 := by
  sorry
theorem toMatrix_classRep (i : Fin 3) :
    toMatrix ℚ ℍ[ℚ] v₃ (classRep i) =
      Matrix.diagonal ![(((classDiag i).1 : ℚ) : K₃), (((classDiag i).2 : ℚ) : K₃)] := by
  sorry
theorem classRep_mem_U0 (i : Fin 3) : classRep i ∈ U0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L19.1** `classDiag`, `diagGL` (field), `classRep` (two fields), `classRep_zero`,
  `toMatrix_classRep`, `classRep_mem_U0` — [RM] §0.5.2 "representatives `c_0 = 1`,
  `c_1 = ι_3(diag(5, 2))`, `c_2 = ι_3(diag(7, 4))` (Jacobs, Theorem 2.1)". L8.9, L9.8, L16.1.
  [SRC] `3_ClassSet.classRep`, `.toMatrix_classRep`, `.classRep_mem_U0`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.2 (module docstring: §0.5.2, §0.5.3).
- Literature: the quotations of the module docstring of `Hamilton/ClassSet.lean`.
- [SRC] (proof idea only, never imported): `3_ClassSet.classRep`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE (Hamilton/ClassSet.lean T071–T075 in one pass, 2 fix rounds). The two `sorry`
  proof obligations inside the fixed skeleton definitions (`diagGL`'s determinant, `classRep`'s
  divisibility) are discharged by NEW public `ratCast_ne_zero_of_not_dvd`, `classDiag_fst_not_dvd`,
  `classDiag_snd_not_dvd` (reused by Factorisations). `toMatrix_classRep` by `← coe_toGL`, `toGL_unitAt`;
  `classRep_mem_U0` by `unitAt_mem_U0_iff` and the integrality of `diag(x, y)`.

### [T072] `redMod9`, `redMod9_intCast`, `redMod9_eq_zero_iff` and 3 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T071] · **Type**: proof · **Leaves**: L19.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def redMod9 : v₃.adicCompletionIntegers ℚ →+* ZMod 9 := by
  sorry
theorem redMod9_intCast (n : ℤ) (h : ((n : ℚ) : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨((n : ℚ) : K₃), h⟩ = (n : ZMod 9) := by
  sorry
theorem redMod9_eq_zero_iff (x : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = 0 ↔ Valued.v (x : K₃) ≤ Valued.v ((9 : ℚ) : K₃) := by
  sorry
theorem redMod9_surjective : Function.Surjective redMod9 := by
  sorry
def redMat : integralMatrices v₃ →+* Matrix (Fin 2) (Fin 2) (ZMod 9) := by
  sorry
def unitsMod9 : (hurwitzOrder)ˣ →* GL (Fin 2) (ZMod 9) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L19.2** `redMod9`, `redMod9_intCast`, `redMod9_eq_zero_iff`, `redMod9_surjective`, `redMat`,
  `unitsMod9` — reduction modulo `9`. Sketch: `adicCompletionIntegers.padicIntEquiv` then
  `PadicInt.toZModPow 2`; `redMat` entrywise; `unitsMod9` is `redMat ∘ θ₃` on Hurwitz units (L17.2).
  [SRC] `3_ClassSet.redMod9`, `.redMat`, `.unitsMod9`. SURVIVED.

#### Mathlib lemmas needed

`adicCompletionIntegers.padicIntEquiv`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.5.2, §0.5.3).
- Literature: the quotations of the module docstring of `Hamilton/ClassSet.lean`.
- [SRC] (proof idea only, never imported): `3_ClassSet.redMod9`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `redMod9 = toZModPow 2 ∘ (adicCompletionIntegersEquiv)⁻¹` (codomain `ZMod (3^2)`
  accepted as `ZMod 9` by defeq); kernel = `9 𝒪₃` by transporting `ker_toZModPow` (divisibility inside
  the subtype, then the valuative form). `redMat` entrywise through `redMod9_add'/mul'` (the `congr 1`
  forms: letting the `ValuationSubring` subtype defeq do the work is slow). `unitsMod9` =
  `Units.map (redMat ∘ hurwitzToMat)`, `hurwitzToMat x = θ₃(x ⊗ 1)` landing in `M₂(ℤ_3)` by
  `theta3_isIntegral`.

### [T073] `primitiveVectors`, `card_primitiveVectors`, `mem_U1_9_iff_bottomRow` and 2 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T072] · **Type**: proof · **Leaves**: L19.3, L19.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def primitiveVectors : Finset (ZMod 9 × ZMod 9) :=
  Finset.univ.filter fun v ↦ IsUnit v.1 ∨ IsUnit v.2
theorem card_primitiveVectors : primitiveVectors.card = 72 := by
  sorry
theorem mem_U1_9_iff_bottomRow {g : Dfx ℚ ℍ[ℚ]} (hg : g ∈ U0)
    (hint : toMatrix ℚ ℍ[ℚ] v₃ g ∈ integralMatrices v₃) :
    g ∈ U1_9 ↔ Matrix.vecMul ![0, 1] (redMat ⟨toMatrix ℚ ℍ[ℚ] v₃ g, hint⟩) = ![0, 1] := by
  sorry
theorem existsUnique_orbit {x : ZMod 9 × ZMod 9} (hx : x ∈ primitiveVectors) :
    ∃! i : Fin 3, ∃ γ : (hurwitzOrder)ˣ,
      Matrix.vecMul ![x.1, x.2] (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) =
        ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹] := by
  sorry
theorem eq_one_of_vecMul_unitsMod9 {i : Fin 3} {γ : (hurwitzOrder)ˣ}
    (h : Matrix.vecMul ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹]
      (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) =
        ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹]) : γ = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L19.3** `primitiveVectors`, `card_primitiveVectors`, `mem_U1_9_iff_bottomRow` — [RM] §0.5.2 "the
  `72` primitive vectors of `(ℤ/9)²`". `decide`; L17.3 with L19.2 (`9 ∣ c` and `d ≡ 1 mod 9` say
  the bottom row is `(0, 1)`). SURVIVED.

- **L19.4** `existsUnique_orbit`, `eq_one_of_vecMul_unitsMod9` — [RM] §0.5.2 "a finite computation
  with three orbits, represented by `(1, 0)`, `(5, 0)`, `(7, 0)`"; §0.5.3 "a Hurwitz unit in
  `c_i U₁(9) c_i^{−1}` reduces to a matrix `≡ ((∗ ∗), (0 1)) mod 9` and only `1` does". [SRC]
  `3_ClassSet.orbits_unitsMod9`, `.only_one_tuple_sigma1`: the `24` unit tuples (L4.4) are reduced
  explicitly (`ν₃ ≡ 4 mod 9`, [SRC] `redMod9_ν₃`) and the statement is a `decide` over
  `24 × 72`. Attacks: [4] **convention check**: the invariant of the coset `u U₁(9)` is the bottom
  row of `θ₃(u)⁻¹`, so the representatives are the bottom rows `(0, d_i⁻¹) = (0,1), (0,5), (0,7)` of
  `c_i⁻¹` (`2⁻¹ = 5`, `4⁻¹ = 7` mod `9`); the roadmap's "`(1, 0), (5, 0), (7, 0)`" is the same set in
  Jacobs's transposed convention. [SRC] states the orbit relation as `(0, d_i⁻¹) · γ̄ = x`; ours is
  `x · γ̄ = (0, d_i⁻¹)`, equivalent by `γ ↦ γ⁻¹`. [1] sanity: could `(0,5)` be in the orbit of
  `(0,1)`? It would need a Hurwitz unit with `θ₃ ≡ ((2 ∗), (0 5))`, trace `7 ≡ −2`, so `γ = −1`, whose
  matrix is `−1` — no ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.2, §0.5.3 (module docstring: §0.5.2, §0.5.3).
- Literature: the quotations of the module docstring of `Hamilton/ClassSet.lean`.
- [SRC] (proof idea only, never imported): `3_ClassSet.orbits_unitsMod9`, `redMod9_ν₃`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `card_primitiveVectors` and the orbit table by kernel `decide` (no
  `native_decide`): `unitsMod9 γ = tupleMat t` for `ofTuple t = γ` (entries `a/2 + (b/2) ν₃ ↦ 5(a + 4b)`
  via `1/2 ≡ 5`, `ν₃ ≡ 22 ≡ 4 mod 9`), so `∃ γ` is `∃ t ∈ unitTuples` over the `24` tuples; the
  inverses `d_i⁻¹` normalised to `![1, 5, 7] i` by `ZMod.inv_eq_of_mul_eq_one`. `tupleMat`'s entries are
  written in exactly the shape `redMod9_half` produces, so each entry closes by `rfl`.

### [CLEANUP-29] `/cleanup` of `Hamilton/ClassSet.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T073] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-30: DONE inline together with CLEANUP-30 (file finished in one pass).

### [T074] `isCompleteFamily_classRep`, `isSection_classRep`, `card_classSet_U1_9`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [CLEANUP-29] · **Type**: proof · **Leaves**: L19.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem isCompleteFamily_classRep : IsCompleteFamily classRep U1_9 := by
  sorry
theorem isSection_classRep : IsSection classRep U1_9 := by
  sorry
theorem card_classSet_U1_9 : Nat.card (classSet ℚ ℍ[ℚ] U1_9) = 3 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L19.5** `isCompleteFamily_classRep`, `isSection_classRep`, `card_classSet_U1_9` — [RM] §0.5.2
  "The class set of `U₁(9)` has three elements"; [Jac03, Theorem 2.1]. Sketch: `g = d u` with
  `u ∈ U₀(1)` (L18.5); the bottom row of `θ₃(u)⁻¹` is primitive; L19.4 gives `γ` and `i`, and
  `g = (d γ') c_i w` with `w ∈ U₁(9)` by L19.3. Distinctness from the uniqueness in L19.4. [SRC]
  `3_ClassSet.classRep_complete`, `.classRep_bijective`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.2 (module docstring: §0.5.2, §0.5.3).
- Literature: [Jac03]; quoted verbatim in the module docstring and the section substrate.
- [SRC] (proof idea only, never imported): `3_ClassSet.classRep_complete`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. Through `redU0 : U₀(1) →* M₂(ℤ/9)` and the key private equivalence
  `u cᵢ ∈ U₁(9) ↔ (0,1)·ū = (0, yᵢ⁻¹)` (`vecMul_diag_eq_iff` by `decide` over `3 × 81`). Completeness:
  `g = d u` (class number one), the bottom row of `ū⁻¹` is primitive (units of `ℤ/9` = nonzero mod `3`,
  `decide`), `existsUnique_orbit` gives `γ, i`, and `g = (d γ) cᵢ (cᵢ⁻¹ γ⁻¹ u)`. Distinctness: `c_j = d cᵢ w`
  forces `d ∈ D^× ∩ U₀(1)` (a Hurwitz unit) with `(0, y_j⁻¹) γ̄ = (0, yᵢ⁻¹)`, and uniqueness of the orbit
  of `(0, y_j⁻¹)`.

### [T075] `stabilizer_classRep`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T074] · **Type**: proof · **Leaves**: L19.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem stabilizer_classRep (i : Fin 3) : stabilizer (classRep i) U1_9 = ⊥ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L19.6** `stabilizer_classRep` — [RM] §0.5.3 "The three stabilisers `Γ_i` are trivial (Jacobs,
  Lemma 2.2)". Sketch: `u ∈ Γ_i` gives `γ = c_i u c_i⁻¹ ∈ D^× ∩ U₀(1)`, a Hurwitz unit (L17.1) with
  `(0, d_i⁻¹) γ̄ = (0, d_i⁻¹)`; L19.4. [SRC] `3_ClassSet.stabilizerAt_classRep`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.3 (module docstring: §0.5.2, §0.5.3).
- Literature: the quotations of the module docstring of `Hamilton/ClassSet.lean`.
- [SRC] (proof idea only, never imported): `3_ClassSet.stabilizerAt_classRep`.

#### Generality decision

Binding decisions of `plan.md`: (2) **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.**

#### Progress

- 2026-09-30: DONE. `cᵢ u cᵢ⁻¹ ∈ D^× ∩ U₀(1)` is a Hurwitz unit fixing `(0, yᵢ⁻¹)` modulo `9`,
  hence `1` by `eq_one_of_vecMul_unitsMod9`.

### [CLEANUP-30] `/cleanup` of `Hamilton/ClassSet.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/ClassSet.lean` · **Depends on**: [T075] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Sorry-free, 14 public results with standard axioms, 0 warnings
  (unused simp arguments removed), lines ≤ 100, `runLinter` passes; `ratCast_ne_zero_of_not_dvd`,
  `classDiag_fst_not_dvd`, `classDiag_snd_not_dvd` made public (reused by Factorisations); module docstring
  lists every main declaration.

### [T076] `three_ne_zero'`, `valued_three_lt_one`, `valued_le_valued_three` and 1 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/EtaDecomposition.lean` · **Depends on**: [T075] · **Type**: proof · **Leaves**: L20.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem three_ne_zero' : ((3 : ℚ) : K₃) ≠ 0 := by
  sorry
theorem valued_three_lt_one : Valued.v ((3 : ℚ) : K₃) < 1 := by
  sorry
theorem valued_le_valued_three {x : K₃} (hx : Valued.v x < 1) :
    Valued.v x ≤ Valued.v ((3 : ℚ) : K₃) := by
  sorry
theorem existsUnique_fin_three {x : K₃} (hx : Valued.v x ≤ 1) :
    ∃! t : Fin 3, Valued.v (x - (((t : ℕ) : ℚ) : K₃)) < 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L20.1** `three_ne_zero'`, `valued_three_lt_one`, `valued_le_valued_three`,
  `existsUnique_fin_three` — `3` is a uniformiser of `K₃` and `{0, 1, 2}` a residue system. L16.1;
  [SRC] `3_EtaDecomposition.exists_fin3_approx`, `.valued_sub_eq_one`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.5.4).
- Literature: the quotations of the module docstring of `Hamilton/EtaDecomposition.lean`.
- [SRC] (proof idea only, never imported): `3_EtaDecomposition.exists_fin3_approx`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-30: DONE (Hamilton/EtaDecomposition.lean T076–T077 in one pass). `valued_le_valued_three`
  through `WithZero.exp_log` and `omega` on the exponent. `existsUnique_fin_three` WITHOUT a second copy of
  the `ℤ_3` equivalence: existence from the public integer approximation `exists_intCast_approx` (T067,
  `T = ∅`, `M = 3`) reduced modulo `3` by cases on `z % 3`; uniqueness since distinct residues differ by
  `±1, ±2`, units at `3` (`valued_intCast_eq_one`).

### [T077] `eta3`, `etaRep3`, `toMatrix_etaRep3` and 2 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/EtaDecomposition.lean` · **Depends on**: [T076] · **Type**: proof · **Leaves**: L20.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def eta3 : Dfx ℚ ℍ[ℚ] := etaAdelic ℚ ℍ[ℚ] v₃ ((3 : ℚ) : K₃) three_ne_zero'
def etaRep3 (t : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  etaAdelicRep ℚ ℍ[ℚ] v₃ ((3 : ℚ) : K₃) three_ne_zero' 2 (((t : ℕ) : ℚ) : K₃)
theorem toMatrix_etaRep3 (t : Fin 3) :
    toMatrix ℚ ℍ[ℚ] v₃ (etaRep3 t) = !![((3 : ℚ) : K₃), 0; 9 * (((t : ℕ) : ℚ) : K₃), 1] := by
  sorry
theorem bijOn_etaRep3 :
    Set.BijOn (Quotient.mk'' : Dfx ℚ ℍ[ℚ] → Quotient (QuotientGroup.rightRel U1_9))
      (Set.range etaRep3)
      ((Quotient.mk'' : Dfx ℚ ℍ[ℚ] → Quotient (QuotientGroup.rightRel U1_9)) ''
        (({eta3} : Set (Dfx ℚ ℍ[ℚ])) * (U1_9 : Set (Dfx ℚ ℍ[ℚ])))) := by
  sorry
theorem etaRep3_injective : Function.Injective etaRep3 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L20.2** `eta3`, `etaRep3`, `toMatrix_etaRep3`, `bijOn_etaRep3`, `etaRep3_injective` — [RM]
  §0.5.4 "`U₁(9) η_3 U₁(9) = ∐_{t ∈ {0,1,2}} U₁(9) · ι_3(((3 0), (9t 1)))` (Jacobs, Lemma 2.3)".
  L14.9 at `ϖ = 3`, `t = 2`, with L14.9's second statement for the lower hypothesis, L12.1 for
  `v(3)² = levelThreshold 2`, and L17.2. [SRC] `3_EtaDecomposition.bijOn_etaRep`. Attacks: [4] the
  representative matrix is `((3 0), (t·3² 1))`, equal to the roadmap's `((3 0), (9t 1))` ✓, and to
  [SRC] `toMatrix_etaRep` ✓ — so the factorisation table transfers verbatim. SURVIVED.

#### Mathlib lemmas needed

`toMatrix_etaRep`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.4 (module docstring: §0.5.4).
- Literature: the quotations of the module docstring of `Hamilton/EtaDecomposition.lean`.
- [SRC] (proof idea only, never imported): `3_EtaDecomposition.bijOn_etaRep`, `toMatrix_etaRep`.

#### Generality decision

Binding decisions of `plan.md`: (8) **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`** (10) **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.**

#### Progress

- 2026-09-30: DONE. `bijOn_etaRep3` = `bijOn_etaAdelicRep` at `ϖ = 3`, `t = 2`, `r t = t`, with
  `v(3)² = levelThreshold 2` (`valued_pow_eq_levelThreshold`), the upper hypothesis unfolded from
  `U1Level` and `iwahoriOne_le_iwahori`, the lower one `unitAt_iwahoriPrincipal_le_U1Level` at the constant
  family `fun _ : Unit ↦ v₃`. `etaRep3_injective` from the `(1,0)` entry `9t` (valuations of `t − s`, no
  `CharZero` needed).

### [CLEANUP-31] `/cleanup` of `Hamilton/EtaDecomposition.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/EtaDecomposition.lean` · **Depends on**: [T077] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Sorry-free, standard axioms, 0 warnings, lines ≤ 100, `runLinter`
  passes; module docstring lists every main declaration.

### [T078] `hA`, `hB`, `hC` and 11 more

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [T077] · **Type**: proof · **Leaves**: L21.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def hA : ℍ[ℚ] := ⟨1, 1, -1, 0⟩
def hB : ℍ[ℚ] := ⟨-(1 / 2), 1 / 2, 3 / 2, 1 / 2⟩
def hC : ℍ[ℚ] := ⟨-(1 / 2), -(3 / 2), -(1 / 2), -(1 / 2)⟩
def third (h : ℍ[ℚ]) (hh : nrd h = 3) : (ℍ[ℚ])ˣ :=
  ⟨(3⁻¹ : ℚ) • h, star h, by sorry, by sorry⟩
def sigmaTable : Fin 3 → Fin 3 → Fin 3 := ![![2, 1, 1], ![0, 2, 2], ![1, 0, 0]]
theorem sigmaTable_ne (i t : Fin 3) : sigmaTable i t ≠ i := by
  sorry
def dTable : Fin 3 → Fin 3 → (ℍ[ℚ])ˣ :=
  ![![-third hA nrd_hA, third hC nrd_hC, third hB nrd_hB],
    ![third hA nrd_hA, third hC nrd_hC, third hB nrd_hB],
    ![third hA nrd_hA, -third hC nrd_hC, -third hB nrd_hB]]
theorem nrd_dTable (i t : Fin 3) : nrd ((dTable i t : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = 1 / 3 := by
  sorry
theorem hA_mem : hA ∈ hurwitzOrder := by
  sorry
theorem hB_mem : hB ∈ hurwitzOrder := by
  sorry
theorem hC_mem : hC ∈ hurwitzOrder := by
  sorry
theorem nrd_hA : nrd hA = 3 := by
  sorry
theorem nrd_hB : nrd hB = 3 := by
  sorry
theorem nrd_hC : nrd hC = 3 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L21.1** `hA`, `hB`, `hC`, their membership and norms, `third` (two fields), `sigmaTable`,
  `sigmaTable_ne`, `dTable`, `nrd_dTable` — [RM] §0.5.5 "`d(i, t) ∈ D^×` of reduced norm `1/3`
  (`± h / 3` for `h ∈ {1 + i − j, (−1 + i + 3j + k)/2, −(1 + 3i + j + k)/2}`),
  `σ = ((2, 1, 1), (0, 2, 2), (1, 0, 0))`". `ext <;> norm_num`; `decide`. [SRC]
  `5_Factorisations.dA`, `.dB`, `.dC`, `.sigmaTable`, `.dTable`. Attacks: [1] `nrd hB = ¼ + ¼ + 9/4 +
  ¼ = 3` ✓, `nrd hC = ¼ + 9/4 + ¼ + ¼ = 3` ✓. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.5 (module docstring: §0.5.5).
- Literature: the quotations of the module docstring of `Hamilton/Factorisations.lean`.
- [SRC] (proof idea only, never imported): `5_Factorisations.dA`.

#### Generality decision

Binding decisions of `plan.md`: (12) **One conclusion per declaration.**

#### Progress

- 2026-09-30: DONE (Hamilton/Factorisations.lean T078–T081 in one pass). `nrd` of the explicit
  quaternions by `nrd_apply` + `norm_num`; `third`'s unit laws via `Quaternion.self_mul_star` and
  `nrd_eq_normSq`; `nrd_dTable` from `nrd_third`/`nrd_neg_third` by `fin_cases` + `exacts`.

### [T079] `uCand`, `uCand_away`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [T078] · **Type**: proof · **Leaves**: L21.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
def uCand (i t : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  (unitsIncl ℚ ℍ[ℚ] (dTable i t) * classRep (sigmaTable i t))⁻¹ * (classRep i * (etaRep3 t)⁻¹)
theorem uCand_away (i t : Fin 3) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃) :
    toLocalUnits ℚ ℍ[ℚ] w (uCand i t) ∈
      localUnits hurwitzBasis isOrderBasis_hurwitzBasis w := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L21.2** `uCand`, `uCand_away` — away from `3`: `d⁻¹ = ± h̄` is a Hurwitz quaternion, and
  `d = ± h/3` is integral where `3` is a unit; the other factors have trivial components. [SRC]
  `5_Factorisations.uCand_away`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.5.5).
- Literature: the quotations of the module docstring of `Hamilton/Factorisations.lean`.
- [SRC] (proof idea only, never imported): `5_Factorisations.uCand_away`.

#### Generality decision

Binding decisions of `plan.md`: (12) **One conclusion per declaration.**

#### Progress

- 2026-09-30: DONE. Away from `3` everything but `d(i,t)` is trivial
  (`toLocalUnits_localIncl_of_ne`); `d = ±h/3` is integral as `h ⊗ 3⁻¹` with `3⁻¹ ∈ 𝒪_w` (`3` a unit at
  `w ≠ v₃`, via `primesEquiv` and `valued_intCast_eq_one` at the prime of `w`), `d⁻¹ = ±h̄` is Hurwitz
  (`star` preserves the Hurwitz order).

### [T080] `toGL_uCand_mem`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [T079] · **Type**: proof · **Leaves**: L21.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem toGL_uCand_mem (i t : Fin 3) :
    toGL ℚ ℍ[ℚ] v₃ (uCand i t) ∈ LocalLevel.iwahoriOne K₃ (levelThreshold 2) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L21.3** `toGL_uCand_mem` — at `3`: nine explicit matrices `c_σ⁻¹ θ₃(d)⁻¹ c_i x_t⁻¹`, each
  integral with unit determinant, `9 ∣ c` and `d ≡ 1 mod 9`, checked with `ν₃ ≡ 22 mod 27` (L16.3).
  [SRC] `5_Factorisations.toMatrix_uCand₀₀ … ₂₂`, `sigma1_uCand…`. **The longest leaf of the board**:
  in [SRC] about `700` lines; its size is a property of the computation, not of the design. Attacks:
  [4] the conventions (`θ₃`, `c_i`, `x_t`, `d(i,t)`, `σ`) were compared with [SRC] one by one (L15.1,
  L19.1, L20.2, L21.1): identical, so the certificate is the one already verified there. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: §0.5.5).
- Literature: the quotations of the module docstring of `Hamilton/Factorisations.lean`.
- [SRC] (proof idea only, never imported): `5_Factorisations.toMatrix_uCand₀₀ … ₂₂`.

#### Generality decision

Binding decisions of `plan.md`: (12) **One conclusion per declaration.**

#### Progress

- 2026-09-30: DONE — with ONE generic certificate instead of nine matrix computations (legacy
  ~700 lines). `θ₃(u(i,t)) = D(x_σ, y_σ)⁻¹ S(d⁻¹) D(xᵢ, yᵢ) E_t⁻¹`, and for `2d⁻¹ = (A, B, C, E)` the entries
  are `(X + Y ν₃)/M` with `X, Y, M` explicit integer polynomials in `(A, B, C, E, xσ, yσ, xᵢ, yᵢ, t)`;
  `v((X + Yν₃)/(3^k m')) ≤ v(3)^e` as soon as `3^(k+e) ∣ X + 22Y` (`ν₃ ≡ 22 mod 27`). Membership in
  `Iw₁(9)` then reduces to three integer divisibilities (by `3`, `27`, `9`) per `(i, t)`, closed by
  `decide`; `v(det) = 1` from multiplicativity (`det ∘ θ₃ = nrd` by `det_map_eq_nrd`, `nrd d = 1/3`,
  `det x_t = 3`). The certificate was recomputed by an exact-arithmetic script and agrees with [SRC].
  `ring` needs `CharZero K₃`: supplied locally by `algebraRat.charZero` (a global instance would loop
  with `DivisionRing.toRatAlgebra`).

### [CLEANUP-32] `/cleanup` of `Hamilton/Factorisations.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [T080] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. Only the declarations proved so far are in scope.

#### Progress

- 2026-09-30: DONE inline together with CLEANUP-33 (file finished in one pass).

### [T081] `uCand_mem`, `factorisation`

- **Status**: done   (finished 2026-09-30) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [CLEANUP-32] · **Type**: proof · **Leaves**: L21.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order:

```lean
theorem uCand_mem (i t : Fin 3) : uCand i t ∈ U1_9 := by
  sorry
theorem factorisation (i t : Fin 3) :
    classRep i * (etaRep3 t)⁻¹ =
      unitsIncl ℚ ℍ[ℚ] (dTable i t) * classRep (sigmaTable i t) * uCand i t := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L21.4** `uCand_mem`, `factorisation` — [RM] §0.5.5 "The nine factorisations
  `c_i · x_t^{−1} = d(i, t) · c_{σ(i,t)} · u(i, t)` […] `u(i, t) ∈ U₁(9)` (Jacobs, Lemmas 2.4–2.5 and
  §B.1)". L17.3's `mem_U1_9_of_toGL` with L21.2, L21.3; the equation holds by the definition of
  `uCand`. SURVIVED.

#### Mathlib lemmas needed

None beyond `simp`/`ring`/`norm_num`-level library facts.

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] §0.5.5 (module docstring: §0.5.5).
- Literature: the quotations of the module docstring of `Hamilton/Factorisations.lean`.

#### Generality decision

Binding decisions of `plan.md`: (12) **One conclusion per declaration.**

#### Progress

- 2026-09-30: DONE. `uCand_mem` = `mem_U1_9_of_toGL` (T066) with T079/T080; `factorisation` by
  `mul_inv_cancel_left` from the definition of `uCand`.

### [CLEANUP-33] `/cleanup` of `Hamilton/Factorisations.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Hamilton/Factorisations.lean` · **Depends on**: [T081] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Sorry-free, standard axioms (13 declarations checked), 0 warnings,
  lines ≤ 100, `runLinter` passes; module docstring lists every main declaration and records that the
  nine computations are one certificate.

### [T082] acceptance examples

- **Status**: done   (finished 2026-09-30) · **File**: `Examples.lean` · **Depends on**: [T081], [T036] · **Type**: examples · **Leaves**: L22.1

#### Statement

Every `example` of `Examples.lean` as it stands in the skeleton; one carries a `sorry` (the three
right cosets of `Iw(3²) η Iw(3²)`), the others are already closed by the named theorems.

#### Proof sketch

Substrate: `decomposition.md`, "§0.5 The running example", *Plain-English proof
substrate*. Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L22.1** the `example`s — [RM] Layer 0, Examples: "the Hurwitz units […]; `U₀(1)` and `U₁(9)` are
  compact open; `D^× \ D_f^× / U₀(1)` is a point and `D^× \ D_f^× / U₁(9)` has three points;
  `Iw(3^2) η Iw(3^2)` splits into three right cosets; `diag(3, 1) ∈ M_t` is not a unit of `M_t`;
  `|nrd(γ)|_f = nrd(γ)^{−1}` for `γ ∈ ℍ[ℚ]^×`". All are one-line instances except the count of the
  cosets of `Iw(3²) η Iw(3²)`, which is `Set.ncard_image_of_injOn` on L11.13's `BijOn` with
  `Fin 3`. SURVIVED.

#### Mathlib lemmas needed

`Set.ncard_image_of_injOn`

Names were checked by elaboration during planning unless the sketch flags them *for the ticket*.

#### Sources

- [RM] see module docstring (module docstring: Layer 0, Examples).
- Literature: the quotations of the module docstring of `Examples.lean`.

#### Generality decision

None; the examples are instances.

#### Progress

- 2026-09-30: DONE. The local three-coset example = `bijOn_etaRep` (Level/Local) at `U = Iw(3²)`:
  `ncard` of the image = `ncard` of the range of the representatives, injective since `etaRep3` is.

### [CLEANUP-34] `/cleanup` of `Examples.lean` (final for the file)

- **Status**: done   (finished 2026-10-01) · **File**: `Examples.lean` · **Depends on**: [T082] · **Type**: cleanup

Run `/cleanup` inline on the file: style audit, golf, Mathlib replacements, docstrings, line length by
codepoints, `lake exe runLinter` on the module, removal of unused instance hypotheses with their callers
updated. The file must be sorry-free and the module docstring must list every main declaration.

#### Progress

- 2026-09-30: DONE inline. Builds with 0 warnings (`Set.ncard_image_of_injOn` → `InjOn.ncard_image`),
  `runLinter` passes.

### [CLEANUP-ALL-2] `/cleanup-all` before milestone M2

- **Status**: done   (finished 2026-10-01) · **Depends on**: [T082] and every cleanup ticket above · **Type**: cleanup

Project-wide pass over the whole of `PhD/TauCeti/Code/OverconvergentForms/`: naming consistency across files, duplicated helpers merged, import
minimisation (replace `import Mathlib` by the needed modules), `#lint` clean.

#### Progress

- 2026-10-01: DONE inline. Whole `OverconvergentForms/` tree: imports minimised in all 22 files
  (CLEANUP-ALL-1); duplicated helpers merged — `rightBasis_repr_toLocal` (private in `Adelic/Components`,
  public copy in `Adelic/IntegralAdeles`) now one public lemma in Components; Factorisations' private
  `star_mem_hurwitzOrder` replaced by `Quaternion.star_mem_hurwitzOrder`; `isUnit_two` (Setting) made
  public and reused, `sq_ν₃_add_one_sq` and `charZero_K₃` (with its no-global-instance warning) added
  to Setting and used by Level/ClassSet/EtaDecomposition/Factorisations, ClassSet's private
  `two_ne_zero₃`/`valued_nine_eq` removed in favour of `isUnit_two`/`valued_nine`. Naming checked: the
  only repeated names are the intended `Hamilton.U0`-family specialisations of `AdelicAlgebra`'s.
  Chain rebuilt, 0 errors, 0 warnings; `runLinter` passes on all 22 modules.

### [M2] Milestone: Layer 0 complete, chain root updated

- **Status**: done   (finished 2026-10-01) · **Depends on**: [CLEANUP-ALL-2] · **Type**: milestone

#### Statement

Add `import PhD.TauCeti.Code.OverconvergentForms.Examples` to `PhD/TauCeti.lean` (the only edit to the
chain root on this board; if the PFA or CO boards have added their imports, keep them). `lake build
PhD.TauCeti` succeeds sorry-free; `#print axioms` on `Hamilton.exists_factor`,
`Hamilton.isSection_classRep`, `Hamilton.stabilizer_classRep`, `Hamilton.bijOn_etaRep3`,
`Hamilton.factorisation` shows the standard axioms only; no file imports `PhD.Main.*`. Update the
provenance table of the roadmap README only if the user asks. Nothing is proved in this ticket.

#### Progress

- 2026-10-01: DONE. Chain root imports `OverconvergentForms.Examples` (the PFA/NewtonPolygons imports
  kept); `lake build PhD.TauCeti`: 3454 jobs, success, no `sorry`, 0 warnings. The five named results
  depend on `[propext, Classical.choice, Quot.sound]` only; no file imports `PhD.Main.*`. Recorded in
  `plan.md` (§ Milestones). Roadmap README provenance table NOT touched (only on the user's request).

### [CLEANUP-FINAL] `/cleanup-all`, final

- **Status**: done   (finished 2026-10-01) · **Depends on**: [M2] · **Type**: cleanup

Last project-wide pass after the milestone: docstrings against the roadmap clauses, Tau Ceti homes in
every module docstring, `#lint` clean, and the memory note of the board updated to COMPLETE.

#### Progress

- 2026-10-01: DONE inline. Every module docstring cites its roadmap clause and Tau Ceti home and lists
  its main declarations (Setting and Components completed after the merges); `runLinter` passes on all
  22 modules; `lake build PhD.TauCeti` succeeds with 0 warnings; memory note `tauceti-of-layer0-board`
  updated to COMPLETE. BOARD COMPLETE: 121/121.
