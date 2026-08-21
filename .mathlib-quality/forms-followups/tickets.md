# Ticket Board — forms-followups (`.mathlib-quality/forms-followups/`)

**BOARD PATH: `.mathlib-quality/forms-followups/`.**  Workers: `/beastmode` with this path.
**Status: BOARD COMPLETE 2026-08-19** (single beastmode run; the user ran the board as planned, so the
optional T004–T005 were executed too).  Item 2 was dropped at planning time (see plan.md).

Governing principles (inherited from forms-headline): **no duplicate code** — fork objects that the
general layer now provides are *replaced by* the general ones; every deletion/rename goes to
`.mathlib-quality/renames.jsonl`; `lia` → `omega`; never touch `PhD/PR'd/`.

Skeleton: every new theorem below exists as `:= by sorry` at the cited file (11 sorries); new
definitions have their real bodies.  `lake build PhD.QMF.Weight.Fredholm PhD.QMF.Weight.Quaternionic
PhD.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace` green (2026-08-19).

## Summary
- Total: 9 proof/def/refactor tickets (T001–T009; T004, T005 optional) + 13 cleanup tickets = 22
- Open: 0 | In Progress: 0 | Done: 22
- Planning defects met on the way: none at the statement level; `PhD.QMF.Finiteness` import needed in
  `Weight/Quaternionic.lean` (adelic topology source); linter cascades (omitting unused section variables
  propagates to consumers — fixed to the fixed point by a scripted loop; `lemma211_first'/second'` lost unused
  explicit hypotheses, call sites updated).
- Parallel capacity at start: 8 (T001 ∥ T007 ∥ T008 ∥ T009 ∥ CLEANUP-6…11)
- Milestone: T006 (eigenform criterion at general weight) — CLEANUP-ALL-1 precedes it.

## Dependency fronts
```
T001 ─► T002 ─► T003 ─► CLEANUP-1 (Compact.lean) , CLEANUP-2 (fork 3_ClassSet/6_Matrix/7_Fredholm)
T002 ─► CLEANUP-ALL-1 ─► T006 (MILESTONE) ─► CLEANUP-3 (Fredholm.lean)
T002 ─► T004 (opt) ─► T005 (opt) ─► CLEANUP-3
T007 ─► CLEANUP-4 (Weight/Quaternionic.lean, 1_Setting.lean)
T008, T009 ─► CLEANUP-5 (Forms.lean, Char.lean, Slash/Sigma0.lean)
CLEANUP-6 (BlockOp) ∥ CLEANUP-7 (2_U3Data) ∥ CLEANUP-8 (1_PadicAnalytic) ∥ CLEANUP-9 (1_SlopeTheorem) ∥ CLEANUP-10 (3_Slopes) ∥ CLEANUP-11 (U1_9)
everything ─► CLEANUP-FINAL
```

---

## Item 1 — bijectivity of `evalAtReps` at a neat level; fork dedup

### [T001] `ext_of_forall_rep`; `evalAtReps_injective` restated at any family meeting every double coset
- **Status**: done (2026-08-19, forms-followups beastmode) | **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry) + restatement

#### Statement
```lean
omit [Fintype ι] [DecidableEq ι] in
theorem ext_of_forall_rep (c : ι → G)
    (hc : Function.Surjective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    {φ ψ : Forms Γ θ κ U hU χ}
    (h : ∀ i, (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i)
      = (ψ : AutomorphicFunction G Γ c(ℕ, K)) (c i)) :
    φ = ψ := by sorry

-- REPLACES the current section-indexed `evalAtReps_injective` (Compact.lean:102; zero consumers):
theorem evalAtReps_injective (c : ι → G)
    (hc : Function.Surjective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)))) :
    Function.Injective (evalAtReps (Γ := Γ) θ κ U hU χ c) :=
  fun φ ψ h => ext_of_forall_rep θ κ U hU χ c hc fun i => by
    simpa only [blockProj_evalAtReps] using congrArg (cSpace.blockProj i) h
```

- **Progress**: DONE — `ext_of_forall_rep` by the fork's `calc` template (`DoubleCoset.rel_iff`/`Quotient.eq''`,
  `left_invt'`, `slash_apply_mul`); `evalAtReps_injective` restated at families (old section form deleted, zero
  consumers); `lake build PhD.QMF.Weight.Compact` green.
#### Proof sketch (`ext_of_forall_rep`; template `JacobsSlash.eval_classRep_injective`, 6_Matrix.lean:197–228, and `bijective_evalAtRepsSlash.1`, Slash/HeckeMatrix.lean:181–190)
1. `letI := kappaLevelSlashActionTwisted θ κ χ; haveI := kappaLevelSMulSlashClassTwisted θ κ χ`.
2. `refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)`.
3. `obtain ⟨i, hi⟩ := hc (Quotient.mk'' g)`; `obtain ⟨a, ha, b, hb, hg⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)` — `hg : g = a * c i * b` with `a ∈ Γ`, `b ∈ U`.
4. `rw [hg, mul_assoc, (φ : AF).left_invt' ha, (ψ : AF).left_invt' ha, AutomorphicFunction.slash_apply_mul K hU φ.2 ⟨b, hb⟩, AutomorphicFunction.slash_apply_mul K hU ψ.2 ⟨b, hb⟩, h i]` (the `slash_apply_mul` shape is `φ (g * u) = φ g ∣ₛ ⟨u, hU u.2⟩`; use `show`/`exact congrArg` if the `rw` needs the coercions spelled out — see the fork template's `calc`).
5. Delete the old `evalAtReps_injective` (no consumers); record in renames.jsonl (`"old": "QMF.Weight.evalAtReps_injective (section form)", "new": "QMF.Weight.evalAtReps_injective (family form)"`).  Update the Compact.lean header bullet.

#### Mathlib lemmas needed
- `DoubleCoset.rel_iff : (DoubleCoset.setoid ↑H ↑K) x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b` (verified by `#check`).
- `Quotient.eq'' : Quotient.mk'' a = Quotient.mk'' b ↔ s a b` (mathlib).
- Project: `AutomorphicFunction.left_invt'`, `AutomorphicFunction.slash_apply_mul`, `Subtype.ext`, `AutomorphicFunction.ext`, `blockProj_evalAtReps`.

#### Sources
- [Buz07] Buzzard, *Eigenvarieties*, §9 p. 69: "f ∈ L(U,A) is determined by f(τ_λ)".  [Jac03] Jacobs, Lemma 1.31 p. 19.

#### Generality decision
- `ι` arbitrary (no `Fintype`), `c` only needs to meet every double coset (surjectivity of `Quotient.mk'' ∘ c`); `χ` general twist; stated for the abstract `(G, Γ, θ)` of `Forms`.

---

### [T002] `bijective_evalAtReps`, `bijective_evalAtReps_of_stabilizer_eq_bot`, `formsModelEquiv`
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE exactly per sketch (`Equiv.ofBijective` section, `bijective_evalAtRepsSlash.2` at the
  tuple `⟨blockProj (e.symm q) F, hstab⟩`, block-ext); `_of_stabilizer_eq_bot` via `Subgroup.mem_bot`+`kappaSlash_one`.
  Axioms standard; Compact.lean 0 sorries; runLinter zero. **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: T001 | **Parallel**: no | **Type**: theorem (2 sorries) + def (in place)

#### Statement
```lean
theorem bijective_evalAtReps (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a) :
    Function.Bijective (evalAtReps (Γ := Γ) θ κ U hU χ c) := by sorry

theorem bijective_evalAtReps_of_stabilizer_eq_bot (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    Function.Bijective (evalAtReps (Γ := Γ) θ κ U hU χ c) := by sorry

noncomputable def formsModelEquiv (c : ι → G) (hc : …) (hstab : …) :
    Forms Γ θ κ U hU χ ≃ₗ[K] c(ι × ℕ, K) :=
  LinearEquiv.ofBijective _ (bijective_evalAtReps θ κ U hU χ c hc hstab)   -- in place
```

#### Proof sketch (`bijective_evalAtReps`; template `JacobsSlash.bijective_evalU3`, 7_Fredholm.lean:75–103)
1. `letI`/`haveI` the twisted action and `SMulSlashClass` as in T001.  `refine ⟨evalAtReps_injective θ κ U hU χ c hc.2, fun F => ?_⟩`.
2. Section of the quotient from `hc`: `set e := Equiv.ofBijective _ hc`; `σ : Quotient → G := fun q => c (e.symm q)`; `hσ : ∀ q, Quotient.mk'' (σ q) = q := fun q => e.apply_symm_apply q` (unfold `e` — `Equiv.ofBijective_apply`).
3. Invariant tuple: for each `q`, `⟨cSpace.blockProj (e.symm q) F, fun w => ?_⟩ : slashFixedPointsOfLE (U := stabilizerAtSlash Γ U (σ q)) K c(ℕ,K) _`; the goal `blockProj … ∣ₛ ⟨w, _⟩ = blockProj …` is, after `show`/`kappaLevelSlashActionTwisted_slash`, exactly `hstab (e.symm q) w w.2 _` (the slash of the pulled-back twisted action at `⟨w, stabilizerAtSlash_le hU Γ _ w.2⟩` unfolds to `χ ⟨θ w, _⟩ • κ.kappaSlash ⟨θ w, _⟩ a` by `rfl`; membership proofs are irrelevant).
4. `obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtRepsSlash (A := c(ℕ, K)) K hU σ hσ).2 (that tuple)`; `hφ : evalAtRepsSlash K hU σ φ = tuple`, so `φ (σ q) = cSpace.blockProj (e.symm q) F` (`congrArg Subtype.val (congrFun hφ q)`).
5. `refine ⟨φ, DFunLike.ext _ _ fun ⟨i, n⟩ => ?_⟩`; `have h3 := (step 4 at q := e i)`; `rw [show σ (e i) = c i by simp [σ, e]]` hmm — `e.symm (e i) = i` by `Equiv.symm_apply_apply`; conclude with `congrArg (fun g => g n) ((blockProj_evalAtReps θ κ U hU χ c φ i).trans h3)` and `cSpace.blockProj_apply`.
6. `_of_stabilizer_eq_bot`: `bijective_evalAtReps … c hc fun i w hw a => ?_`; `have : w = 1 := Subgroup.mem_bot.mp (hstab i ▸ hw)`; `subst this; simp [AnalyticWeight.kappaSlash_one]` (`θ 1 = 1` by `map_one`, `χ 1 = 1`, `one_smul`; the subtype `⟨θ 1, _⟩ = 1` by `Subtype.ext (map_one θ)`).

#### Mathlib lemmas needed
- `Equiv.ofBijective`, `Equiv.ofBijective_apply`, `Equiv.apply_symm_apply`, `Equiv.symm_apply_apply`, `Subgroup.mem_bot`, `map_one`, `one_smul`, `DFunLike.ext`, `LinearEquiv.ofBijective`.
- Project: `AutomorphicFunction.bijective_evalAtRepsSlash` (Slash/HeckeMatrix.lean:181), `evalAtRepsSlash` (:113), `AutomorphicFunction.mem_stabilizerAtSlash_iff`, `stabilizerAtSlash_le`, `cSpace.blockProj_apply`, `blockProj_evalAtReps`, `kappaLevelSlashActionTwisted_slash`, `AnalyticWeight.kappaSlash_one`.

#### Sources
- [Buz07] §9 p. 69 (isomorphism `L(U,A) → ⊕ A^{Γ_λ}`; p. 68 definition of `Γ_λ`); [Jac03] Lemma 1.31 p. 19, Lemma 2.2 (`Γ_i = {1}`), (2.1.1).

#### Generality decision
- "Stabilisers act trivially" (Buzzard's actual condition) as the main hypothesis; `= ⊥` as a corollary.  `hc` bijective (a complete set of representatives).  `χ` general.

---

### [T003] Fork dedup: `classRep_bijective`; `eval_classRep_injective`/`bijective_evalU3` as instances; delete `exists_classRep_section`
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE — `classRep_bijective` (3_ClassSet; `Quotient.inductionOn'` + `exists_classRep_factorisation`,
  `classRep_index_unique`), `eval_classRep_injective`/`bijective_evalU3` one-liners, `exists_classRep_section` deleted
  (renames.jsonl), headers/PROGRESS.md updated; fork rebuilt through 9_EigenvaluesU3/7_DiamondHecke; linter zero on
  3_ClassSet/6_Matrix/7_Fredholm; axioms standard (headline `exists_eigenvalue_U3_in_W_eigenspace` unchanged). **Files**: PhD/JacobsSlash/U3/3_ClassSet.lean, 6_Matrix.lean, 7_Fredholm.lean | **Depends on**: T002 | **Parallel**: no | **Type**: refactor (+1 small lemma)

#### Statement
```lean
-- 3_ClassSet.lean (after classRep_index_unique):
theorem classRep_bijective (hcn : HClassNumberOne) :
    Function.Bijective (fun i : Fin 3 =>
      (Quotient.mk'' (classRep i) : DoubleCoset.Quotient
        ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D)) (U1_9 : Set (Dfx ℚ D)))) := by sorry
-- 6_Matrix.lean: eval_classRep_injective t ht hcn φ ψ h :=
--   Weight.ext_of_forall_rep (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1
--     classRep (classRep_bijective hcn).2 h
-- 7_Fredholm.lean: bijective_evalU3 t ht hcn :=
--   Weight.bijective_evalAtReps_of_stabilizer_eq_bot (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
--     U1_9_subset_levelMonoid1₃ 1 classRep (classRep_bijective hcn) stabilizerAt_classRep
-- kappaFormsModelEquiv unchanged (LinearEquiv.ofBijective); DELETE exists_classRep_section (3_ClassSet.lean:1335).
```

#### Proof sketch
1. `classRep_bijective`: `refine ⟨fun i j hij => ?_, fun q => ?_⟩`.  Injective: `obtain ⟨d, hd, w, hw, h⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hij)` gives `classRep j = d * classRep i * w`; `exact (classRep_index_unique hd hw h).symm`.  Surjective: `induction q using Quotient.inductionOn' with | h g => ?_`; `obtain ⟨i, d, hd, w, hw, rfl⟩ := exists_classRep_factorisation hcn g`; `exact ⟨i, Quotient.eq''.mpr (DoubleCoset.rel_iff.mpr ⟨d, hd, w, hw, rfl⟩)⟩`.  (If `exists_classRep_section`'s proof has reusable `key` lemmas, inline them here; then delete it.)
2. Replace the bodies of `eval_classRep_injective` and `bijective_evalU3` by the one-liners above (`letI` no longer needed); keep `eval_classRep_injective'` (documents that `hClassNumberOne` discharges the hypothesis).
3. Delete `exists_classRep_section`; grep for consumers first (only `bijective_evalU3` today); renames.jsonl; update `PROGRESS.md` (module map row for 3_ClassSet/7_Fredholm) and the `6_Matrix`/`7_Fredholm` headers.
4. Rebuild `PhD.JacobsSlash.U3.«9_EigenvaluesU3»`; `runLinter` the three files.

#### Sources
- [Jac03] Lemma 2.2 ("Γ_i = {1} for all i"), Theorem 2.1 (class number one), (2.1.1).

#### Generality decision
- Fork-specific by nature; the only new lemma is the bijectivity of the thesis's three representatives.

---

### [CLEANUP-1] /cleanup PhD/QMF/Weight/Compact.lean (final)
- **Status**: done (2026-08-19, inline mode: header updated, linter zero) | **Depends on**: T002 | **Type**: cleanup.  Header "Main declarations" gains the four new names; `runLinter PhD.QMF.Weight.Compact`.

### [CLEANUP-2] /cleanup the fork files touched by T003 (3_ClassSet, 6_Matrix, 7_Fredholm)
- **Status**: done (2026-08-19, inline: headers updated, linter zero) | **Depends on**: T003 | **Type**: cleanup.  Headers/docstrings no longer mention `exists_classRep_section`; `runLinter`.

---

## Item 3 — the Fredholm determinant of `[UηU]` on `S_κ(U)`

### [CLEANUP-ALL-1] /cleanup-all on the item-1 surface (pre-milestone)
- **Status**: done (2026-08-19: Compact.lean + fork files linter zero, builds green, sorry census 0) | **Depends on**: CLEANUP-1, CLEANUP-2 | **Type**: cleanup-all.

### [T006] `heckeCharPowerSeries` + `evalT_heckeCharPowerSeries_eq_zero_iff` — **MILESTONE**; fork `charPowerSeriesU3` as instance
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE per sketch (Riesz criterion + `bijective_evalAtReps` + `evalAtReps_heckeOperator`, ~15 lines);
  fork `charPowerSeriesU3` is an abbrev of `heckeCharPowerSeries` (7_Fredholm imports Weight.Fredholm; downstream
  `charPowerSeriesU3_eq_U3MatrixOp`/`map_charPowerSeriesU3`/9_Eigenvalues unchanged, rebuilt green); axioms
  standard; linter zero on Weight/Fredholm + U3/7_Fredholm.  **MILESTONE: eigenforms of [UηU] on S_κ(U) are the
  reciprocal roots of det(1 − T·[UηU]) at every analytic weight.** **File**: PhD/QMF/Weight/Fredholm.lean (+ fork U3/7_Fredholm.lean) | **Depends on**: CLEANUP-ALL-1 (T002) | **Parallel**: no | **Type**: def (in place) + theorem (1 sorry) + fork abbrev

#### Statement
```lean
noncomputable def heckeCharPowerSeries (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) : PowerSeries K :=
  charPowerSeries (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)          -- in place

theorem evalT_heckeCharPowerSeries_eq_zero_iff (c : ι → G) (hc : …Bijective…) (hstab : …acts trivially…)
    {η : G} (hη : η ∈ levelMonoidOf θ S) (h : …finite…)
    (vRep : T → G) (hvΔ) (hv : Set.BijOn …) (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖(θ η).det‖ ≤ σ) {a : K} (ha0 : a ≠ 0) :
    PowerSeries.evalT a (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u) = 0 ↔
      ∃ φ : Forms Γ θ κ U hU χ, φ ≠ 0 ∧ heckeOperator θ κ U hU hη h φ = a⁻¹ • φ := by sorry
-- (full signature in the skeleton file)

-- fork, 7_Fredholm.lean:
noncomputable abbrev charPowerSeriesU3 (t : K₃) (ht : ‖t‖ < 1) : PowerSeries K₃ :=
  Weight.heckeCharPowerSeries (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1
    etaRep etaRep_mem_levelMonoid1₃ sigmaTable uTable     -- `rfl` with the current body
```

#### Proof sketch
1. `have hcomp := isCompactoid_heckeBlockOp θ κ U hU χ hρσ hσ hdet hvΔ hv idx u`; `have hbij := bijective_evalAtReps θ κ U hU χ c hc hstab`; `have htr := fun φ => evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ` (`evalAtReps c ([UηU] φ) = heckeBlockOp (evalAtReps c φ)`).
2. `rw [heckeCharPowerSeries, evalT_charPowerSeries_eq_zero_iff _ hcomp ha0]`.
3. (→) `rintro ⟨x, hx0, hx⟩; obtain ⟨φ, rfl⟩ := hbij.2 x`; `refine ⟨φ, fun h0 => hx0 (by simp [h0]), hbij.1 ?_⟩`; `rw [htr, map_smul, hx]`.
4. (←) `rintro ⟨φ, hφ0, hφ⟩; refine ⟨evalAtReps θ κ U hU χ c φ, fun h0 => hφ0 (hbij.1 (by simpa using h0)), ?_⟩`; `rw [← htr, hφ, map_smul]`.
5. Fork: change `charPowerSeriesU3`'s body to the abbrev above (`charPowerSeriesU3_eq_U3MatrixOp`, `map_charPowerSeriesU3` should still elaborate; if a `rw [charPowerSeriesU3]` breaks, use `show`/`unfold Weight.heckeCharPowerSeries`).  renames.jsonl; PROGRESS.md; README §1/§5.6.

#### Mathlib lemmas needed
- `map_smul`, `LinearMap.map_zero`, `Function.Bijective` projections; project `evalT_charPowerSeries_eq_zero_iff` (Riesz.lean:2233), `isCompactoid_heckeBlockOp`, `evalAtReps_heckeOperator`, `bijective_evalAtReps`.

#### Sources
- [Ser62] §7 Props 11–12 (as formalised); [Jac03] p. 21 (matrix of `U_p` w.r.t. the topological basis), Lemma 2.7; [Buz07] §13 p. 79.

#### Generality decision
- Stated for the abstract `(G, Γ, θ)`, general `χ`, any `η` of `U_ϖ` type (`‖det θ(η)‖ ≤ σ`, `ρ ≤ σ < 1`), any neat family `c`.  The determinant is *defined* at certificates (Jacobs's convention); its intrinsic nature is T005 (optional).

---

### [T004] (OPTIONAL) `evalAtReps_eq_transitionOp` — the transition operator between two families of representatives
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE — block-wise via `mem_forms_iff`/`left_invt'` + `cSpace.sum_apply`/`blockIncl_apply`/`sum_ite_eq`;
  axioms standard. **File**: PhD/QMF/Weight/Fredholm.lean | **Depends on**: T002 | **Parallel**: yes | **Type**: def (in place) + theorem (1 sorry)

#### Statement
```lean
noncomputable def transitionOp (idx : ι' → ι) (u : ι' → U) : c(ι × ℕ, K) →L[K] c(ι' × ℕ, K) :=
  ∑ i' : ι', (cSpace.blockIncl i').comp
    ((((χ (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩) : Kˣ) : K)
        • κ.kappaSlash (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩)).comp
      (cSpace.blockProj (idx i')))                                   -- in place

theorem evalAtReps_eq_transitionOp (c : ι → G) (c' : ι' → G) (idx : ι' → ι) (d : ι' → G)
    (hd : ∀ i', d i' ∈ Γ) (u : ι' → U)
    (hfact : ∀ i', c' i' = d i' * c (idx i') * (u i' : G)) (φ : Forms Γ θ κ U hU χ) :
    evalAtReps θ κ U hU χ c' φ = transitionOp θ κ U hU χ idx u (evalAtReps θ κ U hU χ c φ) := by sorry
```

#### Proof sketch (template `evalAtReps_heckeOperator`, Compact.lean:172–190)
1. `refine DFunLike.ext _ _ fun ⟨i', n⟩ => ?_` or block-wise: show `cSpace.blockProj i' (LHS) = cSpace.blockProj i' (RHS)` for all `i'` then conclude pointwise via `cSpace.blockProj_apply`.
2. LHS block: `blockProj_evalAtReps` → `φ (c' i')`; `rw [hfact i', mul_assoc, (φ : AF).left_invt' (hd i')]`, then `(mem_forms_iff θ κ hU χ).mp φ.2 (u i') (c (idx i'))` → `χ ⟨θ (u i'), _⟩ • κ.kappaSlash ⟨θ (u i'), _⟩ (φ (c (idx i')))`.
3. RHS block: `simp only [transitionOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum, cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true, ContinuousLinearMap.smul_apply, blockProj_evalAtReps]` — the single surviving term is the same expression (`Units.smul_def` to align `Kˣ`- vs `K`-scalars).

#### Sources
- [Jac03] p. 21 (the factorisation `c_i v_t⁻¹ = d c(i,t) u(i,t)` device).

#### Generality decision
- Heterogeneous index types `ι`, `ι'`; written as an explicit sum of `blockIncl ∘ op ∘ blockProj` rather than generalising `TateFredholm.blockOp` to rectangular shape (no churn in BlockOp.lean).

---

### [T005] (OPTIONAL) `heckeCharPowerSeries_eq_of_reps` — independence from representatives and certificates
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE exactly per sketch: transition certificates both ways by `choose` from `hc`/`hc'`, the two
  transition operators are mutually inverse by surjectivity of `evalAtReps`, `ContinuousLinearEquiv` via
  `LinearEquiv.ofLinear` (no OMT/NormedSpace needed), block operators conjugate via the two transports, then
  `charPowerSeries_conj`.  Axioms standard; Fredholm.lean 0 sorries; linter zero.  **The determinant
  `det(1 − T·[UηU])` on `S_κ(U)` is intrinsic at every neat level.** **File**: PhD/QMF/Weight/Fredholm.lean | **Depends on**: T002, T004 | **Parallel**: no | **Type**: theorem (1 sorry)

#### Statement
Full signature in the skeleton (two neat families `c`, `c'`, certificates `(vRep, idx, d, u)` and `(vRep', idx', d', u')` for the same `η`, `hcomp : IsCompactoid (heckeBlockOp … vRep hvΔ idx u)`): `heckeCharPowerSeries … vRep' hvΔ' idx' u' = heckeCharPowerSeries … vRep hvΔ idx u`.

#### Proof sketch
1. Transition certificates from `hc`, `hc'` (no extra hypotheses): `e := Equiv.ofBijective _ hc`, `e' := …hc'`; for `i'`, `mk'' (c' i') = mk'' (c (e.symm (mk'' (c' i'))))` hence by `DoubleCoset.rel_iff` `∃ a ∈ Γ, ∃ b ∈ U, c' i' = a * c (…) * b`; `choose` `idx₁ d₁ hd₁ u₁ hfact₁`; symmetrically `idx₂ d₂ hd₂ u₂ hfact₂` with `c i = d₂ i * c' (idx₂ i) * u₂ i`.
2. `T₁ := transitionOp … idx₁ u₁`, `T₂ := transitionOp … idx₂ u₂`; `evalAtReps c' φ = T₁ (evalAtReps c φ)` and `evalAtReps c φ = T₂ (evalAtReps c' φ)` (T004).
3. `T₂ ∘ T₁ = id`: `ext x`; `obtain ⟨φ, rfl⟩ := (bijective_evalAtReps … c hc hstab).2 x`; rewrite with step 2 twice.  Same for `T₁ ∘ T₂` via `c'`.  Build `E : c(ι×ℕ,K) ≃L[K] c(ι'×ℕ,K) := { LinearEquiv.ofLinear (T₁ : _ →ₗ[K] _) T₂ h₁ h₂ with continuous_toFun := T₁.continuous, continuous_invFun := T₂.continuous }`.
4. Conjugation: `heckeBlockOp' = E ∘ heckeBlockOp ∘ E.symm`: `ext y`; `obtain ⟨φ, rfl⟩ := (bijective_evalAtReps … c' hc' hstab').2 y`; `evalAtReps_heckeOperator` at `c'` and at `c`, step 2.
5. `rw [heckeCharPowerSeries, heckeCharPowerSeries, this]; exact charPowerSeries_conj E _ hcomp` (`TateFredholm.charPowerSeries_conj`, Fredholm.lean:953).

#### Mathlib lemmas needed
- `Equiv.ofBijective`, `DoubleCoset.rel_iff`, `Quotient.eq''`, `Classical.choose`/`choose` tactic, `LinearEquiv.ofLinear`, `ContinuousLinearEquiv.mk`, `ContinuousLinearMap.continuous`, `ContinuousLinearMap.ext`.

#### Sources
- [Buz07] Cor 2.6 p. 14 (basis independence of `det(1 − Xφ)`).

#### Generality decision
- Both families neat (needed: the block operators are conjugate on the whole model only then); compactoidness of one block operator assumed (it is what `charPowerSeries_conj` needs; discharged by `isCompactoid_heckeBlockOp` at the call site).  Non-neat levels (Buzzard's (Pr) route) out of scope.

### [CLEANUP-3] /cleanup PhD/QMF/Weight/Fredholm.lean (final)
- **Status**: done (2026-08-19, inline: header de-skeletonised, linter zero) | **Depends on**: T006 (and T004, T005 if kept) | **Type**: cleanup.  If T004/T005 are struck, delete `transitionOp`, `evalAtReps_eq_transitionOp`, `heckeCharPowerSeries_eq_of_reps` from the skeleton (renames.jsonl) and trim the header.

---

## Item 4 — `S^D_κ(U)` and `U_ϖ` for a quaternion algebra

### [T007] `FormsQ`, `heckeUpiQ`, `U_ϖ` compact at every weight, Hecke finiteness at compact open level; fork instance swap
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE — four one-liners as sketched (`toMatrix_etaAdelic'` at `γ = ofAdd (-1)`, `Sigma0'.eta`,
  `det_fin_two_of`); `PhD.QMF.Finiteness` import is required (it is what provides the adelic topology /
  `TensorProduct.RightActions`); fork: hand-made `K₃` instance deleted (ForMathlib instance found through the
  abbrev, `noncomputable example` documents it), `kappaForms := FormsQ …`, `heckeU3 := heckeUpiQ … pi3 …`
  (both `rfl`-level; 6_Matrix imports Weight.Quaternionic); whole fork rebuilt green; axioms standard; linter
  zero on Quaternionic/6_Matrix/1_Setting. **Files**: PhD/QMF/Weight/Quaternionic.lean (+ PhD/ForMathlib/…/FinitePlace.lean DONE; fork U3/1_Setting.lean, 6_Matrix.lean) | **Depends on**: none | **Parallel**: yes | **Type**: defs (in place) + 4 theorems (4 sorries) + refactor

#### Statement
```lean
-- Quaternionic.lean (skeleton, full signatures there):
theorem etaAdelic'_mem_levelMonoidOf_sigma0' (γ) (hγ : γ < 1) (ϖ) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    etaAdelic' F D v ϖ hϖ0 ∈ Weight.levelMonoidOf (toMatrix F D v) (Sigma0' (v.adicCompletion F) γ hγ)
theorem norm_det_toMatrix_etaAdelic' (ϖ) (hϖ) (hϖ0) : ‖(toMatrix F D v (etaAdelic' F D v ϖ hϖ0)).det‖ = ‖ϖ‖
theorem isCompactoid_heckeBlockOp_etaAdelic' … (hρ : ρ ≤ ‖ϖ‖) (hϖ1 : ‖ϖ‖ < 1) … :
    IsCompactoid (Weight.heckeBlockOp (toMatrix F D v) κ U hU χ vRep hvΔ idx u)
theorem finite_image_etaAdelic'_of_isOpen_of_isCompact (U) (hUo : IsOpen ↑U) (hUc : IsCompact ↑U) (ϖ) (hϖ0) :
    ((Quotient.mk'' : Dfx F D → RightCosets U) '' ({etaAdelic' F D v ϖ hϖ0} * ↑U)).Finite
-- fork: delete `instance : NontriviallyNormedField K₃` (1_Setting.lean:143), import the ForMathlib file;
--   kappaForms t ht := FormsQ ℚ D v₃ (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ ;
--   heckeU3 t ht := heckeUpiQ ℚ D v₃ (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ pi3 pi3_ne_zero
--                     eta3_mem_levelMonoid1₃ finite_image_eta3   (if `eta3` unfolds to `etaAdelic' … pi3 _`; else leave)
```

#### Proof sketch
1. `etaAdelic'_mem_levelMonoidOf_sigma0'`: `exact etaAdelic'_mem_levelMonoid' F D v γ hγ ϖ hϖ hϖ0` (`levelMonoidOf θ (Sigma0' …)` and `levelMonoid' F D v γ hγ` are both `Submonoid.comap (toMatrix F D v) (Sigma0' …)` — `rfl`).
2. `norm_det_toMatrix_etaAdelic'`: pick `γ := (Multiplicative.ofAdd (-1 : ℤ) : WithZero (Multiplicative ℤ))`, `hγ` by `decide`/`WithZero.coe_lt_one`; `rw [toMatrix_etaAdelic' F D v γ hγ ϖ hϖ hϖ0]`; unfold `Sigma0'.eta` to `!![ϖ, 0; 0, 1]` (check its definition in Slash/Sigma0.lean); `rw [Matrix.det_fin_two_of]; simp` (template `JacobsSlash.norm_det_toMatrix_eta3_le`).
3. `isCompactoid_heckeBlockOp_etaAdelic'`: `exact Weight.isCompactoid_heckeBlockOp (toMatrix F D v) κ U hU χ hρ hϖ1 (norm_det_toMatrix_etaAdelic' F D v ϖ hϖ hϖ0).le hvΔ hv idx u`.
4. `finite_image_etaAdelic'_of_isOpen_of_isCompact`: `exact AbstractHeckeOperatorSlash.finite_image_doubleCoset_of_isOpen_of_isCompact hUo hUc _`.
5. Fork: in `1_Setting.lean` add `import PhD.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace`, delete the hand-made instance (keep `norm_three_lt_one`); rebuild the fork (instance defeq verified: both are `⟨instNormedFieldValuedAdicCompletion, _⟩`); redefine `kappaForms`/`heckeU3` through `FormsQ`/`heckeUpiQ` (6_Matrix.lean) — `rfl`-level; renames.jsonl; README §1/§5.4; PROGRESS.md.

#### Mathlib lemmas needed
- `Matrix.det_fin_two_of`, `norm_one`, `mul_one`, `sub_zero`, `WithZero.coe_lt_one`/`decide`; project `toMatrix_etaAdelic'`, `etaAdelic'_mem_levelMonoid'`, `Sigma0'.eta`, `finite_image_doubleCoset_of_isOpen_of_isCompact`, `Weight.isCompactoid_heckeBlockOp`.

#### Sources
- [Buz07] §10 p. 72 (Definition of `S^D_κ(U;r)`), Lemma 12.2 p. 78, §9 p. 69; [Jac03] Def 1.30, 1.33.

#### Generality decision
- `S` general (Jacobs's `Σ₁(3)` vs Buzzard's `M_t`); `η ∈ Δ` and finiteness as hypotheses of `heckeUpiQ` with discharging lemmas; `D` any `F`-algebra for the definitions, `[DivisionRing D] [FiniteDimensional F D]` only where the adelic topology is needed (`open scoped TensorProduct.RightActions`).

### [CLEANUP-4] /cleanup PhD/QMF/Weight/Quaternionic.lean + fork 1_Setting/6_Matrix (final)
- **Status**: done (2026-08-19, inline: linter zero, headers consistent) | **Depends on**: T007 | **Type**: cleanup.

---

## Item 6 — radius restriction; redundant API

### [T008] Route the level action through `AnalyticWeight.kappaSlashAction`; delete `Sigma0'.adjEquiv`
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE — `kappaLevelSlashAction (κ : AnalyticWeight …) := comap … κ.kappaSlashAction`, twisted
  action/SMulSlashClass through `κ.kappaSlash` (all `rfl` lemmas intact); `WeightSeries` no longer appears in
  Forms.lean; `Sigma0'.adjEquiv` deleted (zero users); whole surface rebuilt; linter zero. **Files**: PhD/QMF/Weight/Forms.lean, PhD/QMF/Slash/Sigma0.lean | **Depends on**: none | **Parallel**: yes | **Type**: refactor

#### Statement
```lean
-- Forms.lean
@[instance_reducible]
noncomputable def kappaLevelSlashAction (κ : AnalyticWeight UK S ρ) :
    RightSlashAction (levelMonoidOf θ S) c(ℕ, K) :=
  RightSlashAction.comap (levelMonoidOfToS θ S) κ.kappaSlashAction
@[instance_reducible]
noncomputable def kappaLevelSlashActionTwisted (κ : AnalyticWeight UK S ρ) (χ : S →* Kˣ) :
    RightSlashAction (levelMonoidOf θ S) c(ℕ, K) :=
  RightSlashAction.twist (kappaLevelSlashAction θ κ)
    (fun r f δ => map_smul (κ.kappaSlash (levelMonoidOfToS θ S δ)) r f)
    (χ.comp (levelMonoidOfToS θ S))
-- `kappaLevelSlashActionTwisted_slash` stays `rfl`; `kappaLevelSMulSlashClassTwisted`'s `show` line uses `κ.kappaSlash`.
-- Sigma0.lean: delete `Sigma0'.adjEquiv` (no users).
```
#### Proof sketch
1. Edit the two defs; fix the `show` in `kappaLevelSMulSlashClassTwisted` (`κ.toWeightSeries.kappaSlash` → `κ.kappaSlash`, definitionally equal); `grep -rn "kappaLevelSlashAction θ" PhD` for callers passing a `WeightSeries` (expected: none besides Forms.lean).  Result: `WeightSeries` no longer appears in Forms.lean; `AnalyticWeight.kappaSlashAction`/`smulSlashClass` have a consumer (update README §4).
2. Delete `Sigma0'.adjEquiv` after `grep -rn adjEquiv PhD` confirms zero uses; renames.jsonl.
3. Rebuild `PhD.QMF.Weight.Compact PhD.QMF.Weight.Algebraic PhD.QMF.Slash.Quaternionic` + the fork leaf; `runLinter`.
#### Sources — n/a (API). #### Generality — unchanged.

### [T009] `kappaSlash_restrictRadius`
- **Status**: done (2026-08-19: `WeightSeries.kappaSlash_congr rfl rfl`; axioms standard) | **File**: PhD/QMF/Weight/Char.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement
```lean
theorem kappaSlash_restrictRadius {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ' : ℝ}
    (hS : S' ≤ S) (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ, ‖PowerSeries.coeff m (κ.expansion.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m)
    (g : S') : (κ.restrictRadius hS hb hdecay).kappaSlash g = κ.kappaSlash ⟨g.1, hS g.2⟩ := by sorry
```
#### Proof sketch
1. `exact WeightSeries.kappaSlash_congr rfl rfl` (SlashAction.lean:376 — general in `(S, ρ)`; the columns agree by `rfl`, `restrictRadius_col`).
2. Document in the docstrings of `restrictRadius` (already drafted) that the finer decay is a hypothesis and why (the radius, not integrality, is recorded); README §3 "Known gap" paragraph → "restriction in `ρ` via `restrictRadius` under the finer-decay hypothesis; the saturation theorem deriving it for `SigmaNorm`-type levels is not formalised".
#### Sources — [Buz07] §13 p. 79 (`B_r ⊆ B_{r'}` inclusions). #### Generality — any `S' ≤ S`, any `ρ'` with `LevelBounds S' ρ'`.

### [CLEANUP-5] /cleanup Forms.lean, Char.lean, Slash/Sigma0.lean after T008/T009 (final)
- **Status**: done (2026-08-19, inline: linter zero on the three files) | **Depends on**: T008, T009 | **Type**: cleanup.

---

## Item 5 — pre-existing `runLinter` findings (39)

Each is a cleanup ticket: remove the unused hypothesis (and fix call sites) or `omit … in` for section
variables; one `simpNF`; one `nolint`.  Verify with `lake exe runLinter <module>` (findings listed
in the forms-headline run; full list `scratchpad/linter_legacy.txt` at planning time).

### [CLEANUP-6] PhD/TateFredholm/BlockOp.lean (6)
- **Status**: done (2026-08-19: 5 `omit … in`, `matrixCoeff_inclSubtype` de-simped + unused binder dropped, cascade `blockProj_blockIncl` omitted; linter zero) | **Depends on**: none | **Type**: cleanup.  `cSpace.ofTendsto_apply` (3 unused args, :71), `cSpace.projSubtype_apply` (2, :209), `matrixCoeff_inclSubtype` (1 unused arg + simpNF "LHS simplifies", :230 — restate on the simplified LHS or drop `@[simp]`), `cSpace.blockIncl_apply` (1, :587), `cSpace.blockProj_apply` (3, :595).  This file is now in the general layer — highest priority of the six.
### [CLEANUP-7] PhD/JacobsSlash/2_U3Data.lean (23 unused-argument findings)
- **Status**: done (2026-08-19: 23 + cascades → `omit [..] in` to the fixed point (scripted loop); `lemma211_first'/second'` lost the unused `h3 ht hνc` (4_DiamondW call sites updated with `(t := t) (ν := ν)`); cascades into 3_BaseChange/3_BinomialTheorem also omitted; linter zero) | **Type**: cleanup.  `coeff_kappaSeries₂` (:216), `sq_two_omega_add_one` (:279), `norm_omega` (:288), `norm_le_of_sub` (:321), `norm_sub_le_max'` (:327), `rowInt_monomial/_add/_neg/_mul/_inv` (:421–459), `diagRescale_zero/_sub`, `constantCoeff_diagRescale`, `diagRescale_monomial` (:716–744), `rescaleMat_apply_one_zero/_one_one` (:760/764), `linSeries_smul`, `quadSeries_smul` (:800/807), `neg_eight_ne_zero`, `norm_neg_eight_sub_one` (:844/847), `lemma211_first'`, `lemma211_second'` (:895/956), `norm_coeff_smul_diagRescale_le` (:989).  Mostly section-variable `[IsUltrametricDist K]`/`[CompleteSpace K]`/`hp` leaks → `omit … in`.
### [CLEANUP-8] PhD/JacobsSlash/1_PadicAnalytic.lean (4)
- **Status**: done (2026-08-19, omit loop to fixed point; linter zero) | `norm_natCast_eq_one_of_coprime` (:52), `padicLog_one` (:166), `padicExp_zero` (:171), `binomialCoeff_zero` (:847).
### [CLEANUP-9] PhD/JacobsSlash/1_SlopeTheorem.lean (3)
- **Status**: done (2026-08-19, omit loop; linter zero) | `norm_det_le_of_row_bound` (:63), `det_row_smul_pow` (:83), `norm_tsum_eq_of_dominant` (:141).
### [CLEANUP-10] PhD/JacobsSlash/3_Slopes.lean (2)
- **Status**: done (2026-08-19: `omit hν2 in` on the two + cascaded `norm_det_NgenFun_minor`, callers updated; linter zero) | `norm_coeff_NgenFun_le` (:1072), `norm_coeff_NgenFun_sub_negGeom_lt` (:1082).
### [CLEANUP-11] `JacobsSlash.U1_9` naming (U3/2_Level.lean:315)
- **Status**: done (2026-08-19: `@[nolint defsWithUnderscore]` + docstring note) | Thesis name `U₁(9)`; add `@[nolint defsWithUnderscore]` with a one-line justification (renaming to `U₁9`/`levelU19` would touch ~40 files for no mathematical gain) — user may prefer the rename; say so in the ticket progress if so.

---

### [CLEANUP-FINAL] /cleanup-all on the whole board surface + README/PROGRESS/memory
- **Status**: done (2026-08-19, forms-followups beastmode) |
- **Progress**: DONE — final build green (fork leaves, Weight.Fredholm/Quaternionic/Algebraic, Slash.Quaternionic,
  FiniteDimensional); sorry census 0 (doc mentions only); axioms standard on every endpoint; whole-surface
  `runLinter` zero on QMF/, JacobsSlash/, TateFredholm/BlockOp, the ForMathlib instance file (remaining findings
  only in the TateFredholm core and the frozen FLT vendor — recorded in README §4/§5.7); dead-code sweep: deleted
  `blockProj_evalU3` (no consumer after T003), remaining zero-ref decls are endpoints/API (README §4); README
  status, §1 (+Fredholm, +Quaternionic, instance), §3 (neat levels & the determinant, restrictRadius,
  kappaSlashAction routing), §4 rewritten, §5 (5.6 done, 5.4 half done, new 5.6 non-neat/(Pr), 5.7);
  PROGRESS.md rows (1_Setting, 6_Matrix, 7_Fredholm); memory `parallel-ticket-boards` (COMPLETE),
  `analyticweight-headline`, MEMORY.md. | **Depends on**: every other ticket | **Type**: cleanup-all.  README §1 (Fredholm.lean, Quaternionic.lean, ForMathlib instance), §3 (neat-level model isomorphism, determinant, radius restriction), §4 (dead-code sweep re-run), §5 (tick 5.4 partially, 5.6, 5.7); `PhD/JacobsSlash/PROGRESS.md`; memory `parallel-ticket-boards` (+ this board), `analyticweight-headline`.
