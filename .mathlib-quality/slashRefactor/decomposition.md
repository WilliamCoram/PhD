# Decomposition — slashRefactor (QMF right-slash layer + self-enclosed JacobsSlash fork)

Board: `.mathlib-quality/slashRefactor/`.  Companion to `plan.md` **REVISION 2** (the
fork architecture, port map, and statement-form rules there are binding context for
everything below; the T-CRIT resolution is assumed).

## Skeleton location

S-tranche (QMF layer, written 2026-08-06):
- `PhD/QMF/Slash/Sigma0.lean` — `Σ₀'`, the adjugate dictionary, `eta`
- `PhD/QMF/Slash/Basic.lean` — `RightSlashAction` class + `ofAntiHom` + `SMulSlashClass`
- `PhD/QMF/Slash/WeightModule.lean` — `matrixSubstR`, Buzzard slash on `WeightModule`, `jTwist` bridge
- `PhD/QMF/Slash/AutomorphicFunction.lean` — automorphic slash, `levelSubmoduleSlash`, seam theorem
- `PhD/QMF/Slash/HeckeMonoid.lean`, `PhD/QMF/Slash/HeckeMatrix.lean`,
  `PhD/QMF/Slash/Quaternionic.lean` — PENDING (S-SKEL ticket): right-coset abstract
  Hecke, right evaluation machinery, and the quaternionic specialisation seam
  (leaf **Q12**, user-requested 2026-08-06: `levelMonoid' := Sigma0'.comap toMatrix`,
  `levelMonoidToSigma0'`, `etaAdelic'` with component `(ϖ 0; 0 1)`, `WeightModule`
  slash pulled back along the corestriction, and the classical-weight quaternionic
  modular forms `L(U, L_{n,ν})` via `levelSubmoduleSlash` — the classical right-slash
  forms space, mirroring `Quaternionic.lean:84-147` + `UpiElement.lean:205`; the
  fork's adelic ports P12/P14/P16/P20 instantiate this file rather than building the
  comap plumbing locally).

P-tranche (the fork): skeletons are produced per-port-ticket (see the Result P
adaptation note below); `PhD/JacobsSlash/` is currently empty by design.

**DEVIATION (user-directed, binding):** the Step 2.5 `lake build` verification of the
skeleton is DEFERRED — no builds may run while the BCALL-B beastmode session owns the
build directory.  The board's `GATE-1` ticket performs the full skeleton compile +
digit-prefix module-name check before any proof ticket may start.  Until GATE-1 is
green, every skeleton signature is provisional.

## Sources for this project (source-faithfulness note)

This is a *dialect/transcription* project: the primary sources are (a) the existing
Lean code being transcribed (each leaf cites the exact declaration), and (b) the
verbatim thesis/Buzzard quotes already captured in `.mathlib-quality/qmf/decomposition.md`
and `.mathlib-quality/jacobs/decomposition.md` and in the module docstrings
(`AutomorphicFunction.lean:11-16`, `WeightModule.lean:12-18`, `HeckeMonoid.lean:30-32`
carry the [Buz07 §9 pp. 68-69] quotes verbatim).  The thesis PDF itself is not in the
repo; quotes below are cited through those recorded locations.

---

## Result Q (QMF tranche): the right-slash dialect over the left library

### Plain-English proof (what is being built and why it's sound)

Buzzard's §9 defines: a right `Mₜ`-module structure on `L_{n,v}` (`γ` sends `Z^m` to
`(cZ+d)^n det(γ)^v ((aZ+b)/(cZ+d))^m`), a right action on `A`-valued functions
(`(f|u)(g) = f(gu⁻¹).uₚ`), and `L(U,A)` as the `|`-fixed points.  The library
(`PhD/QMF/`) holds the left-handed shadows of all three, built through the adjugate
anti-isomorphism.  The dialect reverses the presentation: define the right-handed
objects by Buzzard's own formulas over the right-handed monoid `Σ₀'` (his `Mₜ`), and
prove each equal/equivalent to the adjugate transport of its left shadow.  Soundness
rests on three elementary facts: `adjugate` is an anti-homomorphism preserving `det`
(mathlib, any comm ring); `adjugate` is involutive for 2×2; and the matrix identity
`(adjugate δ)ᵀ = J δ J⁻¹` (`J = (0 1; −1 0)`), which locates the only place where the
naive transport differs from Buzzard's formula (the homogenisation seam of the
classical weight module).

### Leaves

- **Q1** (leaf, project+mathlib): `Sigma0'` — the monoid.
  - Lean: `PhD/QMF/Slash/Sigma0.lean` (`Sigma0'`, `mem_iff`, `entry_le_one`, `v_c_le`,
    `v_d_eq_one`, `det_ne_zero`)
  - Source: [Buz07 §9 p. 68] via `Sigma0.lean:74` docstring ("Left-handed version of
    Buzzard's `Mₜ`") — `Σ₀'` is the *unmirrored* `Mₜ`: entries integral, `d` a unit,
    `v(c) ≤ γ`, `det ≠ 0`.
  - Source claim (verbatim, `Sigma0.lean:33` design note): "the adjugate …carries
    Buzzard's '`d` a unit, `π^t ∣ c`' to '`a` a unit, `π^t ∣ c`' — which is *exactly*
    Pollack–Stevens' `Σ₀(p)`."
  - Lean ↔ source: the carrier of `Sigma0'` is the `Sigma0` carrier with `v (g 1 1) = 1`
    replacing `v (g 0 0) = 1`.
  - Discharged by: transcription of `Sigma0.mul_mem'`/`one_mem'` (`Sigma0.lean:75-106`)
    with the roles of the diagonal entries swapped: the unit-product entry is
    `(ab)₁₁ = a₁₀b₀₁ + a₁₁b₁₁` with `v(a₁₀b₀₁) ≤ γ·1 < 1 = v(a₁₁b₁₁)` — same
    ultrametric argument, mirrored indices.
  - Attacks attempted:
    - [1] Edge cases: `γ` arbitrary `< 1` (as in `Sigma0`); `g = 1` (`d = 1` unit ✓,
      `c = 0` ✓); `g = eta ϖ` (`d = 1` unit ✓ — note the thesis η has the unit in the
      `d`-slot, confirming the mirror is the right one for `η₃ = (3 0; 0 1)`).
    - [2] Closure attack: could the mirrored product argument fail because `Sigma0`'s
      proof used `a`-position asymmetrically?  Checked `Sigma0.lean:91-96`: the unit
      argument uses `(ab)₀₀ = a₀₀b₀₀ + a₀₁b₁₀` with the second term small via
      `v(b₁₀) ≤ γ`; mirror uses `(ab)₁₁ = a₁₀b₀₁ + a₁₁b₁₁`, second term IS the unit
      product and the first is small via `v(a₁₀) ≤ γ` — symmetric, works.
    - [3] Source-drift: Buzzard's `Mₜ` also requires `det ≠ 0` and integrality — both
      present.  No drift.
    - Verdict: SURVIVED.

- **Q2** (leaf, mathlib): the adjugate dictionary.
  - Lean: `Slash/Sigma0.lean` (`Sigma0'.adj`, `Sigma0.adj`, `adj_mul` ×2, `adj_one` ×2,
    `det_adj` ×2, `adj_adj` ×2, `adjEquiv`, `eta`, `adj_eta`)
  - Source: `Sigma0.lean:42-54` design note (the adjugate is *the* level-preserving
    anti-automorphism); mathlib `Matrix.adjugate_fin_two_of` (`adjugate !![a,b;c,d] =
    !![d,-b;-c,a]`, Adjugate.lean:380), `adjugate_mul_distrib` (`adjugate (A*B) =
    adjugate B * adjugate A`, Adjugate.lean:455, any `CommRing`), `adjugate_adjugate`
    (`= det A ^ (n−2) • A`; at `n = 2` the exponent is 0 — involutive), `det_adjugate`.
  - Lean ↔ source: membership transport = Q1's mirror argument entrywise
    (`v(−x) = v(x)`); anti-hom = `adjugate_mul_distrib` restricted to the submonoid;
    `det_adj` from `det_adjugate : det (adjugate A) = det A ^ (n−1)` at `n = 2`
    (`det ≠ 0` not even needed).
  - Discharged by: the four mathlib lemmas above (verified against the mathlib source
    at `.lake/packages/mathlib/.../Adjugate.lean` this session: lines 264/269
    (`mul_adjugate`/`adjugate_mul`), 309, 373-381, 443-481).
  - Attacks attempted:
    - [1] Discharge attack: `adjugate_mul_distrib` needs only `CommRing` — verified at
      source line 455 (the `IsLeftRegular` aux at 443 is subsumed by the general
      statement).  No invertibility hypothesis smuggled in.  ✓
    - [2] Edge case `n = 2` exponents: `adjugate_adjugate` gives `det^(2−2) • A = A` ✓;
      `det_adjugate` gives `det^(2−1) = det` ✓.  Both checked against the statements,
      not guessed.
    - [3] Counterexample search on `adj_eta`: `adjugate !![ϖ,0;0,1] = !![1,0;0,ϖ]` by
      `adjugate_fin_two_of` with `b = c = 0` — signs vanish, matches `Sigma0.eta`
      literally.  ✓
    - Verdict: SURVIVED.

- **Q3** (leaf, project): the `RightSlashAction` class + `ofAntiHom` + `SMulSlashClass`.
  - Lean: `PhD/QMF/Slash/Basic.lean`
  - Source: mathlib `SlashAction` (SlashActions.lean:36-53) for the axiom shape
    (`slash_one`, `slash_mul` right-composed, `add_slash`, `zero_slash`); the
    weight-free variant is forced because our weights parametrise carriers (design
    recorded in plan.md "Mathlib interface").
  - Lean ↔ source: axioms are mathlib's verbatim with `β` deleted;
    `ofAntiHom` proofs: `slash_mul` is `τ(δ₁δ₂) • a = (τ δ₂ * τ δ₁) • a =
    τ δ₂ • τ δ₁ • a` — `hmul` + `mul_smul`.
  - Discharged by: `mul_smul`, `one_smul`, `smul_zero`, `smul_add` (mathlib core).
  - Attacks attempted:
    - [1] Composition attack: does `ofAntiHom`'s `slash_mul` come out in the RIGHT
      order?  `a ∣ (δ₁δ₂) = τ(δ₁δ₂) • a = (τδ₂ · τδ₁) • a = τδ₂ • (τδ₁ • a) =
      (a ∣ δ₁) ∣ δ₂` ✓ — right-action law holds with `hmul` as stated (`τ(xy) = τy·τx`).
    - [2] Instance-loop attack: `ofAntiHom` is a `def`, not `instance` — cannot induce
      search loops between the left action and the slash.  ✓
    - [3] Minimality: no `SMul R A` in the base class; scalars enter only through the
      `SMulSlashClass` mixin (needed exactly once, for `levelSubmoduleSlash.smul_mem'`).
      Mirrors the library's `SMulCommClass` seam.  ✓
    - Verdict: SURVIVED.

- **Q4** (leaf, project): `matrixSubstR` and its calculus.
  - Lean: `Slash/WeightModule.lean` (`matrixSubstR`, `_X`, `_one`, `_mul`,
    `_eq_matrixSubst_transpose`, `_mem_homogeneousSubmodule`)
  - Source: [Buz07 §9 p. 68] verbatim quote at `WeightModule.lean:12-18` ("send
    `∏ᵢ Zᵢ^{mᵢ}` to `∏ᵢ (cᵢZᵢ + dᵢ)^{nᵢ} (aᵢdᵢ − bᵢcᵢ)^{vᵢ} ((aᵢZᵢ + bᵢ)/(cᵢZᵢ + dᵢ))^{mᵢ}`") —
    homogenised via `Z = X/Y`, `P(X,Y) = Yⁿp(X/Y)`: the substitution is
    `P ↦ P(aX+bY, cX+dY)` (computed in plan.md; the `(cZ+d)ⁿ` factor is the `Y`-slot).
  - Lean ↔ source: `matrixSubstR g : X_i ↦ Σ_j g i j • X_j` is substitution by the
    *rows* of `g` — `X ↦ aX+bY`, `Y ↦ cX+dY` ✓.
  - Discharged by: transcription of `matrixSubst`'s proofs (`WeightModule.lean:38-71`)
    with `g j i` ↦ `g i j`; `_eq_matrixSubst_transpose` is definitional unfolding;
    `_mul` mirrors `matrixSubst_mul` with the sum-swap in the other order.
  - Attacks attempted:
    - [1] Composition-order attack (the classic right-action sign error): computed
      `matrixSubstR g (matrixSubstR h P)`: `X_i ↦(h) Σ_j h i j X_j ↦(g) Σ_k (h*g) i k X_k`,
      so `matrixSubstR g ∘ matrixSubstR h = matrixSubstR (h*g)`, i.e.
      `matrixSubstR (g*h) = matrixSubstR h ∘ matrixSubstR g` — matches the skeleton's
      `(matrixSubstR h).comp (matrixSubstR g)` ✓ and gives `slash_mul` in the right
      order in Q5.
    - [2] Homogenisation check: at `γ = (a b; c d)`, `Z^m·Y^{n}`-side: Buzzard's
      `(cZ+d)^n((aZ+b)/(cZ+d))^m` homogenises to `(aX+bY)^m(cX+dY)^{n−m}` =
      `matrixSubstR γ (X^m Y^{n−m})` ✓ (degree bookkeeping exact).
    - [3] Hypothesis test: homogeneity preservation needs only that each substituted
      variable is homogeneous of degree 1 — same as the left proof; no extra
      hypothesis.  ✓
    - Verdict: SURVIVED.

- **Q5** (leaf, project): the Buzzard slash instance on `WeightModule`.
  - Lean: `Slash/WeightModule.lean` (`instance RightSlashAction (Sigma0' …)
    (WeightModule R n ν)`, `slash_coe`, `SMulSlashClass` instance)
  - Source: [Buz07 §9 p. 68] as in Q4; the character slot: Buzzard's `det(γ)^v` =
    `ν (Sigma0'.adj δ)` through the dictionary — legitimate because
    `det ∘ adjugate = det` (Q2's `det_adj`), so for `ν = Sigma0.detChar γ hγ w` the
    value is literally `det(δ)^w`.
  - Lean ↔ source match: `P ∣ₛ δ = ν(adj δ) • P(aX+bY, cX+dY)` vs Buzzard's
    `det^v · (substitution)` — exact for det-characters; for a general phantom `ν`
    this is the *definition* of the transported character (recorded, not hidden).
  - Discharged by: Q4's calculus + `Sigma0'`-membership arithmetic (`slash_mul` needs
    `ν (adj (δ₁δ₂)) = ν (adj δ₂ * adj δ₁)`… note `adj_mul` gives `adj (δ₁δ₂) =
    adj δ₂ * adj δ₁`, and `ν` is a monoid hom to the *commutative* `Rˣ`, so the value
    splits as `ν(adj δ₁)·ν(adj δ₂)` — commutativity of `Rˣ` absorbs the reversal).
  - Attacks attempted:
    - [1] Character-order attack: does the anti-reversal break the cocycle?
      `ν(adj(δ₁δ₂)) = ν(adj δ₂)ν(adj δ₁) = ν(adj δ₁)ν(adj δ₂)` (`Rˣ` comm) — matches
      the product of the two slash factors regardless of order.  ✓
    - [2] Edge case `δ = 1`: `adj 1 = 1`, `ν 1 = 1`, `matrixSubstR 1 = id` ⇒
      `slash_one` ✓.
    - [3] Source-drift: Buzzard's action needs no integrality ("extends to all of
      `M₂(K)`", `WeightModule.lean:26`) — our restriction to `Σ₀'` is a *domain
      choice*, not a mathematical constraint; consistent with the left library's
      restriction to `Σ₀`.  ✓
    - Verdict: SURVIVED.

- **Q6** (leaf, project — **known-risk statement**): `jTwist` and the bridge
  `slash_eq_adj_smul`.
  - Lean: `Slash/WeightModule.lean` (`jTwist`, `slash_eq_adj_smul`)
  - Source: plan.md "convention design" derivation (this session):
    `(adjugate δ)ᵀ = J δ J⁻¹` verified by direct computation
    (`J δ = (c d; −a −b)`, `(Jδ)J⁻¹ = (d −c; −b a) = (adjugate δ)ᵀ`), hence
    `matrixSubst (adj δ) = matrixSubstR ((adj δ)ᵀ) = matrixSubstR J⁻¹ ∘ matrixSubstR δ ∘
    matrixSubstR J`, giving `P ∣ₛ δ = jTwist ((adj δ) • jTwist.symm P)` with
    `jTwist := matrixSubstR J` restricted to the homogeneous submodule, and **no
    residual determinant factor** (the `ν` values agree by Q2/Q5).
  - Lean ↔ source: the bridge as stated in the skeleton.
  - Discharged by: Q4 (`matrixSubstR_mul`), Q2 (`det_adj`), `matrixSubst`-vs-`matrixSubstR`
    transpose lemma; `jTwist` invertible since `J` is (`J⁻¹ = −J = (0 −1; 1 0)`).
  - Attacks attempted:
    - [1] Sign attack: the two candidate `J`'s (`±J`) give the same conjugation
      (`(−J)δ(−J)⁻¹ = JδJ⁻¹`) but different `jTwist`s (differing by `(−1)^{deg}` on
      degree-`n` forms).  The bridge holds for either consistent choice; the skeleton
      pins `J = (0 1; −1 0)`.  **STATEMENT-AMENDMENT RISK Q6-A** (recorded): if
      elaboration surfaces a `(−1)ⁿ` mismatch, the fix is the other sign of `J` (or an
      explicit `(−1)ⁿ` in `jTwist`), amended on this leaf — never a proof-side hack.
    - [2] Composition direction: `matrixSubstR (JδJ⁻¹) = matrixSubstR J⁻¹ ∘
      matrixSubstR δ ∘ matrixSubstR J` — checked against Q4's rule
      (`matrixSubstR (A·B·C) = matrixSubstR C ∘ matrixSubstR B ∘ matrixSubstR A`) ✓.
    - [3] Degree preservation: `J`-substitution is linear ⇒ preserves
      `homogeneousSubmodule` (Q4's lemma at `g = J`) ⇒ `jTwist` well-defined.  ✓
    - [4] Necessity attack (is the twist really unavoidable?): if `jTwist` were the
      identity, `matrixSubst (adj δ) = matrixSubstR δ` would force `(adj δ)ᵀ = δ`,
      i.e. `d = a`, false already for `eta ϖ` (`ϖ ≠ 1`).  The seam is real, not an
      artifact.  ✓
    - Verdict: SURVIVED (with recorded amendment path Q6-A).

- **Q7** (leaf, project): the automorphic slash instance.
  - Lean: `Slash/AutomorphicFunction.lean` (instance + `slash_apply`)
  - Source claim (verbatim, `AutomorphicFunction.lean:13-15` quoting [Buz07 §9 p. 69]):
    > "If `f : D^×_f → A` and `u ∈ U` then define `f|u : D^×_f → A` by
    > `(f|u)(g) := f(gu⁻¹).uₚ`."
  - Lean ↔ source: `(φ ∣ₛ δ)(g) = φ(g·δ⁻¹) ∣ₛ δ` — the abstract form with the
    coefficient slash in place of `.uₚ`; inverse in `G` (Buzzard's `u⁻¹` is likewise
    in the ambient group `D^×_f`).
  - Discharged by: group axioms + coefficient `RightSlashAction` axioms; `left_invt`
    from `φ.left_invt` at `γ, g·δ⁻¹`; `slash_mul`:
    `φ(g(δ₁δ₂)⁻¹) ∣ (δ₁δ₂) = φ(gδ₂⁻¹δ₁⁻¹) ∣ δ₁ ∣ δ₂` (computed in plan session ✓).
  - Attacks attempted:
    - [1] Composition attack: hand-checked `slash_mul` both ways (above) — associativity
      of the translation inverses matches the right-composition of coefficient slashes;
      no `mul_inv_rev` sign trap.  ✓
    - [2] Well-definedness attack: `Γ`-left-invariance survives *right* translation ✓
      (left and right multiplications commute); would fail if the slash translated on
      the left — the definition uses `g * δ⁻¹` correctly.  ✓
    - [3] Source-drift: Buzzard restricts to `u ∈ U` with `uₚ ∈ Mₜ`; the abstract
      instance allows any `δ ∈ Δ'` — strictly more general, same formula; the level
      condition reappears in Q8 where it belongs.  ✓
    - Verdict: SURVIVED.

- **Q8** (leaf, project): `levelSubmoduleSlash` + membership forms.
  - Lean: `Slash/AutomorphicFunction.lean` (`levelSubmoduleSlash`, `mem_…_iff`, `mem_…_iff'`)
  - Source claim (verbatim, `AutomorphicFunction.lean:15-16` quoting [Buz07 §9 p. 69]):
    > "Now set `L(U, A) := {f : D^×\D^×_f → A : f|u = f for all u ∈ U}`."
  - Lean ↔ source: fixed points of the Q7 slash over `u ∈ U`, as a submodule (sums,
    zero, scalars fixed — needs `SMulSlashClass`); `iff'` is the pointwise
    transformation law `φ(gu) = φ(g) ∣ₛ u` (substitute `g ↦ gu` in the fixed-point
    equation, use `u·u⁻¹ = 1` — same manipulation as the library's
    `mem_levelSubmodule_iff` ↔ `apply_mul_coe` pair, `AutomorphicFunction.lean:175-192`).
  - Discharged by: Q7 + `RightSlashAction` axioms + `SMulSlashClass`.
  - Attacks attempted:
    - [1] Quantifier attack: `iff'` direction ⇐ needs the equation at `u⁻¹` as well —
      same subtlety the library handled at `apply_mul_coe` (uses `h u⁻¹ (g*u)`);
      transcribed route available.  ✓
    - [2] Edge: trivial coefficients (`a ∣ₛ δ = a`): `levelSubmoduleSlash` = functions
      on `Γ\G/U` — recovers FLT's weight-2 space, same sanity anchor as the left
      library's docstring claims.  ✓
    - [3] Submodule axioms: `smul_mem'` is exactly `SMulSlashClass.smul_slash` — the
      mixin was introduced for this single use; no hidden strength.  ✓
    - Verdict: SURVIVED.

- **Q9** (leaf, project — **the seam theorem**, T-CRIT quarantine):
  `levelSubmoduleSlash_eq_levelSubmodule`.
  - Lean: `Slash/AutomorphicFunction.lean:…` (statement carries the `hcompat` hypothesis)
  - Source: design analysis (plan.md T-CRIT): the two level conditions are
    `φ(gu) ∣ₛ adj-image = φ(g)` (left, unfolded) vs `φ(gu) = φ(g) ∣ₛ u` (slash);
    under the pointwise dictionary `a ∣ₛ u = u⁻¹ • a` on `U`-elements they coincide
    *verbatim* (substitute and use `slash_mul`/`mul_smul` — no monoid-leaving
    composition is performed, avoiding the illegal `det·1 ∉ Σ₁` step identified in
    planning).
  - Lean ↔ source: the hypothesis `hcompat` IS the dictionary; the conclusion is
    submodule equality (`Submodule.ext`, both inclusions by the same rewrite).
  - Discharged by: Q7/Q8 + `mem_levelSubmodule_iff` (library) + group manipulation in
    `U`.
  - **Quarantine design (binding):** whether `hcompat` *holds* for a given coefficient
    module is NOT this leaf's problem.  For the Jacobs κ-modules it is the
    `adjParams`-vs-`params` computation (JacobsSlash tranche); if a central character
    `κ(det u)`-residue appears there, the amendment happens on the *instantiation*
    leaf (twisted-equivalence form), and Q9 stands unchanged as the clean-case seam
    theorem.  Fredholm-side results transport regardless via the proved
    twist-invariance lemmas (`charPowerSeries_blockOp_twist`,
    `charPowerSeries_twist_U3MatrixOp` — both sorry-free in `PhD/Jacobs/`).
  - Attacks attempted:
    - [1] The T-CRIT attack itself (does the "compose with `∣u` ⇒ central `det`"
      argument break equality?): the composition `adj u · u = det u · 1` leaves the
      acting monoid (`det u · 1 ∉ Σ₁(9)`-type: `d`-entry `det u ≢ 1 mod 9`), so the
      would-be obstruction is not expressible pointwise; the equality proof never
      forms it.  The obstruction question moves — correctly — into `hcompat` for each
      instantiation.  ✓ (This attack *shaped* the statement: an unconditional
      `levelSubmoduleSlash = levelSubmodule` would be UNPROVABLE-as-stated for some
      coefficient modules; the hypothesis-parametrised form is the honest one.)
    - [2] Vacuity attack: is `hcompat` ever satisfiable?  Yes — trivial coefficients
      satisfy it (`both sides = a`); and for `ofAntiHom`-transported coefficients it
      reads `τ(u) • a = u⁻¹ • a`, i.e. `τ = (·)⁻¹` on `U` — the group-invertible
      locus, where the anti-hom *can* be inversion.  Non-vacuous.  ✓
    - [3] Direction attack: checked both inclusions use only `hcompat` and its
      `u ↦ u⁻¹` instance (available: `U` a group).  ✓
    - Verdict: SURVIVED.

### Prior-B2 log consultation (Q-tranche)

`.mathlib-quality/slashRefactor/` has no `b2_log.jsonl` yet (new board).  Consulted
the *related boards'* logs for reincarnation risk: `qmf`'s recorded L4.3-family
det-twist notes (charCoeff_M22op_eq scalar bookkeeping) are the ancestors of the
T-CRIT design here — addressed structurally (Q9 quarantine + Q6-A amendment path),
not re-ticketed blind.  `jacobs/b2_log.jsonl`: no name or shape overlap with Q1–Q9
(checked by name: no `slash`/`adj`/`Sigma0'` entries).

---


## Result P (the fork): a self-enclosed, natively right-handed JacobsSlash

### Workflow adaptation (recorded deviation from Phase 1e Step 2.5)

The fork's unit of work is a *file port*, not a fresh lemma: for ~200 already-proved
declarations, a per-declaration `:= by sorry` skeleton IS the port itself.  Adaptation
(user-directed architecture, 2026-08-06): each port ticket carries (a) the port mode
(VERBATIM / NEAR-VERBATIM / MIRROR, per plan.md's port map), (b) a **statement-form
spec** for every convention-carrying declaration (what the thesis-form statement looks
like — written before porting, checked against the recorded thesis display), and
(c) the source pointer to the Jacobs original whose proof is copied/mirrored.  The
compile check runs per-ticket (after GATE-1 opens builds).  The verbatim source-quote
discipline is inherited: the fork's leaves cite the SAME recorded thesis quotes as the
originals' decompositions (jacobs/ and qmf/ boards), because the mathematical content
is identical — only the handedness of presentation changes.

### The port's two engines (proved once, used everywhere)

1. **The S-tranche abstract layer** supplies right-handed level spaces
   (`levelSubmoduleSlash` = Buzzard's `L(U,A)` verbatim), right-coset Hecke operators
   (`Slash/HeckeMonoid`), and right evaluation (`Slash/HeckeMatrix`) — so the fork's
   `U3/6_Matrix` instantiates abstract machinery exactly the way the original
   instantiates the left-handed machinery.  Statements right-handed; proofs by
   transport (adjugate dictionary + inversion, the T-CRIT identity
   `adjugate (u/det) = u⁻¹` where the level seam appears) or mechanical mirror.
2. **Native data.**  In the right-handed development the thesis's own tables
   (ε-matrices, h's, σ/d/u certificates, the p. 21/p. 28 displays) are consumed
   as printed — `kappaSlash δ := ofGenFun (weightGenFun t δ.1)` makes [Jac Prop 2.6]
   definitional with NO adjugate, and the left library's table-recomputation
   obligation (qmf decomposition.md:240) disappears.  `certificate_search.py` re-runs
   un-mirrored as the validation oracle.

### Port leaves (P1–P20; modes and statement-form decisions)

Each `Pn` = one port ticket; the file list, modes, and prefixes are plan.md's port
map.  Statement-form decisions requiring care (rule 3 of plan.md) are called out:

- **P-V group (VERBATIM)**: `1_PadicAnalytic`, `1_GenFun`, `1_BlockOp`,
  `2_BinomialTheorem`, `2_SlopeTheorem`, `U3/2_Hurwitz`, `U3/2_Compose`, `4_Slopes`,
  `5_SlopeReading`, `5_Instance`, `5_BaseChange`, `4_DiamondW` (near-verbatim).
  Change: header/imports/namespace only.  Attack (per file, at ticket time): diff the
  ported file against the original modulo the allowed changes — any statement delta
  is a defect.  These files never mention the acting monoid's handedness (checked by
  grep for `Sigma0`/`Sigma1`/`adjParams` at planning: only `DiamondW`/`U3Data`
  borderline — see P-D).
- **P-D group (data orientation)**: `3_U3Data`, `U3/5_Factorisations`.
  Statement-form spec: the h-series and ε-matrices are transcribed thesis displays —
  KEEP the data identical; the orientation audit decides only whether block labels
  `(i,j)` and the certificate factorisation shape (`cᵢvₜ = d·c_σ·u` as the thesis
  writes, vs the left library's `classRep i * etaRep t = d·c_σ·u`) transpose.  Anchor:
  [Jac p. 28] "the matrix of U₃ will have the form A = (ε_{i,j})" + the p. 21 display.
  The B15 coboundary history is the precedent: expected outcome is that the fork's
  certificate layer is CLOSER to the thesis (right-handed certificates are the
  thesis's own §B.1 data); any residual scalar is a recorded statement amendment.
- **P-M group (MIRROR)**:
  - `U3/1_Setting`: keep `K₃/v₃/ν₃/θ₃` verbatim; `Σ₁(9)'` native (`d ≡ 1`,
    mirror of `Setting.lean:580-606`'s closure proof — the mirrored estimate is
    symmetric, checked in Q1/J1 attacks).  No left `Σ₀/Σ₁` anywhere.
  - `U3/3_Level`: `U₁(9)` with the THESIS congruence (`≡ (∗ ∗; 0 1) mod 9` — this is
    a *different subgroup of `D_f^×`* from the library's `a ≡ 1` form; the fork's
    class set/Hecke theory is about the thesis's own group, which is the point).
    `hClassNumberOne'` mirrors the permanent-sorry contract.
  - `U3/4_ClassSet`: Thm 2.1/Lemma 2.2 for the thesis-form group.  Statement-form
    check: the classRep diagonal data is self-mirror-stable or transposes — audit
    against [Jac p. 24] reps `(1,0),(5,0),(7,0)`.
  - `U3/4_EtaDecomposition`: `η₃ = (3 0; 0 1)` native; the display
    `U₁(9)η₃U₁(9) = ⊔ₜ U₁(9)vₜ` with the thesis's `vₜ = (3 0; 9t 1)`-form reps
    ([Jac p. 20]: `U(3 0;0 1)U = ⊔ U(3 0;9t 1)` — recorded at qmf
    decomposition.md:238).  Proof mirrors the library's 500-line Lemma 2.3 with
    left/right swapped; the mirror is index-mechanical (the library proof was itself
    produced by mirroring the thesis's argument).
  - `U3/3_KappaSlash`: `kappaSlash δ := ofGenFun (weightGenFun t δ.1)` (NO adjParams);
    `matrixCoeff_kappaSlash` definitional; right-action law `kappaSlash_mul` mirrors
    `kappaOp_mul`'s compAn/ODE/binomial route with the substitution cocycle in the
    thesis's own composition order (the thesis proves the RIGHT action law —
    "It is an easy check that … |κ is a right-action" — so the fork's proof follows
    the source MORE directly than the left library did).
  - `U3/6_Matrix`: `kappaForms := levelSubmoduleSlash …` (Buzzard's L(U,A) verbatim);
    `heckeU3 := heckeOperatorSlash` at `η₃`; `heckeU3_apply_classRep` in the p. 21
    display shape; `blockOp` from the thesis-orientation certificates.
  - `U3/7_Fredholm`, `U3/8_HeckeSlopes`: `evalU3` via the right `evalAtReps`;
    `charPowerSeriesU3` and the factorisation + `L₃` witness — statements identical
    to the originals up to the underlying operator being the fork's.
- Excluded: `DiamondHecke` (AG-W-ID in flight), `ClassNumberOneFallback` (unimported).

### S-tranche additions from revision 2 (leaves Q10–Q11, skeletons pending)

- **Q10** `Slash/HeckeMonoid.lean`: `fixedPoints`-side = `levelSubmoduleSlash` (Q8);
  `heckeOperatorSlash (h : finite right-coset image) : L_slash(V) →ₗ[R] L_slash(U)`
  summing `a ∣ₛ xᵢ` over the image of `{g}·V`?? — orientation: Buzzard decomposes
  `UηU = ∐ᵢ Uxᵢ` and sums `f|xᵢ`; the mirror of `HeckeMonoid.lean:113-135` over
  `QuotientGroup.rightRel U` (right quotient) with the sum over the image of `U·g`.
  Statement-form spec written at S-SKEL ticket time by mirroring the left file
  side-by-side; proofs mirrored (the left file is 177 lines, self-contained group
  bookkeeping).  Attack focus: which side's finiteness hypothesis and which quotient
  the `Fintype` lives on — must match `finite_image_doubleCoset` mirrored.
- **Q11** `Slash/HeckeMatrix.lean`: right `heckeOperator_apply_rep` (the p. 21-shape
  matrix recipe: factorisations `cᵢ·x = d·c_σ·u` in thesis orientation) + right
  `evalAtReps`/`bijective_evalAtReps` (the (2.1.1) iso for `|`-transforming
  functions).  Mirror of `HeckeMatrix.lean`/`Decomposition.lean`.

### Prior-B2 / precedent consultation (P-tranche)

The fork inherits every recorded statement amendment of the originals in mirrored
form: E1–E6 errata data decisions (verbatim), the B15 classWeight coboundary (expected
to SIMPLIFY or vanish in thesis orientation — the certificate layer is native; if a
coboundary remains it is recorded exactly as B15 was), the L5.2 CoeffInt-not-RowInt
correction (carried verbatim into `U3/3_KappaSlash`).  No `b2_log.jsonl` name overlap
(fresh `JacobsSlash` namespace).

### Deferred (recorded, NOT ticketed)

- **W-slash / DiamondHecke port** — after jacobs-endgame AG-W-ID lands.
- **Retirement of PhD/Jacobs/ (STATED PLAN, user 2026-08-06)**: once the fork is
  sorry-free and green, `PhD/Jacobs/` moves to legacy — kept as history
  (Keep-PR'd-history discipline) but **never imported again by anything**.  The
  fork's no-import rule is therefore not a temporary hygiene measure; it is the
  permanent architecture.  The move itself is a user action, not a board ticket.
- **BRIDGE (POTENTIAL FUTURE WORK — user decision 2026-08-06: do NOT build)**: a
  kernel-checked "the two U₃'s agree" certificate.  Because Jacobs goes to legacy
  (never imported), a bridge file importing both developments is a dead end; if this
  is ever built, it must itself be **self-enclosed** — e.g. proving *within the fork*
  that the fork's `U₃` also admits the left-handed presentation (re-deriving the
  mirror sum as a theorem of JacobsSlash), rather than referencing legacy
  declarations.  Not ticketed; open via `/develop --continue` only on explicit user
  request.
