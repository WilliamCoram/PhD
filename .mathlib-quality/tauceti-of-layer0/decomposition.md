# Decomposition: overconvergent automorphic forms, Layer 0 (the adelic setting)

Companion to `plan.md`. Every leaf below is a `:= by sorry` declaration, or a `sorry`-field of a
definition, in the skeleton; the pointer is `File.lean · declaration name` (names are stable, line
numbers are not). Sources: [RM] = the roadmap clause the leaf discharges, quoted verbatim;
[Buz07] / [Jac03] / [Voi21] / [Loe11] = literature, quoted verbatim from `references/*.txt` with a
line locator; [SRC] = the read-only reference development `PhD/Main/…` at `7586051`, cited by
`File.decl` for the *proof idea* only (never imported). Discharge lines name the Mathlib lemmas a
worker will call; the names were checked by elaboration (`scratchpad/names_of.lean`; the result is
recorded in the Gate section). Attack categories: [1] search for a contradicting shape, [2] edge
cases, [3] necessity / weakening of each hypothesis, [4] match against the source and the roadmap,
[5] the Mathlib discharge.

## Skeleton location

`PhD/TauCeti/Code/OverconvergentForms/`, 22 files:

- `Quaternion/{ReducedNorm, Definite, BaseChange, Hurwitz}.lean` (§0.1)
- `Adelic/{RightBaseChange, FiniteAdeles, Basic, Components, IntegralAdeles, Norm}.lean` (§0.2)
- `Level/{Local, Standard, ClassSet, HeckePair}.lean` (§0.3, §0.4)
- `Hamilton/{Splitting, Setting, Level, ClassNumberOne, ClassSet, EtaDecomposition,
  Factorisations}.lean` (§0.1.3, §0.3.5, §0.5)
- `Examples.lean` (Examples)

Build status: recorded in the "Gate" section at the end of this file.

## Prior-B2 consultation (Step 4.6), once for the whole tree

Every `b2_log.jsonl` of the project was read (the default board and the named boards `qmf`,
`jacobs`, `slashRefactor`, `hurwitz-cn1`, `laweights`, `lwx-*`, `tate-riesz`, `tauceti-np-layer0`).
No entry names a declaration of this tree. Five entries have a *shape* that recurs here:

- `lwx-quaternion`, the `central` field: *a tame scalar was required to lie in the level, which is
  false for neat levels*. **Addressed**: no leaf asserts that a scalar lies in a level. Scalars enter
  through `unitsIncl_algebraMap_mem_stabilizer`, which takes membership as a hypothesis, and through
  `unitAt_smul_one_mem_wildMonoid_iff`, which is about the monoid `Δ`, not the level.
- `lwx-theta`, `LWX.theta_mem_Iw`: *elaborated without the section hypothesis `hU`*; and
  `lwx-conductor` R13–R17: *an `include` omitted a variable*. **Addressed by design**: the skeleton
  contains no `include`. Every hypothesis of the decomposition theorems is an explicit binder
  (the first draft of `Level/Local.lean` used `variable` + `include` and was rewritten).
- `jacobs` J015/J020: *a missing hypothesis on the weight character*. Not applicable to Layer 0;
  recorded so that Layer 1's board consults it.
- `qmf`, `isCompactoid_restrictOp`: *false without an ambient hypothesis that the prose took for
  granted*. **Addressed**: the adversarial pass hunted for exactly this and found L11.13 (`hr1`).

---

## §0.1 Quaternion algebras (`Quaternion/`)

### Plain-English proof substrate

[Voi21, 3.2.9] (`voight.txt:2241`): "Suppose `char F ≠ 2` and let `B = (a, b | F)`. Then the map
`α = t + xi + yj + zk ↦ ᾱ = t − xi − yj − zk` defines a standard involution on `B`." Mathlib's
`ℍ[R,a,b]` is `ℍ[R,a,0,b]` with `i² = a`, `j² = b`, `k = ij = −ji`, and its `star` is this
involution. Put `trd x = x + x̄ = 2·re` and `nrd x = x x̄`. Expanding,
`x x̄ = re² − (imI·i + imJ·j + imK·k)²`, the cross terms cancel because `i, j, k` anticommute, and
`(imI·i + imJ·j + imK·k)² = a·imI² + b·imJ² − ab·imK²`; hence the formula for `nrd`. Multiplicativity
is `x y (x y)‾ = x (y ȳ) x̄ = nrd y · x x̄`, the scalar `nrd y` being central. The quadratic relation
is `x² − (x + x̄) x + x̄ x = 0`.

*Independence of the splitting.* Let `φ : ℍ[R,a,b] → M₂(S)` be an `R`-algebra map with `2, a, b`
invertible in `S`; write `I = φ i`, `J = φ j`, `K = IJ`. Cayley–Hamilton for `2 × 2` matrices gives
`I² = tr(I) I − det(I)`, and `I² = a`, so `tr(I)·I = a + det I`. Multiplying on the left and on the
right by `J` and adding, `tr(I)(IJ + JI) = 2(a + det I) J`; the left side vanishes, `J` is invertible
(`J² = b`), and `2` is invertible: `det I = −a`, whence `tr(I)·I = 0` and `tr I = 0` because `I` is
invertible. The same for `J`, and for `K` against `I` (`K² = −ab`, `KI = −IK`). The trace is
linear, so `tr(φ x) = 2·re = trd x`. Finally `φ(x)² = trd(x) φ(x) − nrd(x)` and
`φ(x)² = tr(φ x) φ(x) − det(φ x)` give `(det φ x − nrd x)·1 = 0`.

*Definiteness.* For a real embedding `σ`, `σ(nrd x) = σ(re)² + |σ a| σ(imI)² + |σ b| σ(imJ)² +
|σ a σ b| σ(imK)²` when `σ a, σ b < 0`: a sum of four non-negative terms, zero only if `x = 0`.

*The Hurwitz order.* [Voi21, Lemma 11.1.2] (`voight.txt:7621`): "The lattice `O = ℤ + ℤi + ℤj + ℤω`
in `B` is the unique order that properly contains `ℤ⟨i, j⟩`, and `O` is maximal. […] *Proof.*
Suppose that `O′ ⊋ ℤ⟨i, j⟩` and let `α = t + xi + yj + zk ∈ O′` with `t, x, y, z ∈ ℚ`. Then
`trd(α) = 2t ∈ ℤ`, so by Corollary 10.3.6 we have `t ∈ ½ℤ`. Similarly, `αi ∈ O′` therefore
`trd(αi) = −2x ∈ ℤ` and `x ∈ ½ℤ`, and in the same way `y, z ∈ ½ℤ`. Finally,
`nrd(α) = t² + x² + y² + z² ∈ ℤ`, and considerations modulo 4 imply that `t, x, y, z` either all
belong to `ℤ` or to `½ + ℤ`; thus `α ∈ O`." [Voi21, §11.2] (`voight.txt:7640`): "`O^× = Q₈ ∪
(±1 ± i ± j ± k)/2` is a group of order 24." [Voi21, 11.3.1] (`voight.txt:7771`): "for all
`γ ∈ B`, there exists `μ ∈ O` such that `nrd(γ − μ) < 1`. (In fact, we can take
`nrd(γ − μ) ≤ 1/2`; see Exercise 11.7.)" [Voi21, Lemma 11.3.2] (`voight.txt:7783`): "For all
`α, β ∈ O` with `β ≠ 0`, there exists `μ, ρ ∈ O` such that `α = βμ + ρ` and `nrd(ρ) < nrd(β)`.
*Proof.* […] Let `γ = β⁻¹α ∈ B`. Then by 11.3.1, there exists `μ ∈ O` such that `nrd(γ − μ) < 1`.
Let `ρ = α − βμ`. Then by multiplicativity of the norm, `nrd(ρ) = nrd(α − βμ) < nrd(β)`."
[Voi21, Proposition 11.3.4] (`voight.txt:7793`): "Every right ideal `I ⊆ O` is right principal
[…] there exists an element `0 ≠ β ∈ I` with minimal reduced norm `nrd(β) ∈ ℤ_{>0}`. We claim that
`I = βO`."

### Leaves — `ReducedNorm.lean`

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
- **L1.8** `mapRingHom` (fields), `nrd_mapRingHom`, `trd_mapRingHom` — change of coefficients along
  `f : R →+* S`, target `ℍ[S, f a, f b]`. Discharge: `ext <;> simp`. Attacks: [4] the target type
  carries `f a`, `f b`, not `a`, `b`; L3.1 is stated with `algebraMap F R a` accordingly ✓.
  SURVIVED.
- **L1.9** `Quaternion.nrd_eq_normSq` — [RM] §0.1.1 "where `nrd = normSq`". Discharge:
  `Quaternion.normSq_def'` + `simp [nrd_apply]` + `ring`. Attacks: [2] `ℍ[R]` is the *definition*
  `ℍ[R,-1,0,-1]`; the statement elaborated in the skeleton, so the unfolding is available ✓.
  SURVIVED.

### Leaves — `Definite.lean`

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
- **L2.5** `nonempty_ringHom_real`, `isTotallyDefinite_hamilton` — a totally real number field has a
  real embedding (`NumberField.ComplexEmbedding.IsReal.embedding` at any infinite place);
  `(−1, −1 | ℚ)` is totally definite (`map_neg`, `map_one`, `neg_one_lt_zero`). SURVIVED.

### Leaves — `BaseChange.lean`

- **L3.1** `baseChangeEquiv`, `baseChangeEquiv_tmul` — [RM] §0.2.4 "The reduced norm extends to
  `nrd : D_f^× →* (𝔸_F^f)^×`". Lean: `ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R, algebraMap a, algebraMap b]`,
  `x ⊗ r ↦ r • mapRingHom (algebraMap F R) a b x`. Sketch: forward map by
  `Algebra.TensorProduct.lift` of `mapRingHom` (as an `F`-algebra map) and `algebraMap R _`, which
  commute; `R`-linearity for the scoped right algebra is `right_algebraMap_apply`; bijectivity
  because it sends the `R`-basis `rightBasis (basisOneIJK a 0 b)` to `basisOneIJK` of the target.
  Attacks: [2] `R = F`: the identity up to `TensorProduct.rid` ✓. [3] `F` a field is not needed; a
  commutative ring suffices — kept as a field because every use has one. [5]
  `QuaternionAlgebra.basisOneIJK` verified; `rightBasis` is L5.2. SURVIVED.
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
- **L3.5** `det_eq_nrdBaseChange` — [RM] §0.1.3 "Prove `det (θ_𝔭 x) = nrd x`". Lean: for every
  `R`-algebra isomorphism `θ : ℍ[F,a,b] ⊗[F] R ≃ₐ[R] M₂(R)` with `2`, `a`, `b` invertible in `R`.
  Sketch: L1.7 for `θ ∘ baseChangeEquiv.symm`, with `S = R`. Attacks: [3] bijectivity of `θ` is not
  used; an `AlgHom` would do — kept as `≃ₐ` because the consumer has one. SURVIVED.

### Leaves — `Hurwitz.lean`

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
- **L4.3** `isUnit_hurwitzOrder_iff` — [Voi21, §11.2]: "`γ` […] is a unit if and only if
  `nrd(γ) = 1`". Sketch: (→) `nrd` multiplicative with values in `ℕ` (L4.2); (←) `star x` is the
  inverse (L1.2, L4.2). SURVIVED.
- **L4.4** `card_units_hurwitzOrder` — [RM] §0.1.4 "with exactly `24` units"; [Voi21, §11.2]
  "a group of order 24". [SRC] `1_Hurwitz.card_units_hurwitzOrder`: a bijection with the `24` tuples
  `(A,B,C,D) ∈ [−2,2]⁴` of one parity with `A²+B²+C²+D² = 4`, counted by `decide`. Attacks: [5]
  `decide` on a `Finset` filter of `625` tuples compiled in [SRC] ✓. SURVIVED.
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
- **L4.8** `eq_hurwitzOrder_of_le` — [RM] §0.1.4 "prove it is a maximal order"; [Voi21, Lemma
  11.1.2] (quoted). Lean: a subring `S ⊇ hurwitzOrder` of `ℍ[ℚ]` with `S.toAddSubgroup.FG` equals
  it. Sketch: Voight's proof with L2.4 at `a = b = −1` for `α, αi, αj, αk ∈ S`. Attacks: [3] `FG`
  is necessary (`S = ℍ[ℚ]` contains `𝒪`). [4] "order" is rendered as "finitely generated subring";
  that it spans `ℍ[ℚ]` follows from `𝒪 ≤ S`. SURVIVED.

---

## §0.2 The adelic group (`Adelic/`)

### Plain-English proof substrate

[Buz07, §9, p. 68] (`buzzard.txt:2653`): "Define `𝔸_{F,f}` to be the finite adeles of `F` and
`D_f := D ⊗_F 𝔸_{F,f}`. If `x ∈ D_f` then let `x_p ∈ D_p = M₂(F_p)` denote the projection onto the
factor of `D_f` at `p`." [Voi21, 27.6.6–27.6.7] (`voight.txt:21432`): "The `S`-finite adele ring has
a compact open subring `Ô := ∏_{v ∉ S} O_v ⊆ B̂`. We similarly define the `S`-finite idele group
with its compact open subgroup `B̂^× ⊃ ∏_{v ∉ S} O_v^× =: Ô^×`." [Voi21, 27.6.12]
(`voight.txt:21466`): "we have a natural multiplicative map `‖ ‖ : B̂^× → ℝ_{>0}`,
`α = (α_v)_v ↦ ∏_v |nrd(α_v)|_v`."

Everything topological reduces to coordinates. With an `F`-basis `b` of `D`, `b i ⊗ 1` is an
`𝔸`-basis of `D ⊗_F 𝔸` and the coordinate map `D_f ≃ 𝔸^ι` is `𝔸`-linear; both sides carry the
module topology, so it is a homeomorphism (a linear map between module-topology modules is
continuous). Hence `D_f` inherits local compactness, the Hausdorff property and total
disconnectedness from `𝔸_F^f`, and `D_f^×` inherits them through the closed embedding
`Units.embedProduct : D_f^× → D_f × D_fᵐᵒᵖ`. For `𝔸_F^f` itself: `𝒪_v` is open (Mathlib) and
compact, because it is complete, a discrete valuation ring, and its residue field is finite — the
residue map `𝓞 F → 𝒪_v/𝔪_v` is surjective by the density of `F` in `F_v` and kills the prime `v`,
whose quotient is finite; then `∏_v 𝒪_v` is compact by Tychonoff, open in the restricted product,
and `RestrictedProduct.locallyCompactSpace_of_group` applies. The route of [RM] §0.2.3 for the
order: "`𝒪_D ⊗ ℤ̂` is the image of the compact `∏_v 𝒪_v^4` under a continuous map, hence compact, and
open because `∏ 𝒪_v` is open in `𝔸_F^f`; the unit group of a compact multiplicatively closed subset
is compact because `Units.embedProduct` is a closed embedding."

The section `ι_v`: extension by zero `F_v → 𝔸_F^f` (`RestrictedProduct.single`) is additive and
multiplicative but not unital; tensoring with `D` gives `e_v : D ⊗ F_v → D_f` with
`e_v(x) g = e_v(x g_v)` and `g e_v(x) = e_v(g_v x)`, and `ι_v(u) := 1 + e_v(u − 1)` is a unit with
inverse `1 + e_v(u⁻¹ − 1)`, since `(u − 1) + (u⁻¹ − 1) + (u − 1)(u⁻¹ − 1) = 0`. If `g_v = 1` then
`e_v(x) g = e_v(x) = g e_v(x)`: the image of `ι_v` commutes with every element of trivial
`v`-component.

### Leaves — `RightBaseChange.lean`

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

### Leaves — `FiniteAdeles.lean` (seam with the global-number-fields roadmap)

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
- **L6.2** `compactSpace_adicCompletionIntegers`, `isCompact_adicCompletionIntegers`,
  `locallyCompactSpace_adicCompletion` — Sketch:
  `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` (complete:
  closed in a complete space; DVR: Mathlib instance; finite residue field: L6.1); local compactness
  from one compact open neighbourhood of `0` in a topological group. Attacks: [5] the criterion is
  stated for `𝒪[K] = Valued.v.integer` and `𝓀[K]`; `adicCompletionIntegers` is
  `Valued.v.valuationSubring` with the same carrier — the transfer is `isCompact_iff_compactSpace` on
  the common underlying set; **flagged for the ticket** as the one defeq seam of the file. The
  criterion needs `[(Valued.v).RankOne]`: Mathlib's `instRankOneAdicCompletion` ✓. SURVIVED.
- **L6.3** `integralAdeles` (fields), `mem_integralAdeles_iff`, `exists_integralAdeles_eq` — [RM]
  §0.2.3 "`∏_v 𝒪_v`". Every family of local integers is an adele (the restricted-product condition
  holds everywhere). SURVIVED.
- **L6.4** `isCompact_integralAdeles`, `isOpen_integralAdeles` — [Voi21, 27.6.6] "compact open
  subring". Sketch: the range of `RestrictedProduct.structureMap`, the image of the compact
  `∏_v 𝒪_v` (`isCompact_univ_pi`, L6.2) under a continuous map; open by
  `RestrictedProduct.isOpenEmbedding_structureMap`, whose openness hypothesis is Mathlib's `Fact`
  instance. Attacks: [5] both names verified; `structureMap`'s range equals the carrier by `ext`.
  SURVIVED.
- **L6.5** `locallyCompactSpace_finiteAdeleRing`, `t2Space_finiteAdeleRing`,
  `totallyDisconnectedSpace_finiteAdeleRing` — [RM] §0.2.1 "locally compact totally disconnected".
  Sketch: `RestrictedProduct.locallyCompactSpace_of_group`; T2 and total disconnectedness because
  `RestrictedProduct.continuous_coe` is a continuous injection into the product of the `F_v`, which
  is T2 and totally disconnected (each `F_v` is: a valued field has a basis of clopen balls).
  Attacks: [5] **name miss repaired**: `Function.Injective.totallyDisconnectedSpace` does not exist;
  use `isTotallyDisconnected_of_image` (verified in the file
  `Topology/Connected/TotallyDisconnected.lean`). Total disconnectedness of `F_v` may itself need a
  short proof from `Valued.isClopen_closedBall` — **flagged for the ticket**. SURVIVED.

### Leaves — `Basic.lean`

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
- **L7.3** `locallyCompactSpace_Df`, `t2Space_Df`, `totallyDisconnectedSpace_Df` — [RM] §0.2.1
  "`D_f` is a locally compact totally disconnected topological ring". Sketch: L5.3 for a finite
  basis (`Module.Free.chooseBasis`), L6.5. SURVIVED.
- **L7.4** `locallyCompactSpace_Dfx`, `totallyDisconnectedSpace_Dfx` — [RM] §0.2.1 "`D_f^×` is a
  locally compact totally disconnected group". Sketch: closed embedding into `D_f × D_fᵐᵒᵖ`
  (`Topology.IsClosedEmbedding.locallyCompactSpace`), L7.3. `IsTopologicalGroup (Dfx F D)` is found
  by instance search in the skeleton (the `example` at the end of the file). SURVIVED.

### Leaves — `Components.lean`

- **L8.1** `toLocal_tmul`, `toLocal_incl` — API of the component map
  `toLocal = Algebra.TensorProduct.map (AlgHom.id F D) (evalAlgHom F v)`. `simp`. SURVIVED.
- **L8.2** `continuous_toLocal`, `continuous_toLocalUnits` — [RM] §0.2.2 "continuous". L5.4 with
  `RestrictedProduct.continuous_eval`; `Continuous.units_map`. SURVIVED.
- **L8.3** `ext_toLocal` — the components are jointly injective. Sketch: coordinates (L5.2): the
  coordinates of `toLocal v x` are the `v`-components of those of `x` (the statement L9.2), and an
  adele is determined by its components (`RestrictedProduct.ext`). Attacks: [3] `Module.Finite` is
  used only to pick a finite basis; a worker may drop it with `Module.Free.chooseBasis` — left in,
  flagged. SURVIVED.
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
- **L8.6** `singleₗ` (fields), `extendZero_mul`, `toLocal_extendZero`, `toLocal_extendZero_of_ne`,
  `extendZero_mul_eq`, `mul_extendZero_eq` — [RM] §0.2.2 "the inclusion `ι_𝔭 : GL₂(F_𝔭) → D_f^×` of
  elements with trivial components elsewhere". [SRC] `04_UpiElement.singleₗ`, `.iotaV`,
  `.iotaV_mul`, `.toLocal_iotaV`, `.toLocal_iotaV_ne`, and `23_QuaternionData.QMF.
  iotaV_mul_eq_iotaV_mul_toLocal`. Sketch: on pure tensors with `RestrictedProduct.mul_single`,
  `single_mul`, `single_eq_same`, `single_eq_of_ne`. Attacks: [2] `extendZero` is **not** unital:
  `extendZero 1 ≠ 1`, which is why `localIncl` is `1 + extendZero (u − 1)` ✓. [5] four names
  verified; `single` needs `DecidableEq` on the places — `open scoped Classical` in the file ✓.
  SURVIVED.
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
- **L8.9** `unitAt`, `toGL_unitAt`, `toGL_unitAt_of_ne`, `unitAt_injective`, `unitAt_commute`,
  `toLocalUnits_eq_one_of_toGL_eq_one`, `continuous_unitAt` — `ι_v` through the rigidification.
  [SRC] `04_UpiElement.unitAt`, `.toLocal_unitAt`, `23_QuaternionData.QMF.unitAt_mul`,
  `.unitAt_comm_of_toLocal_eq_one`. SURVIVED.
- **L8.10** `unitsIncl_algebraMap_commute`, `toMatrix_unitsIncl_algebraMap` — global scalars are
  central, and `θ_v(c ⊗ 1) = c • 1` by `F_v`-linearity (`c ⊗ 1 = 1 ⊗ c = algebraMap F_v _ c`). [SRC]
  `23_QuaternionData.QMF.unitsIncl_algebraMap_comm`, `.toMatrix_unitsIncl_algebraMap`. SURVIVED.

### Leaves — `IntegralAdeles.lean`

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
- **L9.3** `mem_adelicOrder_iff_forall` — membership is local. Immediate from L9.2 and
  `mem_integralAdeles_iff`. [SRC] `2_LevelTopology.forall_toLocal_mem_localOrder_iff`. SURVIVED.
- **L9.4** `incl_mem_adelicOrder_iff` — [RM] §0.2.1 "`D^× ∩ U₀(1)` is the finite unit group of a
  definite order". Lean: `x ⊗ 1 ∈ 𝒪_D ⊗ ℤ̂ ↔ x ∈ 𝒪_D`. Sketch: an element of `F` integral at every
  finite place is in `𝓞 F` (`HeightOneSpectrum.mem_integers_of_valuation_le_one`). [SRC]
  `2_Level.mem_hurwitzOrder_of_forall_local`. Attacks: [5] the Mathlib lemma is stated for the
  valuation on `K`, ours for `Valued.v` on the completion; bridge by
  `valuedAdicCompletion_eq_valuation'` (verified) ✓. SURVIVED.
- **L9.5** `isCompact_adelicOrder`, `isOpen_adelicOrder`, `isCompact_localOrder`,
  `isOpen_localOrder` — [RM] §0.2.3 (route quoted in the substrate). Sketch: preimage of
  `Set.pi univ (fun _ ↦ integralAdeles)` under the homeomorphism L5.3; L6.4; `isCompact_univ_pi`,
  `isOpen_set_pi`. [SRC] `04_Level.isCompact_integralTensor`, `2_LevelTopology.
  isOpen_integralTensor`. SURVIVED.
- **L9.6** `U0` (fields), `mem_U0_iff`, `isCompact_U0`, `isOpen_U0`, `mem_U0_iff_forall`,
  `unitsIncl_mem_U0_iff`, `localIncl_mem_U0_iff` — [RM] §0.2.3 "its unit group
  `U₀(1) := (𝒪_D ⊗ ℤ̂)^×` is a compact open subgroup of `D_f^×`". Sketch: L7.1 with L9.5;
  locality from L9.3 applied to `g` and `g⁻¹`, stated with `localUnits`. Attacks: [2] at `w ≠ v`
  the component of `ι_v(u)` is `1 ∈ localUnits` ✓. SURVIVED.
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

### Leaves — `Norm.lean`

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
- **L10.3** `continuous_ideleNorm` — [RM] §0.2.4 "a continuous character". Sketch: trivial on the
  open subgroup `{x | x, x⁻¹ ∈ ∏ 𝒪_v}` (L7.1, L6.4), and a homomorphism that is trivial on an open
  subgroup is continuous. SURVIVED.
- **L10.4** `ideleNorm_algebraMap` — [RM] §0.2.4 "by the product formula". Lean: for `x : Fˣ`,
  `|x|_f = |N_{F/ℚ} x|⁻¹`. Sketch: `FinitePlace.prod_eq_inv_abs_norm`, reindexed along
  `FinitePlace.equivHeightOneSpectrum` (`finprod_comp_equiv`), with `FinitePlace.norm_embedding`.
  Attacks: [5] three names verified; the reindexing is the proof of Mathlib's own lemma, read
  backwards ✓. SURVIVED.
- **L10.5** `adelicNrd`, `coe_adelicNrd_unitsIncl`, `adelicNrd_apply` — [RM] §0.2.4 "The reduced
  norm extends to `nrd : D_f^× →* (𝔸_F^f)^×`". `Units.map` of L3.3; components by L3.3's
  `nrdBaseChange_map` at `f = evalAlgHom F v`. SURVIVED.
- **L10.6** `adelicNrd_apply_eq_det`, `det_toMatrix_unitsIncl` — [RM] §0.2.4 "with
  `nrd ∘ ι_𝔭 = det` at `𝔭`"; §0.1.3 "`det (θ_𝔭 x) = nrd x` for `x ∈ D`". Sketch: L3.5 at
  `R = F_v`: `2`, `a`, `b` are units of the field `F_v` because `F → F_v` is injective and `F` has
  characteristic `0`. Attacks: [3] `a ≠ 0`, `b ≠ 0` are necessary for L1.6 and automatic when a
  rigidification exists (a degenerate algebra is not split) — kept explicit, cheaper than deriving.
  SURVIVED.
- **L10.7** `continuous_adelicNrd`, `normClass`, `continuous_normClass`, `normClass_pos` — L3.4 +
  `Continuous.units_map`; L10.3. SURVIVED.
- **L10.8** `normClass_eq_one_of_isCompact` — [RM] §0.2.4 "trivial on `U₀(1)` and on every compact
  open subgroup". Sketch: the image of a compact subgroup under a continuous homomorphism to
  `(ℝ, ·)` with positive values is a compact subgroup of `ℝ_{>0}`; if it contained `c ≠ 1`, the
  powers `c^n`, `n ∈ ℤ`, would be unbounded or accumulate at `0 ∉` image. Attacks: [1] is openness
  needed? No — compactness alone ✓ (the roadmap's "compact open" is weakened to "compact"). [4]
  avoids the integrality of `nrd` on an order, which for a general basis-presented order would need
  L2.4 over `𝓞 F`. SURVIVED.
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

---

## §0.3–§0.4 Levels, class sets and the Hecke pair (`Level/`)

### Plain-English proof substrate

[Buz07, §9, p. 68] (`buzzard.txt:2639`): "If `t ∈ ℤ^J_{≥1}` then define `M_t` to be the elements
`(γ_j)` of `M₂(𝒪_p) = ∏_{j∈J} M₂(𝒪_j)` with the property that if `γ_j = ((a_j b_j), (c_j d_j))` then
`det(γ_j) ≠ 0`, `π_j^{t_j}` divides `c_j`, and `π_j` does not divide `d_j`. Then `M_t` is a monoid
under multiplication." The monoid law: `(γγ')_{10} = c a' + d c'` is divisible by `π^t`, and
`(γγ')_{11} = c b' + d d'` is a unit because `c b'` is not (`t ≥ 1`) and `d d'` is.

[Buz07, proof of Lemma 12.1] (`buzzard.txt:3223`): "for `t_j ≥ 1` the natural left coset
decomposition of the double coset `U₀(π_j^{t_j}) ((π_j 0), (0 1)) U₀(π_j^{t_j})` is
`∐_{α ∈ 𝒪_j/π_j} U₀(π_j^{t_j}) ((π_j 0), (α π_j^{t_j} 1))`." The computation, for
`u = ((a b), (c d)) ∈ Iw(ϖ^t)` and `u_α = ((1 0), (αϖ^t 1))`:
`η u u_α⁻¹ η⁻¹ = ((a − bαϖ^t, ϖ b), ((c − dαϖ^t)/ϖ, d))`. It lies in `Iw(ϖ^t)` exactly when
`c − dαϖ^t ∈ ϖ^{t+1}𝒪`, that is `α ≡ c/(dϖ^t) mod ϖ` — one residue class — and then its diagonal is
congruent to that of `u` modulo `ϖ^t`. So the quotient `u⁻¹ · (η u x_α⁻¹)` lies in the kernel
`Iw₁₁(ϖ^t)` of the diagonal residues, and the decomposition holds for every subgroup between
`Iw₁₁(ϖ^t)` and `Iw(ϖ^t)`. On the other side, `((ϖ β), (0 1))⁻¹ u η = ((a − βc, (b − βd)/ϖ),
(cϖ, d))`, integral exactly when `β ≡ b/d mod ϖ`.

[Buz07, §9, pp. 68–69] (`buzzard.txt:2692`): "Say `D_f^× = ∐_{λ=1}^μ D^× τ_λ U`. Then the groups
`Γ_λ := τ_λ⁻¹ D^× τ_λ ∩ U` are finitely-generated and moreover `τ_λ Γ_λ τ_λ⁻¹ ⊂ D^×` is
commensurable with `𝒪_D^×` and hence with `𝒪_F^×`." (`buzzard.txt:2702`): "If `𝔫` is an ideal of
`𝒪_F` which is coprime to `disc(D)` then we define `U₀(𝔫)` (resp. `U₁(𝔫)`) in the usual way as being
matrices in `(𝒪_D ⊗ ℤ̂)^×` which are congruent to `((∗ ∗), (0 ∗))` (resp. `((∗ ∗), (0 1))`) mod `𝔫`."
(`buzzard.txt:2749`): "If `η ∈ D_f^×` and `η_p ∈ M_t` then one can define an endomorphism `[UηU]` of
`L(U, A)` as follows: decompose `UηU = ∐_i U x_i` (a finite union)". [Loe11, Proposition 3.1.1]
(`loeffler.txt:735`): "For any compact open subgroup `K ⊆ G(𝔸_f)`, the double quotient
`G(F) \ G(𝔸_f) / K` is finite." [Loe11, Proposition 3.1.2] (`loeffler.txt:739`): "If `G_∞` is
compact, then `G(F)` is discrete in `G(𝔸_f)`."

Compact open subgroups: an open subgroup `V` meets a compact subgroup `U` in a subgroup of finite
index, because the cosets of `U ∩ V` are an open partition of `U`. Hence any two compact open
subgroups are commensurable, every conjugate of `U` is commensurable with `U`, and `U η U`, compact
and a disjoint union of open cosets `U x`, is a finite union.

### Leaves — `Local.lean`

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
- **L11.5** `diagonal_mem_monoidM`, `smul_one_mem_monoidM_iff` — [RM] §0.4.1 "the diagonal matrices
  `diag(a, d)` with `a ≠ 0` and `d` a unit lie in `M_t`"; §0.4.4 "the scalars `ι_𝔭(u · 1)` for
  `u ∈ 𝒪^×` lie in `Δ_t` […] `ι_𝔭(ϖ · 1)` does not". Attacks: [1] the roadmap's "`a ≠ 0`" omits
  integrality of `a`; the Lean statement has `v(x) ≤ 1` — **roadmap looseness recorded**, the
  statement is the correct one (`diag(ϖ⁻¹, 1) ∉ M_t`). SURVIVED.
- **L11.6** `isOpen_iwahori`, `isOpen_iwahoriOne`, `isOpen_iwahoriPrincipal` — for `γ ≠ 0`. Sketch:
  entries and determinant are continuous on `GL₂(K)` (units topology); `{x | v x ≤ γ}` is open for
  `γ ≠ 0` (`Valued.isClopen_closedBall`) and `{x | v x = 1}` is open. Attacks: [3] `γ ≠ 0` is
  necessary: the Borel subgroup is not open ✓. SURVIVED.
- **L11.7** `etaGL`, `lowerUnip`, `etaRep`, `upperRep` (the `det ≠ 0` fields), `coe_etaRep`,
  `det_etaRep` — [RM] §0.4.2 "The representatives are `x_α := η u_α` with
  `u_α := ((1 0), (α ϖ^t 1)) ∈ U_𝔭`, so that `x_α = ((ϖ 0), (α ϖ^t 1))`, `det x_α = ϖ`".
  `Matrix.det_fin_two`. SURVIVED.
- **L11.8** `coe_etaGL_mem_monoidM`, `etaGL_not_unit`, `lowerUnip_mem_iwahoriPrincipal`,
  `coe_etaRep_mem_monoidM` — [RM] §0.4.1 "`η := diag(ϖ, 1) ∈ M_t` is not a unit of `M_t`"; §0.4.2
  "`x_α ∈ M_t`". `η⁻¹ = diag(ϖ⁻¹, 1)` has `v(ϖ⁻¹) > 1`. Attacks: [3] `etaGL_not_unit` needs
  `v ϖ < 1` strictly (for `v ϖ = 1`, `η ∈ Iw`) ✓. SURVIVED.
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
- **L11.14** `valued_det_of_mem_doubleCoset` — [RM] §0.4.3 "every `x` in `U η_𝔭 U` has
  `‖det θ_𝔭(x)‖ = ‖ϖ‖`", local form: `det (u η u') = det u · ϖ · det u'`. Attacks: [3] any `γ`
  works, only `U ≤ Iw(γ)` is used ✓. SURVIVED.
- **L11.15** `mem_monoidM_iff_norm` — [RM] §0.4.1 "state the dictionary with the norm form
  `‖c‖ ≤ ‖ϖ‖^t`, `‖d‖ = 1` (Layer 1's `SigmaNorm`)". Lean: under `[(Valued.v).RankOne]` and
  `letI := Valued.toNormedField K Γ₀`. Sketch: the norm is a strictly monotone function of the
  valuation (`Valued.toNormedField.norm_le_iff`, `norm_le_one_iff`). SURVIVED.

### Leaves — `Standard.lean`

- **L12.1** `levelThreshold`, `levelThreshold_lt_one`, `levelThreshold_ne_zero`,
  `valued_pow_eq_levelThreshold` — the value `v(ϖ)^t = exp(−t) ∈ ℤᵐ⁰`. `WithZero.exp_lt_exp`.
  SURVIVED.
- **L12.2** `levelAt`, `mem_levelAt_iff`, `isOpen_levelAt`, `unitAt_mem_levelAt_iff`,
  `unitAt_mem_levelAt_of_ne` — `H.comap (toGL F D v)`; open by L8.5. SURVIVED.
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
- **L12.5** `lowerRightResidueLevel` (fields), `iInf_ker_lowerRightResidueLevel`,
  `lowerRightResidueLevel_surjective` — the quotient `U₀(𝔫)/U₁(𝔫)`. Surjectivity: lift each residue
  to a unit `d_k` (L11.4), take the product of the commuting elements `ι_{w k}(diag(1, d_k))`
  (`Finset.noncommProd`, L8.8), which lies in `U₀(1)` by integrality (L9.8). Attacks: [3] `w`
  injective is necessary: with `w 1 = w 2` and different exponents the two residues at one place are
  linked. `1 ≤ t k` is used by L11.4. SURVIVED.

### Leaves — `ClassSet.lean`

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
- **L13.3** `finite_classSet_of_le`, `finite_classSet_of_relIndex_ne_zero`,
  `hasFiniteClassSets_of_finite` — finiteness at one compact open level gives it everywhere.
  Sketch: `U ≤ U'` gives a surjection of class sets; if `[U' : U] < ∞` the fibres of
  `classSet U → classSet U'` are images of `U'/U`; for an open `U`, `U ∩ U₀` has finite index in the
  compact `U₀` (L13.1). Attacks: [1] is the fibre bound right for a *double* quotient? The fibre
  over `D^× g U'` is `{D^× g u' U : u' ∈ U'}`, a quotient of `U'/U` ✓. SURVIVED.
- **L13.4** `IsCompleteFamily`, `IsSection`, `isSection_iff`, `exists_isSection` — [RM] §0.3.3 "a
  *section* is a family `c : ι → D_f^×` bijective onto `classSet U`, and a *complete family* one
  that meets every double coset". SURVIVED.
- **L13.5** `stabilizer` (fields), `mem_stabilizer_iff`, `stabilizer_le`, `globalStabilizer`,
  `mem_globalStabilizer_iff`, `stabilizerEquiv`, `unitsIncl_algebraMap_mem_stabilizer`,
  `stabilizer_mul` — [RM] §0.3.3 "`Γ_λ := c_λ^{−1} D^× c_λ ∩ U` […] a subgroup of `U` isomorphic to
  `D^× ∩ c_λ U c_λ^{−1}` […] it contains `𝒪_F^× ∩ U`"; [Buz07, p. 68] (quoted). `stabilizer_mul`:
  changing the representative within its class conjugates the stabiliser by an element of `U`.
  Attacks: [1] is `stabilizer` = `c⁻¹ D^× c ∩ U`? `u ∈ c⁻¹D^×c ⟺ c u c⁻¹ ∈ D^×` ✓. SURVIVED.
- **L13.6** `finite_units_orderOf` — [RM] §0.2.1 "`D^× ∩ U₀(1)` is the finite unit group of a
  definite order". Lean: `F = ℚ`, `(a, b)` totally definite, `β` an order basis. Sketch: a unit `u`
  has `nrd u, nrd u⁻¹ ∈ ℤ` (L2.4: `orderOf` is a finitely generated subring) and positive (L2.1),
  so `nrd u = 1`; the standard coordinates of `u` are then bounded (`re² ≤ 1`, `|a| imI² ≤ 1`, …)
  and lie in `(1/N)ℤ` for a common denominator `N` of the basis, a finite set. Attacks: [3]
  definiteness is necessary (`M₂(ℤ)^×` is infinite) ✓. [4] no [SRC]: new; the Hurwitz case is L4.4.
  SURVIVED.
- **L13.7** `discreteTopology_globalUnits` — [RM] §0.2.1 "Its image `Γ := D^×` is discrete when
  `F = ℚ` and `D` is definite"; [Loe11, Proposition 3.1.2] (quoted). Sketch: `D^× ∩ U₀(1)` is the
  image of `𝒪_D^×` (L9.6), finite (L13.6); in a T1 group a subgroup meeting an open neighbourhood of
  `1` in a finite set is discrete. Attacks: [4] the roadmap's warning is respected: nothing is
  claimed for a general totally real `F`. SURVIVED.
- **L13.8** `finite_stabilizer` — [RM] §0.3.3 "which is discrete (§0.2.1) and compact, hence
  **finite**, when `D` is totally definite and `F = ℚ`". Sketch: `globalStabilizer c U` injects into
  `D^× ∩ c U c⁻¹`, a discrete closed subgroup (`Subgroup.isClosed_of_discrete`) inside a compact
  set. Attacks: [3] only compactness of `U` is used, not openness ✓. SURVIVED.

### Leaves — `HeckePair.lean`

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
- **L14.4** `Subgroup.commensurator_eq_top_of_isCompact_of_isOpen`,
  `Subgroup.isHeckeTriple_of_isCompact_of_isOpen` — [RM] §0.3.4 "for a submonoid `Δ ⊆ D_f^×`
  containing `U`, the pair `(Δ, U)` is a Hecke triple in the sense of Mathlib's `IsHeckeTriple`".
  L13.1 for the conjugates of `U`; `IsHeckeTriple.of_diagonal`. SURVIVED.
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
- **L14.7** `wildMonoidOf`, `HasWildLevel`, `etaAdelic_mem_wildMonoidOf`, `hasWildLevel_U0Level`,
  `isHeckeTriple_wildMonoidOf` — [RM] §0.4.3 "for `t ∈ ℕ_{≥1}^𝔓` the monoid
  `Δ_t := θ_p^{−1}(∏_𝔭 M_{t_𝔭}) ⊆ D_f^×` (Buzzard's 'wild level'); a compact open `U` *has wild level
  `≥ 𝔭^t`* if `U ⊆ Δ_t` […] Prove that `η_𝔭 ∈ Δ_t` for every `t`"; §0.4.5 "`(Δ_t, U)` is a Hecke
  triple"; [Buz07, p. 68] (`buzzard.txt:2656`): "we say that a compact open subgroup `U ⊂ D_f^×` has
  wild level `≥ π^t` if the projection `U → D_p^×` is contained within `M_t`". Attacks: [3]
  `etaAdelic_mem_wildMonoidOf` needs `w` injective (at a repeated place with a different threshold
  nothing breaks, but the proof by cases `k' = k` / `w k' ≠ w k` needs it) ✓. SURVIVED.
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

---

## §0.5 The running example `ℍ[ℚ]`, `p = 3` (`Hamilton/`)

### Plain-English proof substrate

[Jac03, §1.4, pp. 13–14] (`jacobs_thesis.txt:410`; the extraction drops `ν`, `ξ`, `×` and `⊗`):
"Let `D` be the discriminant 2 quaternion algebra over `ℚ` and write `D = ℚ(i; j)`. Take
`𝒪_D = ℤ[i; j; ½(1 + i + j + k)]` as our fixed maximal order of `D`." "1.18 Lemma. Suppose `L` is a
field of characteristic zero. Then, `D ⊗_ℚ L = M₂(L)` if and only if there exist `ν, ξ ∈ L` such
that `ν² + ξ² = −1`." "1.19 Lemma. There are no elements `ν, ξ ∈ ℚ₂` such that `ν² + ξ² = −1`."
"One easily verifies that for all odd primes `q` the map `D_q → M₂(ℚ_q)` given by
`a + bi + cj + dk ↦ ((a + bν_q + dξ_q, bξ_q − c − dν_q), (bξ_q + c − dν_q, a − bν_q − dξ_q))`" is an
isomorphism. [Jac03, Lemma 1.22] (`jacobs_thesis.txt:602`): "`D_f^× = D^× U₀(1)`. *Proof.* The
shortest way is to use the Jacquet-Langlands correspondence: we know that there are no cusp forms
of weight 2 […]" — **not the route taken here**. (`jacobs_thesis.txt:614`): "We have,
`D^× \ D_f^× / U = D^× \ D^× U₀(1) / U = D^× ∩ U₀(1) \ U₀(1) / U = 𝒪_D^× \ U₀(1) / U =
𝒪_D^× \ GL₂(ℤ_p) / H₁ = 𝒪_D^× \ GL₂(ℤ/pⁿ) / H₂`".

*The splitting.* With `I = ((ν ξ), (ξ −ν))`, `J = ((0 −1), (1 0))`: `I² = (ν² + ξ²)·1 = −1`,
`J² = −1`, `IJ = ((ξ −ν), (−ν −ξ)) = −JI`. In the basis `e₀₀ + e₁₁, e₀₀ − e₁₁, e₀₁ + e₁₀,
e₀₁ − e₁₀` of `M₂(S)` the four matrices `1, I, J, IJ` have coordinate determinant
`−(ν² + ξ²) = 1`, and that basis differs from the standard one by a matrix of determinant `±4`; so
`1, I, J, IJ` is an `S`-basis of `M₂(S)` exactly when `2` is invertible.

*Class number one.* [Voi21, Lemma 27.6.8] (`voight.txt:21450`): "The set of locally principal,
right fractional `O`-ideals is in bijection with `B̂^×/Ô^×` via the map `I ↦ α̂ Ô^×`, where
`I_p = α_p O_p` and `α̂ = (α_p)_p`; this map induces a bijection `Cls_R O ↔ B^× \ B̂^× / Ô^×`. […]
Conversely, given `α̂ ∈ B̂^×/Ô^×` we recover `I = α̂ Ô ∩ B`". Concretely ([SRC] `CN1/4_Dictionary`):
clear denominators so that `g` is everywhere integral; let
`I_g = {y ∈ 𝒪 | g⁻¹ y ∈ 𝒪 ⊗ ℤ̂}`, a nonzero right ideal; it is principal, `I_g = x𝒪` (L4.7); then
`x⁻¹ g ∈ U₀(1)`: locally `g 𝒪_w = x 𝒪_w`, because every element of the local lattice `g𝒪_w` is
congruent modulo `N` to a global element of `I_g` (integer approximation at `w` with divisibility
at the finitely many bad places), and `N 𝒪_w ⊆ g 𝒪_w` for a common denominator `N` of `g⁻¹`.

*The class set of `U₁(9)`.* For `u ∈ U₀(1)` the coset `u U₁(9)` is determined by the bottom row of
`θ₃(u)⁻¹` modulo `9`, a primitive vector; left multiplication by a Hurwitz unit `γ` multiplies that
row on the right by `θ₃(γ)⁻¹`. The `24` units act on the `72` primitive vectors with three orbits,
represented by the bottom rows `(0, d_i⁻¹) = (0,1), (0,5), (0,7)` of `c_i⁻¹`, and trivial
stabilisers.

### Leaves — `Splitting.lean`

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
- **L15.3** `exists_sq_add_sq_eq_neg_one` — [RM] §0.1.3 "which exists by Hensel's lemma"; Examples
  "split at every odd prime". Lean: `∃ ν ξ : ℤ_[q], ν² + ξ² = −1` for `q` odd. Sketch: modulo `q`
  by `ZMod.sq_add_sq` (every element of `ZMod q` is a sum of two squares); one of the two is
  nonzero modulo `q`, say `ν₀`; `hensels_lemma` for `X² + ξ₀² + 1` at `ν₀`, derivative `2ν₀` a unit.
  Attacks: [2] `q = 2` excluded ✓ (L15.4 shows it must be). [5] both names verified. SURVIVED.
- **L15.4** `nrd_eq_zero_iff_of_padic_two`, `not_exists_sq_add_sq_eq_neg_one_padic_two` — [RM]
  Examples "ramified at `2` (the Hilbert symbol `(−1, −1)_q`)"; [Jac03, Lemma 1.19] (quoted). Lean:
  the reduced norm of `ℍ[ℚ_[2]]` is anisotropic. Sketch: scale a nontrivial zero to `ℤ₂⁴` with one
  odd coordinate; a sum of four squares with an odd term is `≢ 0 mod 8` (squares are `0, 1, 4`; the
  sums with at least one `1` are `1,…,7`). `decide` on `ZMod 8`. Attacks: [1] `1 + 1 + 1 + 1 = 4`,
  `1 + 1 + 1 + 4 = 7`, `1 + 1 + 4 + 4 = 2`, `1 + 4 + 4 + 4 = 5` mod 8 — none is `0` ✓. [4] the
  roadmap's "ramified" is rendered as "the base change is a division algebra" (anisotropic norm),
  the form L1.5 turns into `IsUnit x ↔ x ≠ 0`. SURVIVED.

### Leaves — `Setting.lean`

- **L16.1** `padicPlace`, `valued_natCast_padicPlace`, `valued_intCast_eq_one` — `q` is a
  uniformiser at the place `q` of `ℚ`. [SRC] `1_Setting.norm_three_lt_one`, `2_PadicEmbedding.
  norm_three_eq`. Sketch: `Rat.HeightOneSpectrum.natGenerator`, `span_natGenerator`,
  `valuedAdicCompletion_eq_valuation'`, `intValuation` of a generator. Attacks: [5] **known seam**
  ([SRC] module docstring): `Algebra ℚ (v.adicCompletion ℚ)` has two instance paths,
  `DivisionRing.toRatAlgebra` and the adic one, equal but not syntactically; the skeleton writes
  every rational cast as `((n : ℚ) : K)` through the adic coercion so that only one path occurs.
  SURVIVED.
- **L16.2** `exists_sq_add_sq_eq_neg_one_adicCompletion`, `rigidificationOfOdd` — [RM] Examples
  "`ℍ[ℚ]` split at every odd prime". L15.3 transported along `Padic.adicCompletionEquiv`
  (a ring isomorphism preserving integrality), then L15.2. SURVIVED.
- **L16.3** `exists_sqrt_neg_two`, `ν₃`, `sq_ν₃`, `valued_ν₃_sub_one`, `valued_ν₃`,
  `valued_ν₃_sub_twentyTwo` — [RM] §0.5 "`ν = √−2 ∈ ℤ_3` (the root that is `≡ 1 mod 3`)". Sketch:
  Hensel at `1` for `X² + 2` (`1 + 2 = 3 ≡ 0`, derivative `2`); `22² = 484 = −2 + 2·3⁵` and
  `ν₃ + 22 ≡ 2 mod 3` is a unit, so `v(ν₃ − 22) = v(ν₃² − 484) ≤ v(3)⁵ ≤ v(27)`. [SRC]
  `1_Setting.ν₃`, `5_Factorisations.norm_ν₃_sub_22`. Attacks: [2] `22 ≡ 1 mod 3` ✓ the right root.
  SURVIVED.
- **L16.4** `theta3` (the two proof fields), `toMatrix_unitsIncl` — [RM] §0.5 "the rigidification
  `θ₃` of §0.1.3". `ν₃² + 1² = −1`; `2` is a unit of the field `K₃`. `θ₃(x ⊗ 1) = splitHom ν₃ 1 x` by
  L15.2. SURVIVED.

### Leaves — `Level.lean`

- **L17.1** `hurwitzBasis`, `hurwitzBasis_apply`, `isOrderBasis_hurwitzBasis`,
  `orderOf_hurwitzBasis`, `unitsIncl_mem_U0_iff` — [RM] §0.5 "`𝒪_D` the Hurwitz order". The basis
  `1, i, j, ω`; structure constants from `ω² = ω − 1`, `iω = −1 − j + ω`, … (sixteen products, by
  `ext <;> norm_num`); `(algebraMap (𝓞 ℚ) ℚ).range = ℤ` (`Rat.ringOfIntegersEquiv`); L4.1.
  [SRC] `2_LevelTopology.hurwitzBasis`, `2_Level.mem_hurwitzOrder_iff_coords`. SURVIVED.
- **L17.2** `theta3_isIntegral` — [RM] §0.1.3 "carrying `𝒪_D ⊗ 𝒪_𝔭` onto `M₂(𝒪_𝔭)`". Sketch: `2` is
  a unit of `ℤ₃`, so `𝒪 ⊗ ℤ₃` has the `ℤ₃`-basis `1, i, j, k`; `θ₃` sends it to `1, I, J, IJ`,
  integral matrices (`ν₃` integral, L16.3) forming a `ℤ₃`-basis of `M₂(ℤ₃)` (substrate: coordinate
  determinant a unit). [SRC] `2_Level.theta_localOrder`. SURVIVED.
- **L17.3** `U1_9`, `valued_nine`, `mem_U1_9_iff`, `U1_9_le_U0`, `isCompact_U1_9`, `isOpen_U1_9`,
  `mem_U1_9_of_toGL` — [RM] §0.5 "`U₁(9)` has `3`-component
  `{((a b), (c d)) ∈ GL₂(ℤ_3) | 9 ∣ c, d ≡ 1 mod 9}`"; [Jac03, Definition 1.20, Proposition 1.21]
  (`jacobs_thesis.txt:525`, `:590`): "For all `n ∈ ℕ`, `U₀(pⁿ)` and `U₁(pⁿ)` are open compact
  subgroups of `D_f^×`." `U1Level` at `κ = Unit`; L12.3; `mem_U1_9_iff` by L9.8 (integrality and
  unit determinant are automatic on `U₀(1)`). Attacks: [4] Jacobs takes at `q = 2` "the group of
  units in any fixed maximal order of `D₂`"; ours is the local Hurwitz order, a maximal order ✓.
  SURVIVED.

### Leaves — `ClassNumberOne.lean`

- **L18.1** `exists_intCast_mul_mem_integralAdeles`, `exists_intCast_smul_toLocal_mem` — clearing
  denominators. [SRC] `CN1/3_AdeleIntegrality.exists_intCast_mul_mem_adicCompletionIntegers_forall`,
  `.exists_intCast_smul_toLocal_mem`. `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers`
  at each of the finitely many bad places, product of the integers. SURVIVED.
- **L18.2** `exists_intCast_approx` — integer approximation: `c ∈ ℤ_w` is congruent modulo `M` to an
  integer divisible by `M` at the places of `T ∌ w`. [SRC] `CN1/3_LocalApprox.exists_intCast_approx`
  (density of `ℤ` in `ℤ_w` and the Chinese remainder theorem in `ℤ`). SURVIVED.
- **L18.3** `denominatorIdeal` (fields), `denominatorIdeal_ne_bot` — [Voi21, Lemma 27.6.8]
  "we recover `I = α̂ Ô ∩ B`". [SRC] `CN1/4_Dictionary.latticeOf`, `.latticeOf_ne_bot`. Right
  `𝒪`-stability: `g⁻¹ (y r) = (g⁻¹ y) r` and `r ⊗ 1` is locally integral. Nonzero: a common
  denominator of `g⁻¹` (L18.1) lies in it. SURVIVED.
- **L18.4** `exists_mem_denominatorIdeal_sub_smul` — the local lattice is generated modulo `N` by
  global elements. [SRC] `CN1/4_Dictionary.exists_mem_latticeOf_sub_smul`: coordinates of `ξ` in
  the basis, L18.2 coordinatewise at modulus `N²` with `T` the bad places of `g⁻¹` away from `w`.
  Attacks: [3] the square is needed (slack that makes both the error at `w` and the approximations
  at `T` divisible by `N`) ✓ as in [SRC]. SURVIVED.
- **L18.5** `exists_eq_generator_mul`, `exists_factor_of_forall_mem`, `exists_factor` — [RM] §0.3.5
  "`D_f^× = D^× · U₀(1)` for `D = ℍ[ℚ]` with the Hurwitz order: every right ideal of a
  right-Euclidean order is principal (§0.1.4), and the idelic dictionary […] (Voight, Lemma 27.6.8)
  turns this into the triviality of the class set. ⚠ Jacobs (Lemma 1.22) derives this from the
  absence of weight-two cusp forms through Jacquet–Langlands; the route above is the one to
  formalise". [SRC] `CN1/4_Dictionary.exists_eq_generator_mul`, `.exists_factor_of_forall_mem`,
  `.hClassNumberOne` (sorry-free on standard axioms). Attacks: [4] **JL audit**: no leaf of this
  file, nor of its imports, mentions modular forms; the JL route of [Jac03] is quoted above only to
  be set aside ✓. SURVIVED.
- **L18.6** `subsingleton_classSet_U0`, `hasFiniteClassSets` — [RM] §0.5.1 "The class set of `U₀(1)`
  is trivial"; §0.3.2 (the conclusion of Fujisaki's lemma, for `ℍ[ℚ]`). L18.5; L13.3 with `U₀(1)`
  compact open. Attacks: [4] this is where plan.md decision 2 pays off: every open subgroup of
  `ℍ[ℚ]_f^×` has a finite class set with no Haar measure. SURVIVED.

### Leaves — `ClassSet.lean`

- **L19.1** `classDiag`, `diagGL` (field), `classRep` (two fields), `classRep_zero`,
  `toMatrix_classRep`, `classRep_mem_U0` — [RM] §0.5.2 "representatives `c_0 = 1`,
  `c_1 = ι_3(diag(5, 2))`, `c_2 = ι_3(diag(7, 4))` (Jacobs, Theorem 2.1)". L8.9, L9.8, L16.1.
  [SRC] `3_ClassSet.classRep`, `.toMatrix_classRep`, `.classRep_mem_U0`. SURVIVED.
- **L19.2** `redMod9`, `redMod9_intCast`, `redMod9_eq_zero_iff`, `redMod9_surjective`, `redMat`,
  `unitsMod9` — reduction modulo `9`. Sketch: `adicCompletionIntegers.padicIntEquiv` then
  `PadicInt.toZModPow 2`; `redMat` entrywise; `unitsMod9` is `redMat ∘ θ₃` on Hurwitz units (L17.2).
  [SRC] `3_ClassSet.redMod9`, `.redMat`, `.unitsMod9`. SURVIVED.
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
- **L19.5** `isCompleteFamily_classRep`, `isSection_classRep`, `card_classSet_U1_9` — [RM] §0.5.2
  "The class set of `U₁(9)` has three elements"; [Jac03, Theorem 2.1]. Sketch: `g = d u` with
  `u ∈ U₀(1)` (L18.5); the bottom row of `θ₃(u)⁻¹` is primitive; L19.4 gives `γ` and `i`, and
  `g = (d γ') c_i w` with `w ∈ U₁(9)` by L19.3. Distinctness from the uniqueness in L19.4. [SRC]
  `3_ClassSet.classRep_complete`, `.classRep_bijective`. SURVIVED.
- **L19.6** `stabilizer_classRep` — [RM] §0.5.3 "The three stabilisers `Γ_i` are trivial (Jacobs,
  Lemma 2.2)". Sketch: `u ∈ Γ_i` gives `γ = c_i u c_i⁻¹ ∈ D^× ∩ U₀(1)`, a Hurwitz unit (L17.1) with
  `(0, d_i⁻¹) γ̄ = (0, d_i⁻¹)`; L19.4. [SRC] `3_ClassSet.stabilizerAt_classRep`. SURVIVED.

### Leaves — `EtaDecomposition.lean`

- **L20.1** `three_ne_zero'`, `valued_three_lt_one`, `valued_le_valued_three`,
  `existsUnique_fin_three` — `3` is a uniformiser of `K₃` and `{0, 1, 2}` a residue system. L16.1;
  [SRC] `3_EtaDecomposition.exists_fin3_approx`, `.valued_sub_eq_one`. SURVIVED.
- **L20.2** `eta3`, `etaRep3`, `toMatrix_etaRep3`, `bijOn_etaRep3`, `etaRep3_injective` — [RM]
  §0.5.4 "`U₁(9) η_3 U₁(9) = ∐_{t ∈ {0,1,2}} U₁(9) · ι_3(((3 0), (9t 1)))` (Jacobs, Lemma 2.3)".
  L14.9 at `ϖ = 3`, `t = 2`, with L14.9's second statement for the lower hypothesis, L12.1 for
  `v(3)² = levelThreshold 2`, and L17.2. [SRC] `3_EtaDecomposition.bijOn_etaRep`. Attacks: [4] the
  representative matrix is `((3 0), (t·3² 1))`, equal to the roadmap's `((3 0), (9t 1))` ✓, and to
  [SRC] `toMatrix_etaRep` ✓ — so the factorisation table transfers verbatim. SURVIVED.

### Leaves — `Factorisations.lean`

- **L21.1** `hA`, `hB`, `hC`, their membership and norms, `third` (two fields), `sigmaTable`,
  `sigmaTable_ne`, `dTable`, `nrd_dTable` — [RM] §0.5.5 "`d(i, t) ∈ D^×` of reduced norm `1/3`
  (`± h / 3` for `h ∈ {1 + i − j, (−1 + i + 3j + k)/2, −(1 + 3i + j + k)/2}`),
  `σ = ((2, 1, 1), (0, 2, 2), (1, 0, 0))`". `ext <;> norm_num`; `decide`. [SRC]
  `5_Factorisations.dA`, `.dB`, `.dC`, `.sigmaTable`, `.dTable`. Attacks: [1] `nrd hB = ¼ + ¼ + 9/4 +
  ¼ = 3` ✓, `nrd hC = ¼ + 9/4 + ¼ + ¼ = 3` ✓. SURVIVED.
- **L21.2** `uCand`, `uCand_away` — away from `3`: `d⁻¹ = ± h̄` is a Hurwitz quaternion, and
  `d = ± h/3` is integral where `3` is a unit; the other factors have trivial components. [SRC]
  `5_Factorisations.uCand_away`. SURVIVED.
- **L21.3** `toGL_uCand_mem` — at `3`: nine explicit matrices `c_σ⁻¹ θ₃(d)⁻¹ c_i x_t⁻¹`, each
  integral with unit determinant, `9 ∣ c` and `d ≡ 1 mod 9`, checked with `ν₃ ≡ 22 mod 27` (L16.3).
  [SRC] `5_Factorisations.toMatrix_uCand₀₀ … ₂₂`, `sigma1_uCand…`. **The longest leaf of the board**:
  in [SRC] about `700` lines; its size is a property of the computation, not of the design. Attacks:
  [4] the conventions (`θ₃`, `c_i`, `x_t`, `d(i,t)`, `σ`) were compared with [SRC] one by one (L15.1,
  L19.1, L20.2, L21.1): identical, so the certificate is the one already verified there. SURVIVED.
- **L21.4** `uCand_mem`, `factorisation` — [RM] §0.5.5 "The nine factorisations
  `c_i · x_t^{−1} = d(i, t) · c_{σ(i,t)} · u(i, t)` […] `u(i, t) ∈ U₁(9)` (Jacobs, Lemmas 2.4–2.5 and
  §B.1)". L17.3's `mem_U1_9_of_toGL` with L21.2, L21.3; the equation holds by the definition of
  `uCand`. SURVIVED.

### Leaf — `Examples.lean`

- **L22.1** the `example`s — [RM] Layer 0, Examples: "the Hurwitz units […]; `U₀(1)` and `U₁(9)` are
  compact open; `D^× \ D_f^× / U₀(1)` is a point and `D^× \ D_f^× / U₁(9)` has three points;
  `Iw(3^2) η Iw(3^2)` splits into three right cosets; `diag(3, 1) ∈ M_t` is not a unit of `M_t`;
  `|nrd(γ)|_f = nrd(γ)^{−1}` for `γ ∈ ℍ[ℚ]^×`". All are one-line instances except the count of the
  cosets of `Iw(3²) η Iw(3²)`, which is `Set.ncard_image_of_injOn` on L11.13's `BijOn` with
  `Fin 3`. SURVIVED.

---

## Gate (Step 5): the seven conditions

1. **Every leaf discharged or sketched from named ingredients.** 106 Mathlib names are cited; 104
   elaborate (`scratchpad/names_of.lean`), and the two misses are replaced in the text
   (`isTotallyDisconnected_of_image`; `finprod_eq_prod_of_mulSupport_subset` + `Finset.prod_sdiff`,
   the latter pair to be verified at ticket time). Items flagged *for the ticket* rather than
   asserted: the defeq seam `𝒪[K]` versus `adicCompletionIntegers` (L6.2), total disconnectedness of
   `F_v` (L6.5), continuity of `RestrictedProduct.single` (L8.8), `IsModuleTopology` on `Matrix`
   (L8.5), and integrality through `minpoly` (L2.4, with a fallback). **One API gap needs its own
   development and is not developed here: Fujisaki's lemma (L13.2), carried as the class
   `HasFiniteClassSets` and discharged for `ℍ[ℚ]` (L18.6).**
2. **The Lean skeleton compiles.** The 21 library files built with `sorry` warnings only; the final
   build of `PhD.TauCeti.Code.OverconvergentForms.Examples` (which imports every other file) after
   the last edits succeeded on 2026-09-21: `Build completed successfully (8705 jobs)`, `sorry`
   warnings only, no file importing `PhD.Main.*`.
3. **Verbatim quotes.** Section substrates quote [Buz07] (`D_f`, `M_t`, wild level, `Γ_λ`,
   `U₀(𝔫)`/`U₁(𝔫)`, `[UηU]`, the coset decomposition), [Voi21] (3.2.9, 11.1.2 with its proof, §11.2,
   11.3.1, 11.3.2 with its proof, 11.3.4, 27.6.6–27.6.8, 27.6.12), [Loe11] (3.1.1, 3.1.2) and
   [Jac03] (§1.4, 1.18–1.22, the chain of bijections); the Jacobs extraction is font-damaged and the
   quotes restore `ν`, `ξ`, `×`, `⊗` by hand, which is said where it happens. Leaf-level sources are
   the roadmap clauses, quoted.
4. **Adversarial pass.** Every leaf has an attack block. Attacks that **succeeded** and changed a
   statement: L11.10 / L14.8 (the README's hypothesis on `U` is wrong; `Iw₁₁ ≤ U`), L11.13 / L14.9
   (`hr1`), L14.3 (`η⁻¹ U η`), L5.4 / L8.2 / L8.5 / L12.2 / L12.3 / L14.10 (unnecessary
   `Module.Finite` dropped; `RigidificationAt.moduleFinite` added). Attacks that added a leaf:
   L11.9. Roadmap looseness recorded without a statement change: L11.5 (integrality of `a`),
   L10.10 (the `F = ℚ` formula), L2.1 (`F →+* ℝ` for real places), L4.6 (Voight's left/right slip).
5. **Prior-B2 log.** Consulted, all boards; no name match; four shape lessons applied (top of this
   file). This board starts with an empty `b2_log.jsonl`.
6. **Structure.** The tree is the roadmap's numbered clauses; where [SRC] proves the same statement
   its proof is the sketch, and where it does not — the reduced norm (§0.1.1), definiteness, the
   idele norm and the norm class (§0.2.4), the general coset decomposition (§0.4.2), the general
   levels (§0.3.1), finiteness of units of a definite order (L13.6), splitting at every odd prime
   and ramification at `2` (L15.3–4) — the sketch is written out in the substrate.
7. **Single conclusion per declaration.** Conjunctive conclusions were removed (`localUnits`,
   `baseChangeEquiv_map`, the split integrality theorems). What remains are biconditionals whose
   right-hand sides are the defining conditions (`mem_monoidM_iff`, `mem_U1_9_iff`,
   `unitsIncl_mem_U0_iff`, `isSection_iff`, `mem_iwahori_iff`) and shared-witness existentials
   (`exists_factor`, `exists_mem_denominatorIdeal_sub_smul`, `exists_intCast_approx`), the
   documented exceptions.

No leaf is REVIEW-PENDING.

### Skeleton edits made by the adversarial pass (all applied)

| Leaf | Edit |
|---|---|
| L5.4, L8.2, L8.5, L12.2, L12.3, L14.10 | `[Module.Finite F D]` dropped; `RigidificationAt.moduleFinite` added (L8.4) |
| L11.9 | new leaf `inv_mul_etaGL_mul_mem_iwahoriPrincipal` |
| L11.10, L14.8 | hypothesis on `U`: `iwahoriPrincipal ≤ U ≤ iwahori` (README §0.4.2 corrected) |
| L11.13, L14.9 | `hr1 : ∀ i, Valued.v (r i) ≤ 1` added |
| L14.3 | index `(MulAut.conj η⁻¹ • U).relIndex U` (README §0.3.4 corrected) |
| L9.1, L9.6, L9.8, L17.3, L21.2 | `localUnits`; conjunctions replaced by one membership |
| L3.2 | one equation of `equivTuple`s instead of four conjuncts |
| L2.4 | moved from `Hurwitz.lean` to `Definite.lean`, generalised to definite `(a, b / ℚ)`, split in two |
| `Level/Local.lean` | `variable` + `include` replaced by explicit binders (prior-B2 lesson) |
