/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.Group.Basic
import PhD.TauCeti.Code.PadicFunctionalAnalysis.UnitBall
import PhD.TauCeti.Code.OverconvergentForms.Weight.Level
import PhD.TauCeti.Code.OverconvergentForms.Weight.Action
import PhD.TauCeti.Code.OverconvergentForms.Weight.Identity

/-!
# Analytic weights: characters with expansion data

A local field `L` (Buzzard's `F_𝔭`) is embedded into the coefficient field `K` along a finite
family `ι` of isometric embeddings (Buzzard's `I_𝔭 = Hom_{ℚ_p}(F_𝔭, K)`), carrying an integral basis
whose embedding matrix is invertible (`Embeddings`). The identity theorem on the integral points
`e(z) = (i(z))_{i ∈ ι}`, `z ∈ 𝒪_L`, is Buzzard's "`𝒪` is Zariski-dense in `B₁`".

An *expansion datum* for a character `n : 𝒪_L^× → K^×` at a level `(S, ρ)` assigns to every lower
row `(c, d)` of `S` a restricted series `col(c, d) ∈ K⟨z_i⟩` with row decay `ρ` that evaluates to
`n(cz + d)` at every `e(z)`; it is unique on the level by the identity theorem. An *analytic weight*
`κ = (n, v, col)` is a character `n` with an expansion datum and a norm-one character `v` of `L^×`
(Buzzard's `v`, extended by `v(ϖ) = 1`; see `extendUnits`). Its automorphy factor
`j_κ(γ) = v(det γ) · col(c, d)` satisfies the cocycle `j_κ(δγ) = j_κ(γ) · (j_κ(δ) ∘ w_γ)` —
*derived* here from the multiplicativity of `n` and `v` and the identity theorem, never assumed —
so that it is a weight datum, and the weight action `f ∣_κ γ` is the engine's; on points it is
Buzzard's `n(cz + d) v(det γ) f((az + b)/(cz + d))`, and it depends only on `(n, v)`.

[Buz07, §8, p. 62]: "Proposition 8.3. If `X` is a `K`-affinoid space and `n : 𝒪^× → 𝒪(X)^×` is a
continuous group homomorphism, then there is at least one `r ∈ 𝒩_K^×` and, for any such `r`, a
unique map of `K`-rigid spaces `β_r : B^×_r × X → 𝔾_m`, such that for all `α ∈ 𝒪^×`, `n(α)` is the
element of `𝒪(X)^×` corresponding […] to the map `X → 𝔾_m` obtained by evaluating `β_r` at the
`K`-valued point `α` of `B^×_r`. Definition. We call `β_r` a thickening of `n`." [Buz07, §8, p. 66]:
"Because we have only set up our Fredholm theory on Banach modules, we will have to somehow single
out one such thickening, which we do (rather arbitrarily) in the definition below." [Jac03,
Definition 1.27, p. 19]: "Note, that by `κ(cz + d)` we mean the power series expansion of
`κ(cz + d)` at zero."

## Main definitions

* `AutomorphicForm.Embeddings L K ι`: the embeddings with an integral basis;
  `Embeddings.self K`, `Embeddings.ofAlgHom`.
* `AutomorphicForm.Embeddings.evalPoint e z`: evaluation at `e(z)`, `z ∈ 𝒪_L`.
* `AutomorphicForm.ExpansionData e S ρ n`, `AutomorphicForm.AnalyticWeight e S ρ`.
* `AutomorphicForm.AnalyticWeight.kappaSlash`, `kappaSlashAction`, `restrict`.

## Main results

* `AutomorphicForm.Embeddings.eq_zero_of_forall_evalPoint_eq_zero`: the identity theorem on
  `e(𝒪_L)`.
* `AutomorphicForm.ExpansionData.col_eq_of_mem`: uniqueness of the expansion on the level.
* `AutomorphicForm.AnalyticWeight.autFactor_mul`: the derived cocycle.
* `AutomorphicForm.AnalyticWeight.evalPoint_kappaSlash`: the action on points.
* `AutomorphicForm.AnalyticWeight.kappaSlash_eq_of_n_eq`: the action depends only on `(n, v)`.
* `AutomorphicForm.AnalyticWeight.continuous_n`: the character of a weight is continuous.

Roadmap: §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8; README convention 3. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Expansion.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted Filter Topology

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ : Type*}

/-- Evaluation of a fixed restricted series is continuous in the point of the closed unit
polydisc: the series is the uniform limit of its polynomial truncations there. Source: PFA roadmap
§4.1.3 ("evaluation at the points of `R⁰` gives a bounded `R`-linear map `R⟨X⟩ → C(R⁰, R)`"). -/
theorem continuous_aeval_point (f : Restricted K (1 : σ → ℝ)) :
    Continuous fun x : {x : σ → K // ∀ i, ‖x i‖ ≤ 1} => aeval 1 x.1 x.2 f := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨s, hs⟩ := exists_finset_norm_sub_sum_monomial_lt 1 f hε
  refine ⟨fun x => ∑ t ∈ s, coeff t f.1 * t.prod fun i k => x.1 i ^ k, ?_, fun x => hεu ?_⟩
  · exact continuous_finsetSum s fun t _ => continuous_const.mul
      (continuous_finsetProd _ fun i _ => ((continuous_apply i).comp continuous_subtype_val).pow _)
  · have hP : aeval 1 x.1 x.2 (∑ t ∈ s, monomial 1 t (coeff t f.1)) =
        ∑ t ∈ s, coeff t f.1 * t.prod fun i k => x.1 i ^ k := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [aeval_monomial, Algebra.algebraMap_self_apply]
    calc dist (aeval 1 x.1 x.2 f) (∑ t ∈ s, coeff t f.1 * t.prod fun i k => x.1 i ^ k)
        = ‖aeval 1 x.1 x.2 (f - ∑ t ∈ s, monomial 1 t (coeff t f.1))‖ :=
          (dist_eq_norm _ _).trans (congrArg norm
            ((congrArg (aeval 1 x.1 x.2 f - ·) hP.symm).trans (map_sub _ _ _).symm))
      _ ≤ ‖f - ∑ t ∈ s, monomial 1 t (coeff t f.1)‖ := norm_aeval_le _ _
      _ < ε := hs

end MvPowerSeries.Restricted

namespace AutomorphicForm

variable {L : Type*} [NormedField L] [IsUltrametricDist L]
  {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The embeddings and the identity theorem on `e(𝒪_L)` -/

/-- **The embeddings** `I_𝔭 = Hom(F_𝔭, K)` of the local field into the coefficient field: a finite
family of isometric ring homomorphisms, together with an integral basis `b : ι → 𝒪_L` whose
embedding matrix `(i(b_β))_{i,β}` is invertible — the data Buzzard's proof of Proposition 8.3 uses
("a `ℤ_p`-basis `e_1, …, e_d` of `𝒪`" and "linear independence of distinct field embeddings").
Source: roadmap Layer 1 preamble and §1.2.3. -/
structure Embeddings (L K : Type*) [NormedField L] [NormedField K] (ι : Type*) [Fintype ι]
    [DecidableEq ι] where
  /-- The embeddings `i : L → K`. -/
  emb : ι → L →+* K
  /-- Each embedding is isometric. -/
  norm_emb : ∀ i x, ‖emb i x‖ = ‖x‖
  /-- An integral basis with invertible embedding matrix. -/
  exists_integralBasis : ∃ b : ι → L,
    (∀ β, ‖b β‖ ≤ 1) ∧ (Matrix.of fun i β => emb i (b β)).det ≠ 0

namespace Embeddings

variable (K) in
/-- The single embedding `K → K` (the case `F = ℚ`, `ι = {id}`). -/
def self : Embeddings K K Unit where
  emb _ := RingHom.id K
  norm_emb _ _ := rfl
  exists_integralBasis := ⟨fun _ => 1, fun _ => by simp, by simp⟩

/-- **Dedekind's lemma**: `[L : k] = |ι|` distinct `k`-algebra embeddings `L → K` over a
nontrivially normed base field `k` have an integral basis with invertible embedding matrix. Source:
[Buz07, p. 63] ("It is a standard fact (linear independence of distinct field embeddings) that the
continuous group homomorphisms `𝒪 → K` form a finite-dimensional `K`-vector space with basis the set
`I`"). -/
noncomputable def ofAlgHom {k : Type*} [NontriviallyNormedField k] [NormedAlgebra k L]
    [NormedAlgebra k K] [FiniteDimensional k L] (e : ι → (L →ₐ[k] K)) (he : Function.Injective e)
    (hcard : Fintype.card ι = Module.finrank k L) (hiso : ∀ i x, ‖e i x‖ = ‖x‖) :
    Embeddings L K ι where
  emb i := (e i : L →+* K)
  norm_emb := hiso
  exists_integralBasis := by
    classical
    let b' : Module.Basis ι k L :=
      (Module.finBasisOfFinrankEq k L hcard.symm).reindex (Fintype.equivFin ι).symm
    -- Dedekind: the embedding matrix of a basis is invertible
    have hdet : (Matrix.of fun i β => e i (b' β)).det ≠ 0 := by
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
      refine hv0 (funext fun i => ?_)
      have hinj : Function.Injective fun i => ((e i : L →+* K) : L →* K) := fun i j hij =>
        he (AlgHom.ext fun x => DFunLike.congr_fun hij x)
      refine Fintype.linearIndependent_iff.mp
        ((linearIndependent_monoidHom L K).comp _ hinj) v (funext fun x => ?_) i
      have hcol : ∀ β, ∑ i, v i * e i (b' β) = 0 := fun β => by
        simpa [Matrix.vecMul, dotProduct] using congrFun hv β
      have hx : ∀ i, e i x = ∑ β, algebraMap k K (b'.repr x β) * e i (b' β) := fun i => by
        conv_lhs => rw [← b'.sum_repr x]
        rw [map_sum]
        exact Finset.sum_congr rfl fun β _ => by rw [map_smul, Algebra.smul_def]
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      show ∑ i, v i * e i x = 0
      calc ∑ i, v i * e i x
          = ∑ i, ∑ β, algebraMap k K (b'.repr x β) * (v i * e i (b' β)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hx i, Finset.mul_sum]
            exact Finset.sum_congr rfl fun β _ => mul_left_comm _ _ _
        _ = ∑ β, algebraMap k K (b'.repr x β) * ∑ i, v i * e i (b' β) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun β _ => (Finset.mul_sum _ _ _).symm
        _ = 0 := Finset.sum_eq_zero fun β _ => by rw [hcol β, mul_zero]
    -- rescale the basis into the unit ball
    have hpos : 0 < 1 + ∑ β, ‖b' β‖ :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun β _ => norm_nonneg (b' β))
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt k (inv_pos.mpr hpos)
    refine ⟨fun β => a • b' β, fun β => ?_, ?_⟩
    · have hβ : ‖b' β‖ ≤ 1 + ∑ β, ‖b' β‖ := by
        have := Finset.single_le_sum (f := fun β => ‖b' β‖) (fun β _ => norm_nonneg (b' β))
          (Finset.mem_univ β)
        linarith
      rw [norm_smul]
      calc ‖a‖ * ‖b' β‖ ≤ (1 + ∑ β, ‖b' β‖)⁻¹ * (1 + ∑ β, ‖b' β‖) :=
            mul_le_mul ha.le hβ (norm_nonneg _) (inv_nonneg.mpr hpos.le)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    · show (Matrix.of fun i β => (e i : L →+* K) (a • b' β)).det ≠ 0
      have hM : (Matrix.of fun i β => (e i : L →+* K) (a • b' β)) =
          algebraMap k K a • Matrix.of fun i β => e i (b' β) := by
        ext i β
        simp [Algebra.smul_def]
      rw [hM, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).mpr (norm_pos_iff.mp ha0))) hdet

variable (e : Embeddings L K ι)

/-- The point `e(z) = (i(z))_{i ∈ ι}` of the closed unit polydisc, for `z ∈ 𝒪_L`. -/
def point (z : Subring.unitClosedBall L) : ι → K := fun i => e.emb i z

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_point_le_one (z : Subring.unitClosedBall L) (i : ι) : ‖e.point z i‖ ≤ 1 :=
  (e.norm_emb i z).trans_le (Subring.norm_le_one z)

/-- **Evaluation at an integral point** `e(z)`, `z ∈ 𝒪_L`. Source: roadmap §1.2.2 ("for every
`z ∈ 𝒪`, embedded as `(i(z))_i` in the closed unit polydisc of `K^{I_𝔭}`"). -/
noncomputable def evalPoint (z : Subring.unitClosedBall L) : Restricted K (1 : ι → ℝ) →ₐ[K] K :=
  aeval 1 (e.point z) (e.norm_point_le_one z)

@[simp] theorem evalPoint_X (z : Subring.unitClosedBall L) (i : ι) :
    e.evalPoint z (X K 1 i) = e.emb i z :=
  aeval_X _ i

theorem norm_evalPoint_le (z : Subring.unitClosedBall L) (f : Restricted K (1 : ι → ℝ)) :
    ‖e.evalPoint z f‖ ≤ ‖f‖ :=
  norm_aeval_le _ f

/-- **The identity theorem on `e(𝒪_L)`**: a restricted series vanishing at every integral point
`e(z)`, `z ∈ 𝒪_L`, is zero. Source: roadmap §1.2.3; [Buz07, pp. 63–64] ("that `𝒪` is Zariski-dense
in `B₁`"). -/
theorem eq_zero_of_forall_evalPoint_eq_zero [CharZero K] {f : Restricted K (1 : ι → ℝ)}
    (hf : ∀ z, e.evalPoint z f = 0) : f = 0 := by
  obtain ⟨b, hb1, hdet⟩ := e.exists_integralBasis
  refine eq_zero_of_forall_aeval_mulVec_natCast_eq_zero (M := Matrix.of fun i β => e.emb i (b β))
    (fun i β => (e.norm_emb i (b β)).trans_le (hb1 β)) hdet fun n => ?_
  -- the integral point `z = ∑ n_β b_β`
  have hz : ∑ β, (n β : L) * b β ∈ Subring.unitClosedBall L :=
    sum_mem fun β _ => mul_mem (natCast_mem _ (n β)) (Subring.mem_unitClosedBall.mpr (hb1 β))
  refine (aeval_congr (funext fun i => ?_) _ _ f).trans (hf ⟨_, hz⟩)
  show ∑ β, e.emb i (b β) * (n β : K) = e.emb i (∑ β, (n β : L) * b β)
  rw [map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_mul, map_natCast, mul_comm]

theorem ext_of_forall_evalPoint_eq [CharZero K] {f g : Restricted K (1 : ι → ℝ)}
    (h : ∀ z, e.evalPoint z f = e.evalPoint z g) : f = g :=
  sub_eq_zero.mp (e.eq_zero_of_forall_evalPoint_eq_zero fun z => by rw [map_sub, h z, sub_self])

/-- The multi-matrix `(i(γ))_{i ∈ ι}` of a matrix over `L`. Source: roadmap Layer 1 preamble
("For `γ ∈ M₂(F_𝔭)` and `i ∈ I_𝔭` write `γ_i := i(γ) ∈ M₂(K)`"). -/
def toMulti (g : Matrix (Fin 2) (Fin 2) L) : ι → Matrix (Fin 2) (Fin 2) K :=
  fun i => (e.emb i).mapMatrix g

omit [IsUltrametricDist L] [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem toMulti_apply (g : Matrix (Fin 2) (Fin 2) L) (i : ι) (j k : Fin 2) :
    e.toMulti g i j k = e.emb i (g j k) :=
  rfl

/-- `γ ↦ (i(γ))_i` is a monoid homomorphism. -/
def toMultiHom : Matrix (Fin 2) (Fin 2) L →* (ι → Matrix (Fin 2) (Fin 2) K) where
  toFun := e.toMulti
  map_one' := funext fun i => map_one (e.emb i).mapMatrix
  map_mul' g h := funext fun i => map_mul (e.emb i).mapMatrix g h

omit [IsUltrametricDist L] [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem toMultiHom_apply (g : Matrix (Fin 2) (Fin 2) L) : e.toMultiHom g = e.toMulti g :=
  rfl

omit [IsUltrametricDist L] [IsUltrametricDist K] [CompleteSpace K] in
/-- Level bounds transport along the isometric embeddings. -/
theorem multiBounds_toMulti {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    MultiBounds ρ (e.toMulti g) :=
  ⟨hb.rho_nonneg, hb.rho_lt_one, fun i j k => (e.norm_emb i _).trans_le (hb.integral hg j k),
    fun i => (e.norm_emb i _).trans_le (hb.c_le hg), fun i => (e.norm_emb i _).trans (hb.d_unit hg)⟩

end Embeddings

/-! ### The level acting on `𝒪_L` -/

variable (L) in
/-- The inclusion `𝒪_L^× → L^×`. -/
def unitsIncl : (Subring.unitClosedBall L)ˣ →* Lˣ :=
  Units.map (Subring.unitClosedBall L).subtype.toMonoidHom

@[simp] theorem coe_unitsIncl (u : (Subring.unitClosedBall L)ˣ) :
    ((unitsIncl L u : Lˣ) : L) = (u : Subring.unitClosedBall L) :=
  rfl

/-- The unit of `𝒪_L` given by an element of norm one. -/
noncomputable def unitOfNormEqOne (x : L) (hx : ‖x‖ = 1) : (Subring.unitClosedBall L)ˣ :=
  ((NormedRing.isUnit_iff_norm_eq_one (a := ⟨x, Subring.mem_unitClosedBall.mpr hx.le⟩)).mpr hx).unit

@[simp] theorem coe_unitOfNormEqOne (x : L) (hx : ‖x‖ = 1) :
    ((unitOfNormEqOne x hx : Subring.unitClosedBall L) : L) = x :=
  congrArg Subtype.val (IsUnit.unit_spec _)

namespace LevelBounds

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ} (hb : LevelBounds S ρ)

/-- The unit `c z + d ∈ 𝒪_L^×` of a level element at an integral point. Source: roadmap §1.2.2. -/
noncomputable def linUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) :
    (Subring.unitClosedBall L)ˣ :=
  unitOfNormEqOne (g 1 0 * z + g 1 1) (hb.norm_mul_add_eq_one hg (Subring.norm_le_one z))

@[simp] theorem coe_linUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) :
    ((hb.linUnit hg z : Subring.unitClosedBall L) : L) = g 1 0 * z + g 1 1 :=
  coe_unitOfNormEqOne _ _

/-- The unit `d ∈ 𝒪_L^×` of a level element. -/
noncomputable def dUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) : (Subring.unitClosedBall L)ˣ :=
  unitOfNormEqOne (g 1 1) (hb.d_unit hg)

/-- The Möbius image `γ · z = (a z + b)/(c z + d) ∈ 𝒪_L` of an integral point. Source: roadmap
§1.2.6 ("`col_δ ∘ w_γ` at `e(z)` is `col_δ` at `e(γ·z)`"); [Buz07, Lemma 8.1(b)]. -/
noncomputable def mobiusPt {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) :
    Subring.unitClosedBall L :=
  ⟨(g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1), by
    have := hb.norm_mul_add_eq_one hg (Subring.norm_le_one z)
    refine Subring.mem_unitClosedBall.mpr ?_
    rw [norm_div, this, div_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hb.integral hg 0 1))
    rw [norm_mul]
    exact mul_le_one₀ (hb.integral hg 0 0) (norm_nonneg _) (Subring.norm_le_one z)⟩

@[simp] theorem coe_mobiusPt {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) :
    ((hb.mobiusPt hg z : Subring.unitClosedBall L) : L) =
      (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) :=
  rfl

theorem mobiusPt_one (z : Subring.unitClosedBall L) : hb.mobiusPt S.one_mem z = z := by
  apply Subtype.ext
  rw [coe_mobiusPt]
  simp

/-- Möbius composition on integral points: `(δγ)·z = δ·(γ·z)`. -/
theorem mobiusPt_mul {g h : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hh : h ∈ S)
    (z : Subring.unitClosedBall L) :
    hb.mobiusPt (S.mul_mem hh hg) z = hb.mobiusPt hh (hb.mobiusPt hg z) := by
  have hw : (g 1 0 * z + g 1 1 : L) ≠ 0 := fun h0 => by
    simpa [h0] using hb.norm_mul_add_eq_one hg (Subring.norm_le_one z)
  apply Subtype.ext
  simp only [coe_mobiusPt, Matrix.mul_apply, Fin.sum_univ_two]
  rw [mul_div_assoc', mul_div_assoc', div_add' _ _ _ hw, div_add' _ _ _ hw,
    div_div_div_cancel_right₀ hw]
  congr 1 <;> ring

/-- **The automorphy cocycle in `𝒪_L^×`**: `c''z + d'' = (c'(γ·z) + d')(cz + d)` for
`δγ = ((a'' b''), (c'' d''))`. Source: roadmap §1.2.1 (`j(δγ, z) = j(γ, z) j(δ, γz)`). -/
theorem linUnit_mul {g h : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hh : h ∈ S)
    (z : Subring.unitClosedBall L) :
    hb.linUnit (S.mul_mem hh hg) z = hb.linUnit hh (hb.mobiusPt hg z) * hb.linUnit hg z := by
  have hw : (g 1 0 * z + g 1 1 : L) ≠ 0 := fun h0 => by
    simpa [h0] using hb.norm_mul_add_eq_one hg (Subring.norm_le_one z)
  have key : (h 1 0 * ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) + h 1 1) * (g 1 0 * z + g 1 1) =
      h 1 0 * (g 0 0 * z + g 0 1) + h 1 1 * (g 1 0 * z + g 1 1) := by
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hw]
  apply Units.ext
  apply Subtype.ext
  simp only [Units.val_mul, Subring.coe_mul, coe_linUnit, coe_mobiusPt, Matrix.mul_apply,
    Fin.sum_univ_two]
  rw [key]
  ring

theorem linUnit_one (z : Subring.unitClosedBall L) : hb.linUnit S.one_mem z = 1 := by
  apply Units.ext
  apply Subtype.ext
  simp

/-- The determinant of a level element, as a unit of `L`. -/
noncomputable def detUnits : S →* Lˣ where
  toFun g := Units.mk0 _ (hb.det_ne_zero g.2)
  map_one' := Units.ext Matrix.det_one
  map_mul' _ _ := Units.ext (Matrix.det_mul _ _)

omit [IsUltrametricDist L] in
@[simp] theorem coe_detUnits (g : S) : (hb.detUnits g : L) = (g : Matrix (Fin 2) (Fin 2) L).det :=
  rfl

/-- A level element as an element of `GL₂(L)`. -/
noncomputable def toGL : S →* GL (Fin 2) L where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hb.det_ne_zero g.2)
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

omit [IsUltrametricDist L] in
@[simp] theorem coe_toGL (g : S) : (hb.toGL g : Matrix (Fin 2) (Fin 2) L) = g :=
  rfl

end LevelBounds

namespace Embeddings

variable (e : Embeddings L K ι) {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  (hb : LevelBounds S ρ)

theorem evalPoint_lin {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L)
    (i : ι) : e.evalPoint z (lin (e.toMulti g) i) = e.emb i (hb.linUnit hg z) := by
  show aeval 1 (e.point z) (e.norm_point_le_one z) (lin (e.toMulti g) i) = _
  rw [aeval_lin, LevelBounds.coe_linUnit, map_add, map_mul]
  rfl

/-- The Möbius series at an integral point is the embedded Möbius image: `w_{γ,i}(e(z)) = i(γ·z)`.
Source: roadmap §1.2.6. -/
theorem evalPoint_mobius {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L)
    (i : ι) : e.evalPoint z (mobius (e.toMulti g) i) = e.emb i (hb.mobiusPt hg z) := by
  show aeval 1 (e.point z) (e.norm_point_le_one z) (mobius (e.toMulti g) i) = _
  rw [aeval_mobius (e.multiBounds_toMulti hb hg), LevelBounds.coe_mobiusPt, map_div₀, map_add,
    map_add, map_mul, map_mul]
  rfl

/-- `(f ∘ w_γ)(e(z)) = f(e(γ·z))`. Source: roadmap §1.2.6. -/
theorem evalPoint_mobiusSubst {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) (f : Restricted K (1 : ι → ℝ)) :
    e.evalPoint z (mobiusSubst (e.multiBounds_toMulti hb hg) f) =
      e.evalPoint (hb.mobiusPt hg z) f := by
  show aeval 1 (e.point z) (e.norm_point_le_one z) (mobiusSubst _ f) =
    aeval 1 (e.point (hb.mobiusPt hg z)) (e.norm_point_le_one _) f
  rw [aeval_mobiusSubst]
  exact aeval_congr (funext fun i => e.evalPoint_mobius hb hg z i) _ _ f

end Embeddings

/-! ### Expansion data -/

/-- **An expansion datum** for a character `n : 𝒪_L^× → K^×` at the level `(S, ρ)`: for every
lower row `(c, d)` of `S`, a restricted series `col(c, d) ∈ K⟨z_i⟩` with `‖coeff_m col‖ ≤ ρ^{|m|}`
evaluating to `n(cz + d)` at every integral point `e(z)`. This is Jacobs's "power series expansion
of `κ(cz + d)`" and Buzzard's thickening, carried as data (README convention 3). Source: roadmap
§1.2.2. -/
structure ExpansionData (e : Embeddings L K ι) (S : Submonoid (Matrix (Fin 2) (Fin 2) L)) (ρ : ℝ)
    (n : (Subring.unitClosedBall L)ˣ →* Kˣ) where
  /-- The level bounds. -/
  bounds : LevelBounds S ρ
  /-- The expansion `col(c, d)` of `n(cz + d)`. -/
  col : L → L → Restricted K (1 : ι → ℝ)
  /-- Row decay at the level. -/
  rowBound_col : ∀ {g}, g ∈ S → RowBound ρ (col (g 1 0) (g 1 1))
  /-- The expansion evaluates to the character at every integral point. -/
  evalPoint_col : ∀ {g} (hg : g ∈ S) (z : Subring.unitClosedBall L),
    e.evalPoint z (col (g 1 0) (g 1 1)) = n (bounds.linUnit hg z)

namespace ExpansionData

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  {n : (Subring.unitClosedBall L)ˣ →* Kˣ} (E : ExpansionData e S ρ n)

theorem norm_col_le_one {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    ‖E.col (g 1 0) (g 1 1)‖ ≤ 1 :=
  (E.rowBound_col hg).norm_le_one E.bounds.rho_nonneg E.bounds.rho_lt_one.le

/-- **Uniqueness of the expansion on the level**: two expansion data for the same character agree
on every lower row of `S`, by the identity theorem. Source: roadmap §1.2.3. -/
theorem col_eq_of_mem [CharZero K] (E₁ E₂ : ExpansionData e S ρ n) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) : E₁.col (g 1 0) (g 1 1) = E₂.col (g 1 0) (g 1 1) :=
  e.ext_of_forall_evalPoint_eq fun z => (E₁.evalPoint_col hg z).trans (E₂.evalPoint_col hg z).symm

/-- The expansion at the identity is `1`. -/
theorem col_one [CharZero K] : E.col 0 1 = 1 := by
  refine e.ext_of_forall_evalPoint_eq fun z => ?_
  have h := E.evalPoint_col S.one_mem z
  have h10 : (1 : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have h11 : (1 : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := Matrix.one_apply_eq 1
  rw [E.bounds.linUnit_one z, map_one, Units.val_one, h10, h11] at h
  rw [h, map_one]

/-- **Restriction** to a smaller level and a larger radius. ⚠ A smaller radius at a deeper level is
not formal (roadmap §1.2.8). -/
def restrict {S' : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hS : S' ≤ S) {ρ' : ℝ} (hρρ' : ρ ≤ ρ')
    (hρ' : ρ' < 1) : ExpansionData e S' ρ' n where
  bounds := (E.bounds.mono hS).mono_radius hρρ' hρ'
  col := E.col
  rowBound_col hg := (E.rowBound_col (hS hg)).mono E.bounds.rho_nonneg hρρ'
  evalPoint_col hg z := E.evalPoint_col (hS hg) z

end ExpansionData

/-! ### Analytic weights -/

/-- **An analytic weight** at level `(S, ρ)`: Buzzard's `κ = (n, v)` with the thickening of `n` made
explicit — a character `n` of `𝒪_L^×` with an expansion datum, and a norm-one character `v` of
`L^×` (Buzzard's `v`, extended from `𝒪_L^×` by `v(ϖ) = 1`; `extendUnits` builds it). Source: roadmap
§1.2.2; [Buz07, §10, p. 71] ("the supremum semi-norm of every element in the image of `n` or `v`
is `1`"). -/
structure AnalyticWeight (e : Embeddings L K ι) (S : Submonoid (Matrix (Fin 2) (Fin 2) L)) (ρ : ℝ)
    where
  /-- The character `n`. -/
  n : (Subring.unitClosedBall L)ˣ →* Kˣ
  /-- The character `v`, entering only through `v(det γ)`. -/
  v : Lˣ →* Kˣ
  /-- `v` takes values of norm one. -/
  norm_v : ∀ x, ‖(v x : K)‖ = 1
  /-- The expansion datum of `n`. -/
  expansion : ExpansionData e S ρ n

namespace AnalyticWeight

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  (κ : AnalyticWeight e S ρ)

theorem bounds (κ : AnalyticWeight e S ρ) : LevelBounds S ρ := κ.expansion.bounds

/-- The character `γ ↦ v(det γ)` of the level. Source: roadmap §1.2.8. -/
noncomputable def detChar : S →* Kˣ := κ.v.comp κ.expansion.bounds.detUnits

theorem detChar_apply (γ : S) : κ.detChar γ = κ.v (κ.expansion.bounds.detUnits γ) :=
  rfl

theorem norm_detChar (γ : S) : ‖(κ.detChar γ : K)‖ = 1 :=
  κ.norm_v _

/-- **The automorphy factor** `j_κ(γ) = v(det γ) · col(c, d)`. Source: roadmap §1.2.4. -/
noncomputable def autFactor (γ : S) : Restricted K (1 : ι → ℝ) :=
  (κ.detChar γ : K) • κ.expansion.col ((γ : Matrix (Fin 2) (Fin 2) L) 1 0)
    ((γ : Matrix (Fin 2) (Fin 2) L) 1 1)

theorem rowBound_autFactor (γ : S) : RowBound ρ (κ.autFactor γ) :=
  (κ.expansion.rowBound_col γ.2).smul (κ.norm_detChar γ).le

/-- The automorphy factor at an integral point: `j_κ(γ)(e(z)) = v(det γ) n(cz + d)`. -/
theorem evalPoint_autFactor (γ : S) (z : Subring.unitClosedBall L) :
    e.evalPoint z (κ.autFactor γ) = (κ.detChar γ : K) * κ.n (κ.expansion.bounds.linUnit γ.2 z) := by
  rw [autFactor, map_smul, κ.expansion.evalPoint_col γ.2 z, smul_eq_mul]

theorem autFactor_one [CharZero K] : κ.autFactor 1 = 1 := by
  have h10 : ((1 : S) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp
  have h11 : ((1 : S) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp
  rw [autFactor, map_one, Units.val_one, one_smul, h10, h11]
  exact κ.expansion.col_one

/-- **The cocycle, derived**: `j_κ(δγ) = j_κ(γ) · (j_κ(δ) ∘ w_γ)`. Both sides are restricted series
agreeing at every integral point `e(z)` — by Möbius composition, the multiplicativity of `n` and
`v`, and `det(δγ) = det δ det γ` — hence equal by the identity theorem. ⚠ This is the only place a
character is analysed. Source: roadmap §1.2.6. -/
theorem autFactor_mul [CharZero K] (γ δ : S) :
    κ.autFactor (δ * γ) =
      κ.autFactor γ *
        mobiusSubst (e.multiBounds_toMulti κ.expansion.bounds γ.2) (κ.autFactor δ) := by
  refine e.ext_of_forall_evalPoint_eq fun z => ?_
  have hlin : κ.expansion.bounds.linUnit (δ * γ).2 z =
      κ.expansion.bounds.linUnit δ.2 (κ.expansion.bounds.mobiusPt γ.2 z) *
        κ.expansion.bounds.linUnit γ.2 z :=
    κ.expansion.bounds.linUnit_mul γ.2 δ.2 z
  rw [map_mul, e.evalPoint_mobiusSubst κ.expansion.bounds γ.2, κ.evalPoint_autFactor (δ * γ) z,
    κ.evalPoint_autFactor γ z, κ.evalPoint_autFactor δ, hlin]
  simp only [map_mul, Units.val_mul]
  ring

/-- The weight datum of an analytic weight. Source: roadmap §1.2.6. -/
noncomputable def toWeightData [CharZero K] : WeightData S K ι ρ where
  toMulti := e.toMultiHom.comp S.subtype
  bounds γ := e.multiBounds_toMulti κ.expansion.bounds γ.2
  autFactor := κ.autFactor
  rowBound_autFactor := κ.rowBound_autFactor
  autFactor_one := κ.autFactor_one
  autFactor_mul := κ.autFactor_mul

@[simp] theorem toWeightData_toMulti [CharZero K] (γ : S) :
    κ.toWeightData.toMulti γ = e.toMulti γ :=
  rfl

@[simp] theorem toWeightData_autFactor [CharZero K] (γ : S) :
    κ.toWeightData.autFactor γ = κ.autFactor γ :=
  rfl

/-- **The weight-`κ` action** `f ∣_κ γ`. Source: roadmap §1.2.5; [Buz07, §10, p. 72]; [Jac03,
Definition 1.27]. -/
noncomputable def kappaSlash [CharZero K] (γ : S) :
    Restricted K (1 : ι → ℝ) →L[K] Restricted K (1 : ι → ℝ) :=
  κ.toWeightData.kappaSlash γ

theorem kappaSlash_apply [CharZero K] (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    κ.kappaSlash γ f =
      κ.autFactor γ * mobiusSubst (e.multiBounds_toMulti κ.expansion.bounds γ.2) f :=
  rfl

theorem kappaSlash_one [CharZero K] : κ.kappaSlash 1 = ContinuousLinearMap.id K _ :=
  κ.toWeightData.kappaSlash_one

theorem kappaSlash_mul [CharZero K] (γ δ : S) :
    κ.kappaSlash (δ * γ) = (κ.kappaSlash γ).comp (κ.kappaSlash δ) :=
  κ.toWeightData.kappaSlash_mul γ δ

theorem norm_kappaSlash_apply_le [CharZero K] (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    ‖κ.kappaSlash γ f‖ ≤ ‖f‖ :=
  κ.toWeightData.norm_kappaSlash_apply_le γ f

theorem kappaSlash_monomial [CharZero K] (γ : S) (r : ι →₀ ℕ) :
    κ.kappaSlash γ (monomial 1 r 1) =
      κ.autFactor γ * r.prod fun i k => mobius (e.toMulti γ) i ^ k :=
  κ.toWeightData.kappaSlash_monomial γ r

/-- **The row bound** (§1.2.4): `‖a‖ ≤ σ` and `ρ ≤ σ` give `‖coeff_t (z^r ∣_κ γ)‖ ≤ σ^{|t|}`. -/
theorem norm_coeff_kappaSlash_monomial_le [CharZero K] (γ : S) {σ : ℝ} (hρσ : ρ ≤ σ)
    (ha : ‖(γ : Matrix (Fin 2) (Fin 2) L) 0 0‖ ≤ σ) (t r : ι →₀ ℕ) :
    ‖coeff t (κ.kappaSlash γ (monomial 1 r 1)).1‖ ≤ σ ^ t.degree :=
  κ.toWeightData.norm_coeff_kappaSlash_monomial_le γ hρσ (fun i => by
    simpa [e.norm_emb] using ha) t r

/-- **The action on points** (Buzzard's definition):
`(f ∣_κ γ)(e(z)) = n(cz + d) v(det γ) f(e(γ·z))`. Source: roadmap §1.2.5; [Buz07, §10, p. 72]. -/
theorem evalPoint_kappaSlash [CharZero K] (γ : S) (f : Restricted K (1 : ι → ℝ))
    (z : Subring.unitClosedBall L) :
    e.evalPoint z (κ.kappaSlash γ f) =
      (κ.n (κ.expansion.bounds.linUnit γ.2 z) : K) * (κ.detChar γ : K) *
        e.evalPoint (κ.expansion.bounds.mobiusPt γ.2 z) f := by
  rw [kappaSlash_apply, map_mul, κ.evalPoint_autFactor,
    e.evalPoint_mobiusSubst κ.expansion.bounds γ.2]
  ring

/-- The action depends only on the characters `(n, v)`, not on the expansion datum. Source: roadmap
§1.2.3, §1.2.6. -/
theorem kappaSlash_eq_of_n_eq [CharZero K] (κ' : AnalyticWeight e S ρ) (hn : κ.n = κ'.n)
    (hv : κ.v = κ'.v) (γ : S) : κ.kappaSlash γ = κ'.kappaSlash γ := by
  obtain ⟨n, v, hv1, E⟩ := κ
  obtain ⟨n', v', hv1', E'⟩ := κ'
  dsimp only at hn hv
  subst hn hv
  refine ContinuousLinearMap.ext fun f => ?_
  exact congrArg (fun c => ((v (E.bounds.detUnits γ) : Kˣ) : K) • c *
    mobiusSubst (e.multiBounds_toMulti E.bounds γ.2) f) (ExpansionData.col_eq_of_mem E E' γ.2)

/-- **The right action** of the level on the Tate algebra (README convention 2). -/
@[instance_reducible]
noncomputable def kappaSlashAction [CharZero K] :
    DistribMulAction Sᵐᵒᵖ (Restricted K (1 : ι → ℝ)) :=
  κ.toWeightData.kappaSlashAction

/-- **Restriction** to a smaller level and a larger radius. Source: roadmap §1.2.8. -/
noncomputable def restrict {S' : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hS : S' ≤ S) {ρ' : ℝ}
    (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) : AnalyticWeight e S' ρ' where
  n := κ.n
  v := κ.v
  norm_v := κ.norm_v
  expansion := κ.expansion.restrict hS hρρ' hρ'

theorem kappaSlash_restrict [CharZero K] {S' : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hS : S' ≤ S)
    {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) (γ : S') :
    (κ.restrict hS hρρ' hρ').kappaSlash γ = κ.kappaSlash ⟨γ, hS γ.2⟩ :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The character of a weight is continuous as soon as the level contains a lower unipotent
`((1 0), (c 1))`, `c ≠ 0`: `n(1 + cz) = col(c, 1)(e(z))` is continuous in `z`, so `n` is continuous
on the open subgroup `1 + c𝒪_L`. (The roadmap asks for a continuous character; continuity is a
consequence of the expansion data, not an extra field.) Source: roadmap §1.2.2. -/
theorem continuous_n (hc : ∃ c : L, c ≠ 0 ∧ !![1, 0; c, 1] ∈ S) : Continuous κ.n := by
  obtain ⟨c, hc0, hcS⟩ := hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  refine continuous_of_continuousAt_one κ.n ?_
  refine Units.isEmbedding_val₀.isInducing.continuousAt_iff.mpr ?_
  -- the open neighbourhood `‖u - 1‖ < ‖c‖` of `1`
  let V : Set (Subring.unitClosedBall L)ˣ :=
    {u | ‖((u : Subring.unitClosedBall L) : L) - 1‖ < ‖c‖}
  have hVo : IsOpen V := isOpen_lt (continuous_norm.comp
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)) continuous_const
  have h1V : (1 : (Subring.unitClosedBall L)ˣ) ∈ V := by simpa [V] using hcpos
  refine ContinuousOn.continuousAt ?_ (hVo.mem_nhds h1V)
  rw [continuousOn_iff_continuous_domRestrict]
  -- on `V`, `u = c z + 1` with `z = (u - 1)/c ∈ 𝒪_L`
  have hz : ∀ u : V,
      ((((u : (Subring.unitClosedBall L)ˣ) : Subring.unitClosedBall L) : L) - 1) / c ∈
        Subring.unitClosedBall L := fun u => by
    rw [Subring.mem_unitClosedBall, norm_div]
    exact (div_le_one hcpos).mpr u.2.le
  let z : V → Subring.unitClosedBall L := fun u => ⟨_, hz u⟩
  have hzc : Continuous z := ((((continuous_subtype_val.comp Units.continuous_val).comp
    continuous_subtype_val).sub continuous_const).div_const c).subtype_mk _
  have hemb : ∀ i, Continuous (e.emb i) := fun i =>
    (AddMonoidHomClass.isometry_of_norm (e.emb i) (e.norm_emb i)).continuous
  have hpt : Continuous fun u : V =>
      (⟨e.point (z u), e.norm_point_le_one (z u)⟩ : {x : ι → K // ∀ i, ‖x i‖ ≤ 1}) :=
    (continuous_pi fun i => (hemb i).comp (continuous_subtype_val.comp hzc)).subtype_mk _
  refine ((continuous_aeval_point (κ.expansion.col c 1)).comp hpt).congr fun u => ?_
  -- `n(u) = n(c z + 1) = col(c, 1)(e(z))`
  have hlin : κ.expansion.bounds.linUnit hcS (z u) = u := by
    refine Units.ext (Subtype.ext ?_)
    rw [LevelBounds.coe_linUnit]
    show c * (((((u : (Subring.unitClosedBall L)ˣ) : Subring.unitClosedBall L) : L) - 1) / c) + 1 =
      _
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hc0, sub_add_cancel]
  exact (κ.expansion.evalPoint_col hcS (z u)).trans (congrArg (fun w => (κ.n w : K)) hlin)

end AnalyticWeight

end AutomorphicForm
