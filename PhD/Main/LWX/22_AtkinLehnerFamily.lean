/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«21_AtkinLehnerIdentityH»

/-!
# The Atkin–Lehner data at every classical weight

[LWX, §4.2] uses Step I / Prop 3.22 at **every** classical weight `(k, ψ)` of a given conductor:
"We look at weights of the form (k, ψ) for all k ≥ 0" (`lwx.txt:2322`), then "Replacing ψ by
ψω₀⁻¹ and k by k + 1" (`lwx.txt:2351`) and "for any character ω of Δ … Choose ψ so that
ψ|_Δ·ω₀^k = ω" (`lwx.txt:2356–2359`).  The unit-band hypothesis `HasUnitBand D ω n` at every
vertex `n` and every disc `ω`, which `13_SlopesSeam.lean`'s slope reading consumes, therefore needs
the adelic data (`AtkinLehnerData`) at every pair `(ω, k)` **with one and the same section
`ιp`** (so that the `U_p`-representatives, hence the `UpDatum`, do not depend on `(ω, k)`).

* `AtkinLehnerFamily θG ψ U Γ ζ` — one section `ιp` (with the level, `ιp_pGL_comm`, `central_pow`
  and `w`-normalisation properties of `AtkinLehnerData`) and, for every disc `ω` and exponent `k`, a
  Hecke character `χ ω k` restricting to the nebentypus `nebCharK ψ ω k ζ` on `U`
  (`ζ` a fixed primitive `p`-th root of unity, conductor `p²`).  `toData ω k` is the
  `AtkinLehnerData` at `(ω, k)`; `vRepD (toData ω k)` is `vRepF` definitionally.
* `AtkinLehnerFamilyH θG ψ U F h ζh` — the same at conductor `p^{h+1}` over the section of `F`
  (`ζh` a primitive `p^h`-th root of unity): `toDataH ω k : AtkinLehnerDataH …`.
* The partner-character arithmetic that (4.2.5)–(4.2.6) need: `partnerChar p ω (k+1) =
  partnerChar p ω k · ω₀²`, `partnerChar p (ω⁻¹ω₀^{2k}) k = ω`, and `ω₀^{p−1} = 1`
  (`lwx.txt:2361`: "since ω₀^{ϕ(q)} = 1"), in the form `ω·ω₀^{2·(p−1)/2} = ω` for odd `p`.

For a definite quaternion algebra over `ℚ` both families are constructed in
`23_QuaternionData.lean` (`QuaternionInput.atkinLehnerFamily` and its level-`h` twin); here the
fields are hypotheses.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)

/-! ### The level-`1` family -/

/-- **The Atkin–Lehner data at every classical weight of conductor `p²`**: one section `ιp` and a
Hecke character `χ ω k` for every disc `ω` and exponent `k`, restricting on `U` to the
nebentypus `nebCharK ψ ω k ζ` of the classical point `T_{χ_k}` on the disc `ω`. -/
structure AtkinLehnerFamily (Γ : Subgroup G) (ζ : K) where
  /-- A section `GL₂(ℚ_p) → G` of the `p`-component `θ`. -/
  ιp : GL (Fin 2) ℚ_[p] →* G
  theta_ιp : ∀ g, θG (ιp g) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p])
  /-- The level contains the lifts of the local Iwahori subgroup `Iw_p`. -/
  ιp_mem_U : ∀ g : GL (Fin 2) ℚ_[p], (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1 → ιp g ∈ U
  /-- The local central element `p·1` is central in `G` (it is a scalar at `p` and `1` away
  from `p`). -/
  ιp_pGL_comm : ∀ x, ιp (pGL p) * x = x * ιp (pGL p)
  /-- Some power of the central element `p` (at `p`) is a global central element times an element
  of the level with trivial `p`-component: `p_p^N = p^N_global · ((p^{(p)})^N)⁻¹` — true for every
  open tame level, since the tame scalars form a compact group. -/
  central_pow : ∃ N, 0 < N ∧ ∃ γ ∈ Γ, ∃ u ∈ U,
    ιp (pGL p) ^ N = γ * u ∧ θG u = 1 ∧ ∀ x, γ * x = x * γ
  /-- `w` normalises the disc-`0` part of the level. -/
  w_conj_mem_U : ∀ u ∈ U, ‖(θG u) 0 1‖ ≤ (p : ℝ)⁻¹ →
    ιp (wGL p) * u * (ιp (wGL p))⁻¹ ∈ U ∧ (ιp (wGL p))⁻¹ * u * ιp (wGL p) ∈ U
  /-- The Hecke character `ψ_A ∘ ν` of the classical weight `(k, ψ)` on the disc `ω`. -/
  χ : ((ZMod p)ˣ →* ℤ_[p]ˣ) → ℕ → G →* Kˣ
  χ_Γ : ∀ ω k, ∀ γ ∈ Γ, χ ω k γ = 1
  χ_U : ∀ ω k, ∀ u ∈ U, (χ ω k u : K) = nebCharK ψ ω k ζ (ψ (θG u).det)
  χ_vGL : ∀ ω k (c : ℚ_[p]), χ ω k (ιp (vGL p c)) = 1
  χ_wGL : ∀ ω k, χ ω k (ιp (wGL p)) = 1

variable {ζ : K} (F : AtkinLehnerFamily θG ψ U Γ ζ)

/-- The Atkin–Lehner data at one classical weight `(ω, k)`. -/
def AtkinLehnerFamily.toData (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    AtkinLehnerData θG ψ U Γ (nebCharK ψ ω k ζ) where
  ιp := F.ιp
  theta_ιp := F.theta_ιp
  ιp_mem_U := F.ιp_mem_U
  ιp_pGL_comm := F.ιp_pGL_comm
  central_pow := F.central_pow
  χ := F.χ ω k
  χ_Γ := F.χ_Γ ω k
  χ_U := F.χ_U ω k
  χ_vGL := F.χ_vGL ω k
  χ_wGL := F.χ_wGL ω k
  w_conj_mem_U := F.w_conj_mem_U

/-- The `U_p`-representatives of the family: `v_c = ιp (p 0; cp 1)`. -/
def vRepF (c : Fin p) : G := F.ιp (vGL p (c : ℕ))

/-- The `U_p`-element `η = ιp (p 0; 0 1)` of the family. -/
def upEltF : G := F.ιp (vGL p 0)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem vRepF_mem_levelM1 (c : Fin p) : vRepF θG ψ U F c ∈ levelM1 (p := p) θG :=
  vRepD_mem_levelM1 θG ψ U (AtkinLehnerFamily.toData θG ψ U F 1 0) c

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem upEltF_mem_levelM1 : upEltF θG ψ U F ∈ levelM1 (p := p) θG :=
  upEltD_mem_levelM1 θG ψ U (AtkinLehnerFamily.toData θG ψ U F 1 0)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The representatives of the data at `(ω, k)` are those of the family, definitionally. -/
@[simp] theorem vRepD_toData (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    vRepD θG ψ U (AtkinLehnerFamily.toData θG ψ U F ω k) = vRepF θG ψ U F :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem upEltD_toData (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    upEltD θG ψ U (AtkinLehnerFamily.toData θG ψ U F ω k) = upEltF θG ψ U F :=
  rfl

/-! ### The level-`h` family over the same section -/

variable (h : ℕ)

/-- **The Atkin–Lehner data at every classical weight of conductor `p^{h+1}`**, over the section
of a level-`1` family `F`: a Hecke character `χ ω k` for every `(ω, k)` restricting to
`nebCharKH h ψ ω k ζh` on `U`, and the level-`p^{h+1}` normalisation of `w_h`. -/
structure AtkinLehnerFamilyH (ζh : K) where
  /-- The Hecke character of the classical weight `(k, ψ)` of conductor `p^{h+1}` on the disc
  `ω`. -/
  χ : ((ZMod p)ˣ →* ℤ_[p]ˣ) → ℕ → G →* Kˣ
  χ_Γ : ∀ ω k, ∀ γ ∈ Γ, χ ω k γ = 1
  χ_U : ∀ ω k, ∀ u ∈ U, (χ ω k u : K) = nebCharKH h ψ ω k ζh (ψ (θG u).det)
  χ_vGL : ∀ ω k (c : ℚ_[p]), χ ω k (F.ιp (vGL p c)) = 1
  χ_wGLH : ∀ ω k, χ ω k (F.ιp (wGLH p h)) = 1
  /-- `w_h` normalises the level-`p^{h+1}` part of the level. -/
  w_conj_mem_U : ∀ u ∈ U, ‖(θG u) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h →
    F.ιp (wGLH p h) * u * (F.ιp (wGLH p h))⁻¹ ∈ U ∧ (F.ιp (wGLH p h))⁻¹ * u * F.ιp (wGLH p h) ∈ U

variable {h} {ζh : K} (X : AtkinLehnerFamilyH θG ψ U F h ζh)

/-- The level-`h` Atkin–Lehner data at one classical weight `(ω, k)`. -/
def AtkinLehnerFamilyH.toDataH (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    AtkinLehnerDataH θG ψ U h Γ (nebCharKH h ψ ω k ζh) where
  ιp := F.ιp
  theta_ιp := F.theta_ιp
  ιp_mem_U := F.ιp_mem_U
  ιp_pGL_comm := F.ιp_pGL_comm
  central_pow := F.central_pow
  χ := X.χ ω k
  χ_Γ := X.χ_Γ ω k
  χ_U := X.χ_U ω k
  χ_vGL := X.χ_vGL ω k
  χ_wGLH := X.χ_wGLH ω k
  w_conj_mem_U := X.w_conj_mem_U

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The representatives of the level-`h` data are those of the family, definitionally. -/
@[simp] theorem vRepDH_toDataH (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    vRepDH θG ψ U h (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k) = vRepF θG ψ U F :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem upEltDH_toDataH (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    upEltDH θG ψ U h (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k) = upEltF θG ψ U F :=
  rfl

/-! ### The partner characters, for (4.2.5)–(4.2.6) -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `invChar ω` is the group inverse of `ω` in `(ℤ/p)^× →* ℤ_p^×`. -/
theorem invChar_eq_inv (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : invChar ω = ω⁻¹ := by
  ext u
  simp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The partner disc at exponent `k + 1` is the partner disc at `k` times `ω₀²`
([LWX, §4.2]: "Replacing ψ by ψω₀⁻¹ and k by k + 1"). -/
theorem partnerChar_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    partnerChar p ω (k + 1) = partnerChar p ω k * teichChar p ^ 2 := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, partnerChar_apply, partnerChar_apply,
    teichChar_apply, mul_assoc, ← pow_add, mul_add, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Every disc is a partner disc: `partnerChar p (ω⁻¹ω₀^{2k}) k = ω`
([LWX, §4.2]: "Choose ψ so that ψ|_Δ·ω₀^k = ω"). -/
theorem partnerChar_invChar_mul_teichChar_pow (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    partnerChar p (invChar ω * teichChar p ^ (2 * k)) k = ω := by
  refine MonoidHom.ext fun r => ?_
  rw [partnerChar_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, teichChar_apply, invChar_apply,
    mul_inv, inv_inv, inv_mul_cancel_right]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ω₀^{p−1} = 1` ([LWX, §4.2]: "since ω₀^{ϕ(q)} = 1"): `teichRes` is multiplicative and
`r^{p−1} = 1` in `(ℤ/p)^×`. -/
theorem teichChar_pow_sub_one : teichChar p ^ (p - 1) = 1 := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ZMod.units_pow_card_sub_one_eq_one,
    map_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ω·ω₀^{2·(p−1)/2} = ω` for odd `p` ([LWX, Cor 1.4], `lwx.txt:168–169`: "since
`ω₀^{ϕ(q)} = 1`"). -/
theorem mul_teichChar_pow_two_mul_sub_one_div_two (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ω * teichChar p ^ (2 * ((p - 1) / 2)) = ω := by
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
  rw [show 2 * ((p - 1) / 2) = p - 1 by omega, teichChar_pow_sub_one]
  exact MonoidHom.ext fun r => by rw [MonoidHom.mul_apply, MonoidHom.one_apply, mul_one]

end LWX

end
