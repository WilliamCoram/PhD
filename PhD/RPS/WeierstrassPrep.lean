import PhD.RPS.mathlib
import PhD.GaussNorm.GN
import PhD.RPS.Restricted

open MvPowerSeries

variable (R : Type*) [NormedRing R] [IsUltrametricDist R] (v : R → ℝ)

noncomputable
instance isNormedRing (n : ℕ) : NormedRing (Restricted R (σ := Fin n) 1) :=
  RingNorm.toNormedRing (isRingNorm 1 (by aesop))

def coeff_isUnit {n : ℕ} (f : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1)) (s : ℕ) :
    Prop :=
  IsUnit (PowerSeries.coeff s f.1)

-- for now, but Ricardo may suggest not doing this and just using gaussNorm as prev but using
-- unit as σ!
noncomputable def
gaussNorm_powerSeries (T : Type*) [Semiring T] (v' : T → ℝ) (g : PowerSeries T) (d : ℝ) : ℝ :=
  ⨆ t : ℕ, v' (PowerSeries.coeff t g) * d ^ t

def gaussNorm_eq_gaussNorm {n : ℕ} (f : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1))
    (s : ℕ) : Prop :=
  -- gaussNorm of the coefficient gₛ in Tₙ
  gaussNorm v 1 (PowerSeries.coeff s f.1).1 =
  -- gaussNorm of g in Tₙ<X>
  gaussNorm_powerSeries (Restricted R (σ := Fin n) 1)
    (fun a : Restricted R (σ := Fin n)  1 => gaussNorm v 1 a.1) f.1 1

def gaussNorm_max_achiever {n : ℕ} (f : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1))
    (s : ℕ) : Prop :=
  -- gaussNorm of the coefficient gₛ in Tₙ is greater than later coefficients
  ∀ t, t > s → gaussNorm v 1 (PowerSeries.coeff s f.1).1 > gaussNorm v 1 (PowerSeries.coeff t f.1).1

  -- i.e. combined with gaussNorm_eq_gaussNorm; it is the latest coefficient that achieves the
  -- gaussNorm of g

-- X n-1 distinguished??
def Xₙ_distinguised {n : ℕ} (f : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1)) (s : ℕ)
    : Prop :=
  coeff_isUnit R f s ∧
  gaussNorm_eq_gaussNorm R v f s ∧
  gaussNorm_max_achiever R v f s

-- note I should probably introduce notation for all of this
-- e.g. Restricted = R<X_σ> c
-- PowerSeries.Restricted -> R<X> c


-- now I need to write a coercion from polynomials as restricted power series
-- should follow from:
-- polynomial → powerseries
-- polynomial → restristed proof


-- note comm ring is an unecessary assumption; which should be removed
lemma isRestricted_MvPolynomial {σ : Type*} [NormedCommRing R] (f : MvPolynomial σ R) (c : σ → ℝ) :
    IsRestricted R c (f : MvPowerSeries σ R) := by
  simp_rw [IsRestricted]
  -- the support of f is finite
  -- so certainly this is true
  sorry

-- but doing this removes Comm so keep using this for now
variable {R} in
lemma isRestricted_polynomial [NormedRing R] (f : Polynomial R) (c : ℝ) :
    PowerSeries.IsRestricted c (f : PowerSeries R) := by
  -- this is becoming a mess
  -- we have this is restricted iff it is restricted as an MvPowerSeries
  -- now this should follow from above?
  -- maybe? I could be typing everything horribly
  -- maybe Ricardo saying only define everything for mv makes sense here more
  sorry

lemma Weierstrass_division {n : ℕ}
    (g : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1))
    (s : ℕ) (h : Xₙ_distinguised _ v g s)
    (f : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1)) :
    ∃! (q : PowerSeries.Restricted 1 (R := Restricted R (σ := Fin n) 1)),
    ∃! (r : Polynomial (Restricted R (σ := Fin n) 1)), Polynomial.degree r < s ∧
    f = q * g + ⟨r, (isRestricted_polynomial (R := Restricted R (σ := Fin n) 1) r 1)⟩:= by

  sorry

lemma Weierstrass_preparation
