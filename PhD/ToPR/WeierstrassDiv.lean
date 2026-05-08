import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

variable {R : Type*} (v : R → ℝ)

def coeff_isUnit [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop := IsUnit (PowerSeries.coeff s f)

def norm_eq [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop :=
  PowerSeries.gaussNorm v c f = v (PowerSeries.coeff s f)

def norm_max_achiever [Semiring R] (f : PowerSeries R) (s : ℕ) : Prop :=
  ∀ t, s < t → v (PowerSeries.coeff s f) < v (PowerSeries.coeff s f)

structure distinguished [Semiring R] (c : ℝ) (f : PowerSeries R) (s : ℕ) : Prop where
  unit : coeff_isUnit f s
  norm_eq : norm_eq v c f s
  norm_max : norm_max_achiever v f s

variable [NormedCommRing R] [IsUltrametricDist R] {n : ℕ} (c : Fin (n + 1) → ℝ) [StrongPos c]

variable {c} in
abbrev distinguished_restricted (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c))
    (c 0)) (s : ℕ) : Prop :=
  distinguished (R := (MvPowerSeries.Restricted R (Fin.tail c))) norm (c 0) f.1 s

def distinguished_MvRestricted (f : (MvPowerSeries.Restricted R c)) (s : ℕ) : Prop :=
  distinguished_restricted (MvRestricted.finSuccEquiv R n c f) s

lemma weierstrassDivision_existance
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) :
    ∃ q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0),
    ∃ r : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)),
    ∃ h : Polynomial.degree r < s,
    f = g * q + (Polynomial.toRestricted (c 0) r) := by

  sorry

-- not sure if this is the best way to set up this unique condition?
lemma weierstrassDivision_unique
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) :
    ∃! q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0),
    ∃! r : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)),
    ∃ h : Polynomial.degree r < s,
    f = g * q + (Polynomial.toRestricted (c 0) r) := by

  sorry

lemma weierstrassDivision_bounds_q
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (r : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted (c 0) r)) :
    Restricted.gaussNorm _ (c 0) q ≤ (Restricted.gaussNorm _ (c 0) g)⁻¹ *
    (Restricted.gaussNorm _ (c 0) f) := by

  sorry

lemma weierstrassDivision_bounds_r
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (s : ℕ) (hg : distinguished_restricted g s)
    (f : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (q : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0))
    (r : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)))
    (hr : Polynomial.degree r < s)
    (hf : f = g * q + (Polynomial.toRestricted (c 0) r)) :
    Restricted.gaussNorm _ (c 0) (Polynomial.toRestricted (c 0) r) ≤
    Restricted.gaussNorm _ (c 0) f := by

  sorry

lemma weierstrassPreparation_exists
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) (s : ℕ) :
    ∃ ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)), ∃ hω : ω.Monic,
    ∃ e : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0),
    ∃ he : IsUnit e, g = e * (Polynomial.toRestricted (c 0) ω) := by

  sorry

lemma weierstrassPreparation_unique
    (g : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0)) (s : ℕ) :
    ∃! ω : Polynomial (MvPowerSeries.Restricted R (Fin.tail c)), ∃ hω : ω.Monic,
    ∃! e : PowerSeries.Restricted (MvPowerSeries.Restricted R (Fin.tail c)) (c 0),
    ∃ he : IsUnit e, g = e * (Polynomial.toRestricted (c 0) ω) := by

  sorry
