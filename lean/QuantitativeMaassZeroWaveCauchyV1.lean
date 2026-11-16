module

public import QuantitativeMaassZeroWaveCosineV1
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace QuantitativeMaass.ZeroWave

def waveValue (a : ℝ → ℂ) (t u : ℝ) : ℂ := a (u+t)+a (u-t)

def schwartzWave (a : 𝓢(ℝ,ℂ)) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  a.compSubConstCLM ℂ (-t)+a.compSubConstCLM ℂ t

theorem schwartzWave_apply (a : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    schwartzWave a t u=waveValue a t u := by
  simp [schwartzWave,waveValue,sub_neg_eq_add]

theorem shift_toLp (a : 𝓢(ℝ,ℂ)) (t : ℝ) :
    shift t (a.toLp 2)=(a.compSubConstCLM ℂ (-t)).toLp 2 := by
  apply Lp.ext
  have ha := (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae_eq_comp
    (a.coeFn_toLp 2)
  filter_upwards [shift_ae t (a.toLp 2),ha,(a.compSubConstCLM ℂ (-t)).coeFn_toLp 2]
    with u hu hau hbu
  rw [hu,hbu]
  simpa [sub_neg_eq_add] using hau

/-- On the dense Schwartz core, the bounded wave operator has the actual
smooth d'Alembert representative. -/
theorem wave_toLp (a : 𝓢(ℝ,ℂ)) (t : ℝ) : wave t (a.toLp 2)=(schwartzWave a t).toLp 2 := by
  change shift t (a.toLp 2)+shift (-t) (a.toLp 2)=_
  rw [shift_toLp,shift_toLp,neg_neg]
  exact (map_add (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume) _ _).symm

theorem waveValue_timeDerivative (a a' : ℝ → ℂ)
    (ha : ∀ u, HasDerivAt a (a' u) u) (t u : ℝ) :
    HasDerivAt (fun v => waveValue a v u) (a' (u+t)-a' (u-t)) t := by
  have hp := (ha (u+t)).scomp t ((hasDerivAt_id t).const_add u)
  have hm := (ha (u-t)).scomp t ((hasDerivAt_id t).const_sub u)
  convert hp.add hm using 1
  · funext v
    rfl
  · simp [sub_eq_add_neg]

theorem waveValue_spaceDerivative (a a' : ℝ → ℂ)
    (ha : ∀ u, HasDerivAt a (a' u) u) (t u : ℝ) :
    HasDerivAt (waveValue a t) (a' (u+t)+a' (u-t)) u := by
  have hp := (ha (u+t)).scomp u ((hasDerivAt_id u).add_const t)
  have hm := (ha (u-t)).scomp u ((hasDerivAt_id u).sub_const t)
  convert hp.add hm using 1
  · funext v
    rfl
  · simp

/-- The actual smooth representative satisfies the free one-dimensional
wave equation; this is proved by differentiating the explicit translations. -/
theorem waveValue_equation (a a' a'' : ℝ → ℂ)
    (ha : ∀ u, HasDerivAt a (a' u) u) (ha' : ∀ u, HasDerivAt a' (a'' u) u)
    (t u : ℝ) :
    deriv (deriv (fun v => waveValue a v u)) t=deriv (deriv (waveValue a t)) u := by
  have ht : deriv (fun v => waveValue a v u)=fun v => a' (u+v)-a' (u-v) :=
    funext fun v => (waveValue_timeDerivative a a' ha v u).deriv
  have hu : deriv (waveValue a t)=waveValue a' t :=
    funext fun v => (waveValue_spaceDerivative a a' ha t v).deriv
  rw [ht,hu,(waveValue_spaceDerivative a' a'' ha' t u).deriv]
  have hp := (ha' (u+t)).scomp t ((hasDerivAt_id t).const_add u)
  have hm := (ha' (u-t)).scomp t ((hasDerivAt_id t).const_sub u)
  have h : HasDerivAt (fun v => a' (u+v)-a' (u-v))
      (a'' (u+t)+a'' (u-t)) t := by
    convert hp.sub hm using 1
    · funext v
      rfl
    · simp
  exact h.deriv

theorem waveValue_initial (a : ℝ → ℂ) (u : ℝ) : waveValue a 0 u=2*a u := by
  simp [waveValue,two_mul]

theorem waveValue_initialVelocity (a a' : ℝ → ℂ)
    (ha : ∀ u, HasDerivAt a (a' u) u) (u : ℝ) :
    deriv (fun t => waveValue a t u) 0=0 := by
  simpa using (waveValue_timeDerivative a a' ha 0 u).deriv

/-- The actual Schwartz representative of the bounded L² wave satisfies
the PDE, with no separate derivative hypotheses on the initial vector. -/
theorem schwartzWave_equation (a : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    deriv (deriv (fun v => schwartzWave a v u)) t =
      deriv (deriv (fun v => schwartzWave a t v)) u := by
  simp_rw [schwartzWave_apply]
  have hc : ContDiff ℝ 1 (deriv a) :=
    (contDiff_succ_iff_deriv.mp (a.smooth 2)).2.2
  exact waveValue_equation a (deriv a) (deriv (deriv a))
    (fun v => (a.differentiable v).hasDerivAt)
    (fun v => (hc.differentiable one_ne_zero v).hasDerivAt) t u

#print axioms schwartzWave_equation
#print axioms wave_toLp
#print axioms waveValue_equation
#print axioms waveValue_initialVelocity

end QuantitativeMaass.ZeroWave
