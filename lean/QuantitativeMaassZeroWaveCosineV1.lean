module

public import QuantitativeMaassZeroWaveTranslationV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace QuantitativeMaass.ZeroWave

/-- The actual zero-channel wave multiplier 2 cos(t sqrt(-d²/du²)),
constructed directly as the sum of the two translation operators. The name
records the classical d'Alembert formula, not an assumed spectral calculus. -/
def wave (t : ℝ) : Space →L[ℂ] Space := shift t+shift (-t)

def cosine (t : ℝ) : Space →L[ℂ] Space := (1/2:ℂ) • wave t

theorem wave_selfAdjoint (t : ℝ) : IsSelfAdjoint (wave t) := by
  change (wave t).adjoint=wave t
  simp only [wave,map_add,shift_adjoint,neg_neg]
  exact add_comm _ _

theorem wave_norm_apply_le (t : ℝ) (a : Space) : ‖wave t a‖≤2*‖a‖ := by
  change ‖shift t a+shift (-t) a‖≤2*‖a‖
  have he := norm_add_le (shift t a) (shift (-t) a)
  rw [shift_norm,shift_norm] at he
  linarith

theorem wave_norm_le (t : ℝ) : ‖wave t‖≤2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (wave_norm_apply_le t)

theorem cosine_selfAdjoint (t : ℝ) : IsSelfAdjoint (cosine t) :=
  (show IsSelfAdjoint (1/2:ℂ) by simp [IsSelfAdjoint]).smul (wave_selfAdjoint t)

theorem cosine_norm_apply_le (t : ℝ) (a : Space) : ‖cosine t a‖≤‖a‖ := by
  change ‖(1/2:ℂ) • wave t a‖≤‖a‖
  rw [norm_smul]
  norm_num
  linarith [wave_norm_apply_le t a]

theorem cosine_norm_le (t : ℝ) : ‖cosine t‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun a => by simpa using cosine_norm_apply_le t a)

theorem cosine_zero : cosine 0=ContinuousLinearMap.id ℂ Space := by
  apply ContinuousLinearMap.ext
  intro a
  change (1/2:ℂ) • (shift 0 a+shift (-0) a)=a
  rw [neg_zero,shift_zero]
  module

theorem cosine_even (t : ℝ) : cosine (-t)=cosine t := by
  simp only [cosine,wave,neg_neg]
  rw [add_comm]

/-- The exact cosine-family law is derived from actual translation
composition, rather than imposed as a wave-operator axiom. -/
theorem cosine_law (s t : ℝ) :
    cosine (s+t)+cosine (s-t)=(2:ℂ) • (cosine s * cosine t) := by
  apply ContinuousLinearMap.ext
  intro a
  change cosine (s+t) a+cosine (s-t) a=(2:ℂ) • (cosine s (cosine t a))
  simp only [cosine,wave,smul_apply,add_apply,map_smul,map_add,←shift_add]
  rw [show -(s+t)=(-s)+(-t) by ring,
    show -(s-t)=(-s)+t by ring,show s-t=s+(-t) by ring]
  module

theorem wave_strongContinuous (a : Space) : Continuous (fun t : ℝ => wave t a) :=
  (shift_strongContinuous a).add ((shift_strongContinuous a).comp continuous_neg)

theorem cosine_strongContinuous (a : Space) : Continuous (fun t : ℝ => cosine t a) :=
  (wave_strongContinuous a).const_smul (1/2:ℂ)

/-- A representative-level formula, retaining every almost-everywhere
qualification needed for the actual L² operators. -/
theorem wave_ae (t : ℝ) (a : Space) : wave t a =ᵐ[volume]
    fun u : ℝ => a (u+t)+a (u-t) := by
  have ha := Lp.coeFn_add (shift t a) (shift (-t) a)
  filter_upwards [ha,shift_ae t a,shift_ae (-t) a] with u hu hplus hminus
  change (shift t a+shift (-t) a) u=_
  rw [hu]
  change (shift t a) u+(shift (-t) a) u=_
  rw [hplus,hminus]
  simp [sub_eq_add_neg]

#print axioms wave_selfAdjoint
#print axioms wave_norm_le
#print axioms cosine_law
#print axioms cosine_strongContinuous
#print axioms wave_ae

end QuantitativeMaass.ZeroWave
