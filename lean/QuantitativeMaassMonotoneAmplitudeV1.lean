module

public import QuantitativeMaassAbelVariationDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Multiplication by a nonnegative decreasing weight costs its endpoint
value, even when its derivative is concentrated near that endpoint. -/
theorem decreasing_weight_amplitude_variation (g g' : ℝ → ℂ) (p p' : ℝ → ℝ)
    (a b M M1 : ℝ) (hab : a≤b) (hM : 0≤M) (hM1 : 0≤M1)
    (hg : ∀ u∈uIcc a b,HasDerivAt g (g' u) u)
    (hp : ∀ u∈uIcc a b,HasDerivAt p (p' u) u)
    (hgi : IntervalIntegrable g' volume a b) (hpi : IntervalIntegrable p' volume a b)
    (hg0 : ∀ u∈Icc a b,‖g u‖≤M) (hg1 : ∀ u∈Icc a b,‖g' u‖≤M1)
    (hp0 : ∀ u∈Icc a b,0≤p u ∧ p u≤p a)
    (hp1 : ∀ u∈Icc a b,p' u≤0) :
    (∫ u in a..b,‖g' u*(p u:ℂ)+g u*(p' u:ℂ)‖)≤
      (M1*(b-a)+M)*p a := by
  have hpc : ContinuousOn (fun u => (p u:ℂ)) (uIcc a b) := fun u hu =>
    ((hp u hu).ofReal_comp).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (uIcc a b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have hpic : IntervalIntegrable (fun u => (p' u:ℂ)) volume a b := ⟨hpi.1.ofReal,hpi.2.ofReal⟩
  have hi := (hgi.mul_continuousOn hpc).add (hpic.continuousOn_mul hgc)
  have hb : IntervalIntegrable (fun u => M1*p a+M*(-p' u)) volume a b :=
    intervalIntegrable_const.add (hpi.neg.const_mul M)
  have hh := intervalIntegral.integral_mono_on hab hi.norm hb (fun u hu => by
    calc
      ‖g' u*(p u:ℂ)+g u*(p' u:ℂ)‖ ≤ ‖g' u*(p u:ℂ)‖+‖g u*(p' u:ℂ)‖ := norm_add_le _ _
      _ = ‖g' u‖*p u+‖g u‖*(-p' u) := by
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hp0 u hu).1,abs_of_nonpos (hp1 u hu)]
      _ ≤ M1*p a+M*(-p' u) := add_le_add
        (mul_le_mul (hg1 u hu) (hp0 u hu).2 (hp0 u hu).1 hM1)
        (mul_le_mul_of_nonneg_right (hg0 u hu) (neg_nonneg.mpr (hp1 u hu))))
  rw [intervalIntegral.integral_add (f:=fun _ => M1*p a) (g:=fun u => M*(-p' u)) intervalIntegrable_const (hpi.neg.const_mul M),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_neg,intervalIntegral.integral_eq_sub_of_hasDerivAt hp hpi,
    smul_eq_mul] at hh
  have hb0 := (hp0 b ⟨hab,le_rfl⟩).1
  nlinarith [mul_nonneg hM hb0]

/-- Square-root Abel decay with a decreasing auxiliary weight; derivatives of
that weight contribute only its value at the singular lower endpoint. -/
theorem abelSingularWeight_decreasing_amplitude_decay
    (g g' : ℝ → ℂ) (p p' : ℝ → ℝ) (d b t M M1 : ℝ)
    (hd : 0<d) (hdb : d≤b) (ht : t≠0) (hM : 0≤M) (hM1 : 0≤M1)
    (hgm : Measurable g) (hpm : Measurable p)
    (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hp : ∀ u∈uIcc d b,HasDerivAt p (p' u) u)
    (hgi : IntervalIntegrable g' volume d b) (hpi : IntervalIntegrable p' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤M) (hg1 : ∀ u∈Icc d b,‖g' u‖≤M1)
    (hp0 : ∀ u∈Icc d b,0≤p u ∧ p u≤p d)
    (hp1 : ∀ u∈Icc d b,p' u≤0) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(p u:ℂ))*(abelSingularWeight d u:ℂ)‖≤
      ((5*M+M1*(b-d))*p d)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have hpd := (hp0 d ⟨le_rfl,hdb⟩).1
  have hpc : ContinuousOn (fun u => (p u:ℂ)) (uIcc d b) := fun u hu =>
    ((hp u hu).ofReal_comp).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (uIcc d b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have hpic : IntervalIntegrable (fun u => (p' u:ℂ)) volume d b := ⟨hpi.1.ofReal,hpi.2.ofReal⟩
  have hi := (hgi.mul_continuousOn hpc).add (hpic.continuousOn_mul hgc)
  have hh := abelSingularWeight_variation_decay (fun u => g u*(p u:ℂ))
    (fun u => g' u*(p u:ℂ)+g u*(p' u:ℂ)) d b t (M*p d) ((M1*(b-d)+M)*p d)
    hd hdb ht (by positivity) (by positivity) (hgm.mul (Complex.measurable_ofReal.comp hpm))
    (fun u hu => (hg u hu).mul (hp u hu).ofReal_comp) hi (by
      intro u hu
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp0 u hu).1]
      exact mul_le_mul (hg0 u hu) (hp0 u hu).2 (hp0 u hu).1 hM)
    (decreasing_weight_amplitude_variation g g' p p' d b M M1 hdb hM hM1 hg hp hgi hpi hg0 hg1 hp0 hp1)
  convert hh using 1
  ring

#print axioms decreasing_weight_amplitude_variation
#print axioms abelSingularWeight_decreasing_amplitude_decay

end QuantitativeMaass
