module

public import QuantitativeMaassAbelSingularWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The square-root singularity is integrable, with its exact primitive.
No artificial positive lower cutoff is needed. -/
theorem inverse_sqrt_gap_integral (d b : ℝ) (hdb : d≤b) :
    IntervalIntegrable (fun u => (Real.sqrt (u-d))⁻¹) volume d b ∧
      (∫ u in d..b,(Real.sqrt (u-d))⁻¹)=2*Real.sqrt (b-d) := by
  have hc : ContinuousOn (fun u : ℝ => 2*Real.sqrt (u-d)) (Icc d b) := by fun_prop
  have hd : ∀ u∈Ioo d b,HasDerivAt (fun v : ℝ => 2*Real.sqrt (v-d))
      ((Real.sqrt (u-d))⁻¹) u := by
    intro u hu
    have hh := (((hasDerivAt_id u).sub_const d).sqrt (sub_pos.mpr hu.1).ne').const_mul 2
    simp only [id_eq] at hh
    convert hh using 1
    field_simp
  have hi : IntervalIntegrable (fun u => (Real.sqrt (u-d))⁻¹) volume d b := by
    rw [intervalIntegrable_iff,uIoc_of_le hdb]
    exact intervalIntegral.integrableOn_deriv_of_nonneg hc hd (fun u _ => by positivity)
  refine ⟨hi,?_⟩
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hdb hc hd hi
  simpa only [sub_self,Real.sqrt_zero,mul_zero,sub_zero] using hh

/-- A separated positive radial distance gives a scalar inverse-square-root
majorant with all constants explicit. -/
theorem abelSingularWeight_le_inverse_sqrt (d u : ℝ) (hd : 0<d) (hu : d<u) :
    abelSingularWeight d u≤(Real.sqrt (Real.sinh d))⁻¹*(Real.sqrt (u-d))⁻¹ := by
  have h := abelSingularWeight_le_linear d u hd hu
  rwa [Real.sqrt_mul (Real.sinh_nonneg_iff.mpr hd.le),mul_inv] at h

/-- Absolute integrability of the bare Abel weight right up to its singular
endpoint at every positive distance. At d=0 the bare weight is not integrable. -/
theorem abelSingularWeight_intervalIntegrable (d b : ℝ) (hd : 0<d) (hdb : d≤b) :
    IntervalIntegrable (abelSingularWeight d) volume d b := by
  have hi := (inverse_sqrt_gap_integral d b hdb).1.const_mul
    ((Real.sqrt (Real.sinh d))⁻¹)
  have hm : Measurable (abelSingularWeight d) := by
    change Measurable (fun u => (Real.sqrt (Real.cosh u-Real.cosh d))⁻¹)
    fun_prop
  apply hi.mono_fun' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [uIoc_of_le hdb] at hu
  rw [Real.norm_of_nonneg (abelSingularWeight_pos d u hd.le hu.1).le]
  exact abelSingularWeight_le_inverse_sqrt d u hd hu.1

/-- The complete initial interval has square-root mass, uniformly in its
length. This is the missing endpoint term in the oscillatory split. -/
theorem abelSingularWeight_initial_integral (d b : ℝ) (hd : 0<d) (hdb : d≤b) :
    (∫ u in d..b,abelSingularWeight d u)≤
      2*Real.sqrt (b-d)/Real.sqrt (Real.sinh d) := by
  have hi := (inverse_sqrt_gap_integral d b hdb).1.const_mul
    ((Real.sqrt (Real.sinh d))⁻¹)
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo hdb
    (abelSingularWeight_intervalIntegrable d b hd hdb) hi
    (fun u hu => abelSingularWeight_le_inverse_sqrt d u hd hu.1)
  rw [intervalIntegral.integral_const_mul,(inverse_sqrt_gap_integral d b hdb).2] at hh
  convert hh using 1
  ring

/-- The same endpoint bound applies to a bounded complex amplitude, including
an arbitrary real oscillatory frequency. -/
theorem abelSingularWeight_initial_amplitude (g : ℝ → ℂ) (d b t A : ℝ)
    (hd : 0<d) (hdb : d≤b) (hA : 0≤A)
    (hg : ∀ u∈Ioc d b,‖g u‖≤A) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      2*A*Real.sqrt (b-d)/Real.sqrt (Real.sinh d) := by
  have hi := (abelSingularWeight_intervalIntegrable d b hd hdb).const_mul A
  have hh := intervalIntegral.norm_integral_le_of_norm_le hdb
    (Eventually.of_forall (fun u hu => show
      ‖Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
        A*abelSingularWeight d u by
      rw [norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (abelSingularWeight_pos d u hd.le hu.1)]
      exact mul_le_mul_of_nonneg_right (hg u hu)
        (abelSingularWeight_pos d u hd.le hu.1).le)) hi
  rw [intervalIntegral.integral_const_mul] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (abelSingularWeight_initial_integral d b hd hdb) hA
  convert hm using 1
  ring

#print axioms inverse_sqrt_gap_integral
#print axioms abelSingularWeight_le_inverse_sqrt
#print axioms abelSingularWeight_intervalIntegrable
#print axioms abelSingularWeight_initial_integral
#print axioms abelSingularWeight_initial_amplitude

end QuantitativeMaass
