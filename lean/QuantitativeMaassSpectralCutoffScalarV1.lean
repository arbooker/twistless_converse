module

public import QuantitativeMaassWaveSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass.Wave

/-- A continuous cutoff of the resolvent spectrum, vanishing below ε.
It is a contraction but need not be an orthogonal projection. -/
def resolventCutoff (ε s : ℝ) : ℝ := 1-ε/max ε s

/-- The inverse resolvent minus identity, regularized below ε. -/
def boundedResolventGenerator (ε s : ℝ) : ℝ := (max ε s)⁻¹-1

theorem resolventCutoff_continuous (ε : ℝ) (hε : 0<ε) :
    Continuous (resolventCutoff ε) :=
  continuous_const.sub (continuous_const.div (continuous_const.max continuous_id)
    (fun s => ne_of_gt (lt_of_lt_of_le hε (le_max_left ε s))))

theorem boundedResolventGenerator_continuous (ε : ℝ) (hε : 0<ε) :
    Continuous (boundedResolventGenerator ε) :=
  ((continuous_const.max continuous_id).inv₀
    (fun s => ne_of_gt (lt_of_lt_of_le hε (le_max_left ε s)))).sub continuous_const

theorem resolventCutoff_bounds (ε s : ℝ) (hε : 0<ε) :
    0≤resolventCutoff ε s ∧ resolventCutoff ε s≤1 := by
  have hm : 0<max ε s := lt_of_lt_of_le hε (le_max_left ε s)
  have hd : ε/max ε s≤1 := (div_le_one hm).mpr (le_max_left _ _)
  have hd0 : 0≤ε/max ε s := div_nonneg hε.le hm.le
  unfold resolventCutoff
  constructor <;> linarith

theorem resolventCutoff_norm_le (ε s : ℝ) (hε : 0<ε) :
    ‖resolventCutoff ε s‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (resolventCutoff_bounds ε s hε).1]
  exact (resolventCutoff_bounds ε s hε).2

theorem resolventCutoff_zero (ε s : ℝ) (hε : 0<ε) (hs : s≤ε) :
    resolventCutoff ε s=0 := by
  simp only [resolventCutoff,max_eq_left hs,div_self (ne_of_gt hε),sub_self]

/-- The inverse relation is exact on the cutoff, even at the zero spectral
point: the cutoff vanishes on the region where the inverse was altered. -/
theorem resolventCutoff_generator_identity (ε s : ℝ) (hε : 0<ε) :
    s*(resolventCutoff ε s+boundedResolventGenerator ε s*resolventCutoff ε s)=
      resolventCutoff ε s := by
  by_cases hs : s≤ε
  · rw [resolventCutoff_zero ε s hε hs]
    ring
  · have hp : 0<s := lt_trans hε (lt_of_not_ge hs)
    simp only [resolventCutoff,boundedResolventGenerator,max_eq_right (le_of_not_ge hs)]
    field_simp
    ring

/-- On a nonnegative resolvent spectrum the cutoff error after one
resolvent factor has uniform operator-norm bound ε. -/
theorem resolventCutoff_residual_bound (ε s : ℝ) (hε : 0<ε) (hs : 0≤s) :
    ‖s*(resolventCutoff ε s-1)‖≤ε := by
  by_cases he : s≤ε
  · rw [resolventCutoff_zero ε s hε he]
    simpa only [zero_sub,mul_neg_one,norm_neg,Real.norm_eq_abs,abs_of_nonneg hs] using he
  · have hp : 0<s := lt_trans hε (lt_of_not_ge he)
    have hv : s*(resolventCutoff ε s-1)= -ε := by
      simp only [resolventCutoff,max_eq_right (le_of_not_ge he)]
      field_simp
      ring
    rw [hv,norm_neg,Real.norm_eq_abs,abs_of_pos hε]

theorem boundedResolventGenerator_norm_le (ε s : ℝ) (hε : 0<ε) :
    ‖boundedResolventGenerator ε s‖≤ε⁻¹+1 := by
  have hm : 0<max ε s := lt_of_lt_of_le hε (le_max_left ε s)
  calc
    _ ≤ ‖(max ε s)⁻¹‖+‖(1:ℝ)‖ := norm_sub_le _ _
    _ = (max ε s)⁻¹+1 := by rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hm)]; norm_num
    _ ≤ ε⁻¹+1 := by linarith [inv_anti₀ hε (le_max_left ε s)]

#print axioms resolventCutoff_generator_identity
#print axioms resolventCutoff_residual_bound
#print axioms boundedResolventGenerator_norm_le

end QuantitativeMaass.Wave
