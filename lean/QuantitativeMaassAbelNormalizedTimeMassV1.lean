module

public import QuantitativeMaassAbelNormalizedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelNormalizedTest_time_mass (R : ℝ) (hR : 0<R) :
    (∫ t,(Real.cosh (t/2):ℂ)*coshTimeTest (abelNormalizedTest R) t)=1 := by
  have hm := abelNormalizedProfile_mass R hR
  rw [abelNormalizedProfile,abelProfile_time_mass _ (abelNormalizedTest_smooth R)
    (abelNormalizedTest_compact R hR) R hR.le (abelNormalizedTest_support R hR)] at hm
  simpa only [mul_comm] using hm

theorem abelNormalizedTest_time_norm (R : ℝ) (hR : 0<R) (t : ℝ) :
    ‖coshTimeTest (abelNormalizedTest R) t‖=
      (abelCutoffMass R)⁻¹*abelCutoffReal (Real.cosh R-1) (Real.cosh t) := by
  simp only [coshTimeTest,abelNormalizedTest,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (abelCutoffMass_pos R hR),abelCutoff,
    abs_of_nonneg (abelCutoffReal_nonneg _ _)]

theorem abelNormalizedTest_time_norm_mass (R : ℝ) (hR : 0<R) :
    (∫ t,‖coshTimeTest (abelNormalizedTest R) t‖*Real.cosh (|t|/2))=1 := by
  simp_rw [abelNormalizedTest_time_norm R hR]
  have he (t : ℝ) : Real.cosh (|t|/2)=Real.cosh (t/2) := by
    simpa only [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] using Real.cosh_abs (t/2)
  simp_rw [he,mul_assoc]
  rw [integral_const_mul]
  change (abelCutoffMass R)⁻¹*abelCutoffMass R=1
  exact inv_mul_cancel₀ (ne_of_gt (abelCutoffMass_pos R hR))

#print axioms abelNormalizedTest_time_mass
#print axioms abelNormalizedTest_time_norm_mass

end QuantitativeMaass
