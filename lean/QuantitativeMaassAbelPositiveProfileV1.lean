module

public import QuantitativeMaassAbelCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def abelCutoffProfileReal (a q : ℝ) : ℝ :=
  -(Real.sqrt 2/Real.pi)*(∫ s in Ioi (0:ℝ),deriv (abelCutoffReal a) (q+s^2))

theorem abelCutoffProfile_eq (a q : ℝ) :
    abelProfile (abelCutoff a) q=(abelCutoffProfileReal a q:ℂ) := by
  simp only [abelProfile,abelIntegral,abelCutoff_deriv,integral_complex_ofReal,
    abelCutoffProfileReal,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div]

theorem abelCutoffProfile_nonneg (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 1≤q) :
    0≤abelCutoffProfileReal a q := by
  have hi : (∫ s in Ioi (0:ℝ),deriv (abelCutoffReal a) (q+s^2))≤0 :=
    integral_nonpos (fun s => abelCutoffReal_deriv_nonpos a ha (q+s^2) (by nlinarith [sq_nonneg s]))
  exact mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)) hi

theorem abelCutoffProfile_norm (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 1≤q) :
    ‖abelProfile (abelCutoff a) q‖=abelCutoffProfileReal a q := by
  rw [abelCutoffProfile_eq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (abelCutoffProfile_nonneg a ha q hq)]

theorem abelCutoff_radius_support (R : ℝ) (hR : 0<R) :
    Function.support (abelCutoff (Real.cosh R-1))⊆Iic (Real.cosh R) := by
  have ha : 0<Real.cosh R-1 := sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hR))
  simpa only [add_sub_cancel] using abelCutoff_support (Real.cosh R-1) ha

#print axioms abelCutoffProfile_eq
#print axioms abelCutoffProfile_nonneg
#print axioms abelCutoffProfile_norm
#print axioms abelCutoff_radius_support

end QuantitativeMaass
