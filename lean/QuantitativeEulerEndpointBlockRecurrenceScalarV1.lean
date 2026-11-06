module

public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public section
namespace QuantitativeEulerEndpointBlockRecurrence

/-- Scalar accounting for a soft block, once its actual hard contraction
and trace-loss estimate are supplied. This is not a count theorem. -/
theorem soft_block_excess {a m r target next defect L w rho theta eta D : ℝ}
    (hdef : 0≤defect) (hw0 : 0≤w) (hw1 : w≤1)
    (hrho0 : 0≤rho) (hrho1 : rho≤1) (htheta0 : 0≤theta) (htheta1 : theta≤1)
    (heta : 0≤eta) (hD : 0≤D) (hrD : r≤D)
    (hm : a-4*defect≤m) (hchain : r-target≤rho*(m-target))
    (hloss : w*(m-(r+(m-r)*theta+r*eta))-2*L*defect≤a-next) :
    next-target≤(1-w*(1-rho)*(1-theta))*(a-target)+(4+2*L)*defect+D*eta := by
  have hwt : 0≤w*(1-theta) := mul_nonneg hw0 (sub_nonneg.mpr htheta1)
  have hwr : 0≤w*(1-theta)*(1-rho) := mul_nonneg hwt (sub_nonneg.mpr hrho1)
  have hmr : (1-rho)*(m-target)≤m-r := by nlinarith only [hchain]
  have hc := mul_le_mul_of_nonneg_left hmr hwt
  have hmi := mul_le_mul_of_nonneg_left hm hwr
  have hprod : w*(1-theta)*(1-rho)≤1 := by
    calc
      w*(1-theta)*(1-rho)≤1*1*1 := mul_le_mul
        (mul_le_mul hw1 (by linarith : 1-theta≤1) (sub_nonneg.mpr htheta1) (by norm_num))
        (by linarith : 1-rho≤1) (sub_nonneg.mpr hrho1) (by norm_num)
      _ = 1 := by ring
  have herr := mul_le_mul_of_nonneg_right hprod (mul_nonneg (by norm_num : (0:ℝ)≤4) hdef)
  have hadd1 := mul_le_mul_of_nonneg_left hrD hw0
  have hadd2 := mul_le_mul_of_nonneg_right hw1 hD
  have hadd := mul_le_mul_of_nonneg_right (hadd1.trans (by simpa only [one_mul] using hadd2)) heta
  nlinarith only [hloss,hc,hmi,herr,hadd]

#print axioms soft_block_excess
end QuantitativeEulerEndpointBlockRecurrence
