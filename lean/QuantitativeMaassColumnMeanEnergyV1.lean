module

public import QuantitativeMaassCuspColumnMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups

namespace QuantitativeMaass

/-- Exact squared norm of the period-average column as a double kernel integral. -/
theorem cuspColumnMean_norm_square (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (hc : Continuous c) (s : SL(2,ℤ)) (u : ℝ) :
    ‖cuspColumnMean N c s u‖^2=
      (∫ x in Icc (0:ℝ) 1,∫ y in Icc (0:ℝ) 1,
        inner ℂ (c (cuspLogPoint N s u x)) (c (cuspLogPoint N s u y))).re := by
  have hcont : Continuous (fun x => c (cuspLogPoint N s u x)) :=
    hc.comp ((cuspLogPoint_continuous N s).comp (continuous_const.prodMk continuous_id))
  have hint : IntegrableOn (fun x => c (cuspLogPoint N s u x)) (Icc (0:ℝ) 1) volume :=
    hcont.integrableOn_Icc
  have hh := cuspColumnMean_inner N c hc s u (cuspColumnMean N c s u)
  have he : inner ℂ (cuspColumnMean N c s u) (cuspColumnMean N c s u)=
      ∫ x in Icc (0:ℝ) 1,∫ y in Icc (0:ℝ) 1,
        inner ℂ (c (cuspLogPoint N s u x)) (c (cuspLogPoint N s u y)) := by
    rw [hh]
    unfold cuspConstant zeroFourier
    simp only [cuspProfile,dite_eq_left (Real.exp_pos u)]
    rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards with x
    exact (integral_inner hint (c (cuspLogPoint N s u x))).symm
  have hre := congrArg Complex.re he
  rw [show (inner ℂ (cuspColumnMean N c s u) (cuspColumnMean N c s u)).re=
    ‖cuspColumnMean N c s u‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _] at hre
  exact hre

/-- Exact centered energy; every term is the actual continuous column kernel. -/
theorem cuspColumnMean_centered_energy (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (hc : Continuous c) (s : SL(2,ℤ)) (u : ℝ) (z : ℍ) :
    ‖c z-cuspColumnMean N c s u‖^2=‖c z‖^2-
      2*(∫ x in Icc (0:ℝ) 1,inner ℂ (c z) (c (cuspLogPoint N s u x))).re+
      (∫ x in Icc (0:ℝ) 1,∫ y in Icc (0:ℝ) 1,
        inner ℂ (c (cuspLogPoint N s u x)) (c (cuspLogPoint N s u y))).re := by
  have hcont : Continuous (fun x => c (cuspLogPoint N s u x)) :=
    hc.comp ((cuspLogPoint_continuous N s).comp (continuous_const.prodMk continuous_id))
  have hint : IntegrableOn (fun x => c (cuspLogPoint N s u x)) (Icc (0:ℝ) 1) volume :=
    hcont.integrableOn_Icc
  rw [norm_sub_sq (𝕜:=ℂ)]
  change ‖c z‖^2-2*(inner ℂ (c z) (cuspColumnMean N c s u)).re+
    ‖cuspColumnMean N c s u‖^2=_
  rw [cuspColumnMean_norm_square N c hc s u]
  congr 2
  exact congrArg (fun q : ℂ => 2*q.re) (integral_inner hint (c z)).symm

#print axioms cuspColumnMean_norm_square
#print axioms cuspColumnMean_centered_energy

end QuantitativeMaass
