module

public import QuantitativeMaassCuspParabolicLatticeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

theorem rational_label_eq_of_action (g h : AsymptoticRationalGroup.Group)
    (he : ∀ z : ℍ,g•z=h•z) : g=h := by
  apply mul_inv_eq_one.mp
  apply QuantitativeHolomorphic.rational_label_eq_one_of_fixed
  intro z
  rw [mul_smul,he,smul_inv_smul]

/-- The projective label of an integral upper-triangular matrix is exactly
translation by its signed upper-right entry. -/
theorem integral_upper_triangular_label (B : SL(2,ℤ)) (hc : B 1 0=0) :
    integralLabel B=integralLabel (upperSL (B 0 0*B 0 1)) := by
  apply rational_label_eq_of_action
  intro z
  rw [integralLabel_action,integralLabel_action]
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply,coe_specialLinearGroup_apply]
  rcases integral_upper_triangular_diagonal B hc with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simp [upperSL,AsymptoticFreshCRT.upper,hc,ha,hd]
  · simp [upperSL,AsymptoticFreshCRT.upper,hc,ha,hd,div_neg]
    ring

/-- Distinct integer translations in the same actual cusp remain distinct
in the projective group. -/
theorem cuspParabolicMatrix_label_injective (A : SL(2,ℤ)) :
    Function.Injective (fun n : ℤ => integralLabel (cuspParabolicMatrix A n)) := by
  intro n m he
  simp only [cuspParabolicMatrix,map_mul,map_inv] at he
  have hh := mul_left_cancel (mul_right_cancel he)
  have ha := congrArg (fun g : AsymptoticRationalGroup.Group => (g•I:ℍ).re) hh
  simp only [upper_label,translation_re] at ha
  exact_mod_cast (add_left_cancel ha)

/-- Every high-cusp cross return has a unique actual admissible integer
translation parameter. -/
theorem high_cusp_return_unique_translation (N : ℕ) (A : SL(2,ℤ))
    (γ : gamma N) (z w : ℍ) (hheight : z.im=w.im) (R : ℝ)
    (hR : dist (γ•(A•z)) (A•w)≤R) (hz : Real.exp (R/2)<z.im) :
    ∃! n : ℤ,(N:ℤ)∣n*(A 1 0)^2 ∧ integralLabel (cuspParabolicMatrix A n)=γ.val := by
  let B := representative (cuspConjugateFull N A γ)
  have hb (v : ℍ) : B•v=cuspConjugateFull N A γ•v := by
    rw [←integralLabel_action,representative_label]
    rfl
  have hd : dist (B•z) w≤R := by
    rw [hb,cuspConjugateFull_cross_displacement]
    exact hR
  have hc := integral_high_cusp_cross_lowerleft_zero B z w hheight R hd hz
  let n := B 0 0*B 0 1
  have he : integralLabel (cuspParabolicMatrix A n)=γ.val := by
    simp only [cuspParabolicMatrix,map_mul,map_inv]
    rw [←integral_upper_triangular_label B hc,representative_label]
    change integralLabel A*((integralLabel A)⁻¹*γ.val*integralLabel A)*(integralLabel A)⁻¹=γ.val
    group
  refine ⟨n,⟨(cuspParabolicMatrix_mem_iff N A n).mp (he.symm ▸ γ.property),he⟩,?_⟩
  intro m hm
  exact cuspParabolicMatrix_label_injective A (hm.2.trans he.symm)

#print axioms rational_label_eq_of_action
#print axioms integral_upper_triangular_label
#print axioms cuspParabolicMatrix_label_injective
#print axioms high_cusp_return_unique_translation

end QuantitativeMaass
