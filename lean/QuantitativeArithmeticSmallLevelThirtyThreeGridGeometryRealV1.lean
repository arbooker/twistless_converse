module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridGeometryV1
public import QuantitativeArithmeticSmallLevelThirtyThreeSourceTaylorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix

theorem group_geometry_real (i : Fin 588) :
    (sourceMatrix (groupSource i) 1 0:ℝ)*((groupIndex i:ℕ):ℝ)/66+
      (sourceMatrix (groupSource i) 1 1:ℝ) ≠ 0 ∧
    sourcePartner (groupSource i) (((groupIndex i:ℕ):ℝ)/66)=(groupTarget i:ℝ)/66 ∧
    sourceRate (groupSource i) (((groupIndex i:ℕ):ℝ)/66)=(groupRate i:ℝ) ∧
    sourceDerivative (groupSource i) (((groupIndex i:ℕ):ℝ)/66)=(groupDerivative i:ℝ) ∧
    0 < (groupRate i:ℝ) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := group_valid i
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [mul_div_assoc]
    have hh := (Rat.cast_ne_zero (α := ℝ)).mpr h0
    push_cast at hh
    exact hh
  · unfold sourcePartner
    have hh := congrArg (fun x : ℚ => (x:ℝ)) h1
    push_cast at hh
    exact hh
  · unfold sourceRate
    have hh := congrArg (fun x : ℚ => (x:ℝ)) h2
    push_cast at hh
    simpa only [Matrix.det_fin_two,Matrix.map_apply,Rat.cast_intCast,Int.cast_sub,Int.cast_mul] using hh
  · unfold sourceDerivative
    have hh := congrArg (fun x : ℚ => (x:ℝ)) h3
    push_cast at hh
    simpa only [Matrix.det_fin_two,Matrix.map_apply,Rat.cast_intCast,Int.cast_sub,Int.cast_mul] using hh
  · exact_mod_cast h4

theorem infinity_geometry_real (i : Fin 46) :
    (sourceMatrix (infinitySpecs i).1 1 0:ℝ)*(((infinitySpecs i).2:ℕ):ℝ)/66+
      (sourceMatrix (infinitySpecs i).1 1 1:ℝ)=0 := by
  exact_mod_cast infinity_valid i

#print axioms group_geometry_real
#print axioms infinity_geometry_real
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
