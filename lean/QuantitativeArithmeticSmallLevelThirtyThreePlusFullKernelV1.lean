module
public import QuantitativeArithmeticSmallLevelThirtyThreePlusTriangularKernelV1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusSelectedResidualsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeMinorRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem residual0_match : QuantitativeArithmeticSmallLevelThirtyThreePlusSelectedResiduals.row0=QuantitativeArithmeticSmallLevelThirtyThreeMinorRows.row0 := by rfl
theorem residual9_match : QuantitativeArithmeticSmallLevelThirtyThreePlusSelectedResiduals.row9=QuantitativeArithmeticSmallLevelThirtyThreeMinorRows.row9 := by rfl

theorem full_kernel_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hd : QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x y a≠0)
    (hsource : ∀ j,eval x y z 1 a 1 1 v (baseRows 1 j)=0) : ∀ j<66,v j=0 := by
  have h0 := QuantitativeArithmeticSmallLevelThirtyThreePlusSelectedResiduals.row0_of_sources x y z a v hx hy hz hsource
  have h9 := QuantitativeArithmeticSmallLevelThirtyThreePlusSelectedResiduals.row9_of_sources x y z a v hx hy hz hsource
  rw [residual0_match] at h0
  rw [residual9_match] at h9
  obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeMinorRows.two_rows_zero x y z a v hx hd h0 h9
  exact kernel_free_zero x y z a v hx hy hz hsource h18 h42

#print axioms full_kernel_zero
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
