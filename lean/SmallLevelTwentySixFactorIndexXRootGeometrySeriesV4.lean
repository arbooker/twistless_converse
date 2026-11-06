module
public import SmallLevelTwentySixFactorIndexXRootNodeBundleSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6XRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 6) : Fin 6→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance] i
def pBoundQ : Fin 6→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound]
theorem distance_positive (i : Fin 6) : ∀ j : Fin 6,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive

theorem distance_diagonal (i : Fin 6) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal

theorem distance_lower (i : Fin 6) : ∀ j : Fin 6,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower

theorem bound_product (i : Fin 6) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 6,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product

theorem all_P_value_bounds (i : Fin 6) : ‖pRoot.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound


end SmallLevelTwentySixFactor6XRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7XRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 7) : Fin 7→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance,node6Distance] i
def pBoundQ : Fin 7→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound,node6Bound]
theorem distance_positive (i : Fin 7) : ∀ j : Fin 7,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive
  · exact node6_distance_positive

theorem distance_diagonal (i : Fin 7) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal
  · exact node6_distance_diagonal

theorem distance_lower (i : Fin 7) : ∀ j : Fin 7,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower
  · exact node6_distance_lower

theorem bound_product (i : Fin 7) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 7,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product
  · exact node6_bound_product

theorem all_P_value_bounds (i : Fin 7) : ‖pRoot.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound
  · exact node6_bound


end SmallLevelTwentySixFactor7XRoot
end
