module
public import SmallLevelTwentySixFactorIndexYRootNodeBundleSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6YRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 18) : Fin 18→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance,node6Distance,node7Distance,node8Distance,node9Distance,node10Distance,node11Distance,node12Distance,node13Distance,node14Distance,node15Distance,node16Distance,node17Distance] i
def pBoundQ : Fin 18→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound,node6Bound,node7Bound,node8Bound,node9Bound,node10Bound,node11Bound,node12Bound,node13Bound,node14Bound,node15Bound,node16Bound,node17Bound]
theorem distance_positive (i : Fin 18) : ∀ j : Fin 18,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive
  · exact node6_distance_positive
  · exact node7_distance_positive
  · exact node8_distance_positive
  · exact node9_distance_positive
  · exact node10_distance_positive
  · exact node11_distance_positive
  · exact node12_distance_positive
  · exact node13_distance_positive
  · exact node14_distance_positive
  · exact node15_distance_positive
  · exact node16_distance_positive
  · exact node17_distance_positive

theorem distance_diagonal (i : Fin 18) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal
  · exact node6_distance_diagonal
  · exact node7_distance_diagonal
  · exact node8_distance_diagonal
  · exact node9_distance_diagonal
  · exact node10_distance_diagonal
  · exact node11_distance_diagonal
  · exact node12_distance_diagonal
  · exact node13_distance_diagonal
  · exact node14_distance_diagonal
  · exact node15_distance_diagonal
  · exact node16_distance_diagonal
  · exact node17_distance_diagonal

theorem distance_lower (i : Fin 18) : ∀ j : Fin 18,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower
  · exact node6_distance_lower
  · exact node7_distance_lower
  · exact node8_distance_lower
  · exact node9_distance_lower
  · exact node10_distance_lower
  · exact node11_distance_lower
  · exact node12_distance_lower
  · exact node13_distance_lower
  · exact node14_distance_lower
  · exact node15_distance_lower
  · exact node16_distance_lower
  · exact node17_distance_lower

theorem bound_product (i : Fin 18) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 18,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product
  · exact node6_bound_product
  · exact node7_bound_product
  · exact node8_bound_product
  · exact node9_bound_product
  · exact node10_bound_product
  · exact node11_bound_product
  · exact node12_bound_product
  · exact node13_bound_product
  · exact node14_bound_product
  · exact node15_bound_product
  · exact node16_bound_product
  · exact node17_bound_product

theorem all_P_value_bounds (i : Fin 18) : ‖pRoot.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound
  · exact node6_bound
  · exact node7_bound
  · exact node8_bound
  · exact node9_bound
  · exact node10_bound
  · exact node11_bound
  · exact node12_bound
  · exact node13_bound
  · exact node14_bound
  · exact node15_bound
  · exact node16_bound
  · exact node17_bound


end SmallLevelTwentySixFactor6YRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7YRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 14) : Fin 14→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance,node6Distance,node7Distance,node8Distance,node9Distance,node10Distance,node11Distance,node12Distance,node13Distance] i
def pBoundQ : Fin 14→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound,node6Bound,node7Bound,node8Bound,node9Bound,node10Bound,node11Bound,node12Bound,node13Bound]
theorem distance_positive (i : Fin 14) : ∀ j : Fin 14,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive
  · exact node6_distance_positive
  · exact node7_distance_positive
  · exact node8_distance_positive
  · exact node9_distance_positive
  · exact node10_distance_positive
  · exact node11_distance_positive
  · exact node12_distance_positive
  · exact node13_distance_positive

theorem distance_diagonal (i : Fin 14) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal
  · exact node6_distance_diagonal
  · exact node7_distance_diagonal
  · exact node8_distance_diagonal
  · exact node9_distance_diagonal
  · exact node10_distance_diagonal
  · exact node11_distance_diagonal
  · exact node12_distance_diagonal
  · exact node13_distance_diagonal

theorem distance_lower (i : Fin 14) : ∀ j : Fin 14,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower
  · exact node6_distance_lower
  · exact node7_distance_lower
  · exact node8_distance_lower
  · exact node9_distance_lower
  · exact node10_distance_lower
  · exact node11_distance_lower
  · exact node12_distance_lower
  · exact node13_distance_lower

theorem bound_product (i : Fin 14) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 14,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product
  · exact node6_bound_product
  · exact node7_bound_product
  · exact node8_bound_product
  · exact node9_bound_product
  · exact node10_bound_product
  · exact node11_bound_product
  · exact node12_bound_product
  · exact node13_bound_product

theorem all_P_value_bounds (i : Fin 14) : ‖pRoot.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound
  · exact node6_bound
  · exact node7_bound
  · exact node8_bound
  · exact node9_bound
  · exact node10_bound
  · exact node11_bound
  · exact node12_bound
  · exact node13_bound


end SmallLevelTwentySixFactor7YRoot
end
