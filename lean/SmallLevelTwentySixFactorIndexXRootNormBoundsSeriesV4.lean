module
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4
public import SmallLevelTwentySixFactorIndexXRootCoverSeriesV4
public import SmallLevelTwentySixLowCurveFactorFamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6XRoot
open Complex Polynomial QuantitativeArithmeticComplexHornerBounds
def lowerQ : Fin 6→ℚ := ![(4777/125),(4781/1000),(17/50),(1377/1000),(8623/1000),(8623/1000)]
def upperQ : Fin 6→ℚ := ![(38217/1000),(2391/500),(341/1000),(689/500),(1078/125),(1078/125)]
theorem lower_enclosure : ∀ i : Fin 6,lowerQ i≤
    (centerQ i).1^2+(centerQ i).2^2-radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ) := by decide +kernel
theorem upper_enclosure : ∀ i : Fin 6,
    (centerQ i).1^2+(centerQ i).2^2+radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ)≤upperQ i := by decide +kernel

theorem root_norm_bounds (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 6,(lowerQ i:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(upperQ i:ℝ) := by
  obtain ⟨i,hi⟩:=pRoot_root_in_disk z hz
  exact ⟨i,squared_norm_enclosure_of_rational_error z (centerQ i) radiusQ
    (lowerQ i) (upperQ i) (by decide +kernel) hi.le (lower_enclosure i) (upper_enclosure i)⟩
theorem factor_binding (x : ℂ) :
    SmallLevelTwentySixPariFinalFactors.factor6 x=541*pRoot.eval x := by
  norm_num [SmallLevelTwentySixPariFinalFactors.factor6,pRoot,pCoefficient,
    eval_hornerPolynomial,hornerValue]
  ring
#print axioms factor_binding
#print axioms root_norm_bounds

end SmallLevelTwentySixFactor6XRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7XRoot
open Complex Polynomial QuantitativeArithmeticComplexHornerBounds
def lowerQ : Fin 7→ℚ := ![(4277/200),(1333/500),(693/500),(2139/200),(5983/250),(2531/250),(2531/250)]
def upperQ : Fin 7→ℚ := ![(10693/500),(2667/1000),(1387/1000),(1337/125),(23933/1000),(81/8),(81/8)]
theorem lower_enclosure : ∀ i : Fin 7,lowerQ i≤
    (centerQ i).1^2+(centerQ i).2^2-radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ) := by decide +kernel
theorem upper_enclosure : ∀ i : Fin 7,
    (centerQ i).1^2+(centerQ i).2^2+radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ)≤upperQ i := by decide +kernel

theorem root_norm_bounds (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 7,(lowerQ i:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(upperQ i:ℝ) := by
  obtain ⟨i,hi⟩:=pRoot_root_in_disk z hz
  exact ⟨i,squared_norm_enclosure_of_rational_error z (centerQ i) radiusQ
    (lowerQ i) (upperQ i) (by decide +kernel) hi.le (lower_enclosure i) (upper_enclosure i)⟩
theorem factor_binding (x : ℂ) :
    SmallLevelTwentySixPariFinalFactors.factor7 x=1*pRoot.eval x := by
  norm_num [SmallLevelTwentySixPariFinalFactors.factor7,pRoot,pCoefficient,
    eval_hornerPolynomial,hornerValue]
  ring
#print axioms factor_binding
#print axioms root_norm_bounds

end SmallLevelTwentySixFactor7XRoot
end
