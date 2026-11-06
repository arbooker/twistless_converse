module
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4
public import SmallLevelTwentySixFactorIndexYRootCoverSeriesV4
public import SmallLevelTwentySixLowCurveFactorFamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6YRoot
open Complex Polynomial QuantitativeArithmeticComplexHornerBounds
def lowerQ : Fin 18→ℚ := ![(5401/500),(6781/1000),(10593/1000),(16537/500),(16663/500),(38749/1000),(950187/1000),(34138029/1000),(250037/1000),(250037/1000),(13393/500),(13393/500),(29037/1000),(29037/1000),(80943/500),(80943/500),(134281/250),(134281/250)]
def upperQ : Fin 18→ℚ := ![(10803/1000),(3391/500),(5297/500),(1323/40),(33327/1000),(155/4),(237547/250),(3413803/100),(125019/500),(125019/500),(26787/1000),(26787/1000),(14519/500),(14519/500),(161887/1000),(161887/1000),(4297/8),(4297/8)]
theorem lower_enclosure : ∀ i : Fin 18,lowerQ i≤
    (centerQ i).1^2+(centerQ i).2^2-radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ) := by decide +kernel
theorem upper_enclosure : ∀ i : Fin 18,
    (centerQ i).1^2+(centerQ i).2^2+radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ)≤upperQ i := by decide +kernel

theorem root_norm_bounds (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 18,(lowerQ i:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(upperQ i:ℝ) := by
  obtain ⟨i,hi⟩:=pRoot_root_in_disk z hz
  exact ⟨i,squared_norm_enclosure_of_rational_error z (centerQ i) radiusQ
    (lowerQ i) (upperQ i) (by decide +kernel) hi.le (lower_enclosure i) (upper_enclosure i)⟩
theorem squarefree_binding (x y : ℂ) :
    SmallLevelTwentySixLowCurveFactor6.squarefree x y=pRoot.eval y := by
  norm_num [SmallLevelTwentySixLowCurveFactor6.squarefree,pRoot,pCoefficient,
    eval_hornerPolynomial,hornerValue]
  ring
#print axioms squarefree_binding
#print axioms root_norm_bounds

end SmallLevelTwentySixFactor6YRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7YRoot
open Complex Polynomial QuantitativeArithmeticComplexHornerBounds
def lowerQ : Fin 14→ℚ := ![(1917/250),(12781/1000),(6291/200),(4847/125),(23209/500),(133503/1000),(242931/1000),(302523/1000),(379637/1000),(93384/125),(11976/125),(11976/125),(69/2),(69/2)]
def upperQ : Fin 14→ℚ := ![(7669/1000),(6391/500),(3932/125),(38777/1000),(46419/1000),(16688/125),(60733/250),(75631/250),(189819/500),(747073/1000),(95809/1000),(95809/1000),(34501/1000),(34501/1000)]
theorem lower_enclosure : ∀ i : Fin 14,lowerQ i≤
    (centerQ i).1^2+(centerQ i).2^2-radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ) := by decide +kernel
theorem upper_enclosure : ∀ i : Fin 14,
    (centerQ i).1^2+(centerQ i).2^2+radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ)≤upperQ i := by decide +kernel

theorem root_norm_bounds (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 14,(lowerQ i:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(upperQ i:ℝ) := by
  obtain ⟨i,hi⟩:=pRoot_root_in_disk z hz
  exact ⟨i,squared_norm_enclosure_of_rational_error z (centerQ i) radiusQ
    (lowerQ i) (upperQ i) (by decide +kernel) hi.le (lower_enclosure i) (upper_enclosure i)⟩
theorem squarefree_binding (x y : ℂ) :
    SmallLevelTwentySixLowCurveFactor7.squarefree x y=pRoot.eval y := by
  norm_num [SmallLevelTwentySixLowCurveFactor7.squarefree,pRoot,pCoefficient,
    eval_hornerPolynomial,hornerValue]
  ring
#print axioms squarefree_binding
#print axioms root_norm_bounds

end SmallLevelTwentySixFactor7YRoot
end
