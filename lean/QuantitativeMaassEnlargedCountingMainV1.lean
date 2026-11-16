module

public import QuantitativeMaassEnlargedMovingRegularTraceV1
public import QuantitativeMaassCrossCountingIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch AsymptoticNestedQuotients
open AsymptoticCongruenceStrip AsymptoticRegularTrace
open scoped FourierTransform SchwartzMap lp
namespace QuantitativeMaass.Scheduled

/-- The moving regular main term factors through the actual counting
operator. The spatial cutoff mass remains explicit. -/
theorem enlargedMovingExpressionMain_counting (N : ℕ) (E : ℕ→Expression)
    (A : ℕ→ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ))
    (hA : ∀ m,Counting.Realizes (gamma N) (E m) (A m))
    (δ P D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) :
    enlargedMovingExpressionMain N E δ P D hδ K hc ε t=
      (∫ x in cutoffRectangle (movingLowerEdge δ P ε t) t,
        ‖upperFunction (cutoffSeed (movingLowerEdge δ P ε t) D t
          (movingLowerEdge_pos hδ P ε t)).toFun x‖^2)*
      ((A (growingLVDegree t) (delta (classOf (gamma N) 1))) (classOf (gamma N) 1)*
        windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re := by
  unfold enlargedMovingExpressionMain
  rw [←integral_mul_const]
  apply setIntegral_congr_fun (upperRectangle_compact 0 1 (movingLowerEdge δ P ε t) _
    (movingLowerEdge_pos hδ P ε t)).measurableSet
  intro x _
  dsimp only
  rw [←(hA (growingLVDegree t)).root_coefficient x]
  simp only [mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

#print axioms enlargedMovingExpressionMain_counting
end QuantitativeMaass.Scheduled
