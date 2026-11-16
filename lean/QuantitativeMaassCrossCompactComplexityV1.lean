module

public import QuantitativeMaassCrossCompactBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open AsymptoticCongruenceStrip

namespace QuantitativeMaass.CrossCompactBranch

/-- Compact localization has an explicit coefficient cost. The overlap
bound counts the actual intermediate congruence labels for each branch. -/
theorem localExpression_coefficient_bound (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) (o : ℍ) (R S Q : ℝ)
    (hKR : K ⊆ Metric.closedBall o R) (hLS : L ⊆ Metric.closedBall o S)
    (hmotion : ∀ q ∈ E, dist (q.label • o) o ≤ Q) :
    expressionBound (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) ≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+Q+S):ℝ)*
        (B₁*expressionBound E*B₂) := by
  rw [localExpression_bound]
  induction E with
  | nil => simp [expressionBound]
  | cons q E ih =>
    have hq := overlap_card_bound N K L hK hL o R S Q hKR hLS q.label
      (hmotion q (List.mem_cons_self))
    have hq' : ((overlap N K L hK hL q.label).card:ℝ) ≤
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+Q+S):ℝ) := by exact_mod_cast hq
    have hi := ih (fun a ha => hmotion a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.sum_cons]
    have hh := add_le_add
      (mul_le_mul_of_nonneg_right hq' (mul_nonneg (mul_nonneg hB₁ q.bound_nonneg) hB₂)) hi
    apply hh.trans_eq
    simp only [expressionBound,List.map_cons,List.sum_cons]
    ring

#print axioms localExpression_coefficient_bound

end QuantitativeMaass.CrossCompactBranch
