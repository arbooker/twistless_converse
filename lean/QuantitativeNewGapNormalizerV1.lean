module

public import QuantitativeNewGapFrickeSignV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticQuotientOperators AsymptoticRegularTrace
open AsymptoticPermutationInvariant AsymptoticPolarIsometry
open scoped lp

variable {G : Type*} [Group G] (H : Subgroup G) (a : G)
  (ha : ∀ g∈H,a*g*a⁻¹∈H) (hai : ∀ g∈H,a⁻¹*g*a∈H)

theorem normalizerEquiv_involutive (haa : a*a∈H) :
    Function.Involutive (leftMulEquiv H a ha hai) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    change classOf H (a*(a*g))=classOf H g
    rw [← mul_assoc]
    exact classOf_mul _ ⟨a*a,haa⟩ g

/-- Exact finite-coset average transport under an actual normalizer. -/
theorem normalizer_old_transport {J K : Subgroup G} (hJ : H≤J) (hK : H≤K)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    (hJK : ∀ g,a*g*a⁻¹∈J ↔ g∈K)
    (hi : (H.subgroupOf J).index=(H.subgroupOf K).index) (q r : Classes H) :
    matrix (space hJ).starProjection (leftMulEquiv H a ha hai q) (leftMulEquiv H a ha hai r)=
      matrix (space hK).starProjection q r := by
  classical
  induction q using Quotient.inductionOn with
  | h g =>
    induction r using Quotient.inductionOn with
    | h k =>
      change (space hJ).starProjection (delta (classOf H (a*k))) (classOf H (a*g))=
        (space hK).starProjection (delta (classOf H k)) (classOf H g)
      rw [projection_matrix,projection_matrix,hi]
      apply if_congr _ rfl rfl
      simp only [forget_classOf,classOf_eq_iff,mul_inv_rev,mul_assoc]
      simpa only [mul_assoc] using hJK (g*k⁻¹)

theorem normalizer_old_invariant {J : Subgroup G} (hJ : H≤J)
    [Finite (J ⧸ H.subgroupOf J)] (hAJ : ∀ g,a*g*a⁻¹∈J ↔ g∈J) :
    Invariant (leftMulEquiv H a ha hai) (space hJ).starProjection :=
  normalizer_old_transport H a ha hai hJ hJ hAJ rfl

theorem normalizer_new_invariant_fixed {J K : Subgroup G} (hJ : H≤J) (hK : H≤K)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    (hAJ : ∀ g,a*g*a⁻¹∈J ↔ g∈J) (hAK : ∀ g,a*g*a⁻¹∈K ↔ g∈K) :
    Invariant (leftMulEquiv H a ha hai) (newSpace hJ hK).starProjection := by
  rw [starProjection_congr _ _ (newSpace_eq_old_sum_kernel hJ hK)]
  exact invariant_kernel _ _ (invariant_add _ _ _
    (normalizer_old_invariant H a ha hai hJ hAJ)
    (normalizer_old_invariant H a ha hai hK hAK))

theorem normalizer_new_invariant_swap {J K : Subgroup G} (hJ : H≤J) (hK : H≤K)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    (haa : a*a∈H) (hJK : ∀ g,a*g*a⁻¹∈J ↔ g∈K)
    (hi : (H.subgroupOf J).index=(H.subgroupOf K).index) :
    Invariant (leftMulEquiv H a ha hai) (newSpace hJ hK).starProjection := by
  have hs : Invariant (leftMulEquiv H a ha hai)
      ((space hJ).starProjection+(space hK).starProjection) := by
    intro q r
    have h₁ := normalizer_old_transport H a ha hai hJ hK hJK hi q r
    have h₂ := normalizer_old_transport H a ha hai hJ hK hJK hi
      (leftMulEquiv H a ha hai q) (leftMulEquiv H a ha hai r)
    rw [normalizerEquiv_involutive H a ha hai haa,normalizerEquiv_involutive H a ha hai haa] at h₂
    change matrixCLM _ _ (_+_)=matrixCLM _ _ (_+_)
    simp only [map_add,matrixCLM_apply]
    rw [h₁,← h₂,add_comm]
  rw [starProjection_congr _ _ (newSpace_eq_old_sum_kernel hJ hK)]
  exact invariant_kernel _ _ hs

theorem normalizerEquivs_commute (b : G)
    (hb : ∀ g∈H,b*g*b⁻¹∈H) (hbi : ∀ g∈H,b⁻¹*g*b∈H)
    (hab : a*b*a⁻¹*b⁻¹∈H) :
    Function.Commute (leftMulEquiv H a ha hai) (leftMulEquiv H b hb hbi) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    change classOf H (a*(b*g))=classOf H (b*(a*g))
    rw [classOf_eq_iff]
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_one] using hab

theorem permutationOperators_commute {ι : Type*} (e d : ι ≃ ι) (hed : Function.Commute e d) :
    Commute (permutationOperator e) (permutationOperator d) := by
  ext f q
  exact congrArg f (hed q).symm

#print axioms normalizer_old_transport
#print axioms normalizer_new_invariant_fixed
#print axioms normalizer_new_invariant_swap
#print axioms normalizerEquivs_commute

end QuantitativeNewGap
