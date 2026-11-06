module

public import AsymptoticStackPolarV1
public import AsymptoticRegularPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry AsymptoticObservation
open AsymptoticObservationStack
open scoped lp

variable {G α ι : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α] [Fintype ι]

/-- The Gram family of a labelled stack is regular, with the labels
counted by the finite sum of row Gram operators. -/
theorem stack_gram_regular (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i)) :
    (∀ g h,Measurable (fun x => matrix ((stack (L x)).adjoint.comp (stack (L x))) g h)) ∧
      Covariant (fun x => (stack (L x)).adjoint.comp (stack (L x))) := by
  simp only [stack_gram]
  exact ⟨matrix_finsetSum_measurable Finset.univ _
    (fun i _ => matrix_comp_measurable _ _ (matrix_adjoint_measurable _ (hm i)) (hm i)),
    covariant_finsetSum Finset.univ _ (fun i _ => covariant_comp _ _ (covariant_adjoint _ (hc i)) (hc i))⟩

theorem stack_absolute_regular (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) :
    (∀ g h,Measurable (fun x => matrix (absolute (stack (L x))) g h)) ∧
      Covariant (fun x => absolute (stack (L x))) := by
  obtain ⟨hg,hcg⟩ := stack_gram_regular L hm hc
  have hb (x : α) : ‖(stack (L x)).adjoint.comp (stack (L x))‖≤M^2 := by
    rw [norm_adjoint_comp_self]
    nlinarith [hM x,norm_nonneg (stack (L x))]
  have hr := sqrt_regular (fun x => (stack (L x)).adjoint.comp (stack (L x))) hg hcg
    (fun x => nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self (stack (L x)))) (M^2) hb
  simpa only [← absolute_eq_positiveRoot] using hr

theorem stack_resolvent_regular (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) (n : ℕ) :
    (∀ g h,Measurable (fun x => matrix (AsymptoticPolarIsometry.resolvent (stack (L x)) n) g h)) ∧
      Covariant (fun x => AsymptoticPolarIsometry.resolvent (stack (L x)) n) := by
  obtain ⟨ha,hca⟩ := stack_absolute_regular L hm hc M hM
  have hroot := sqrt_regular (fun x => absolute (stack (L x))) ha hca
    (fun x => absolute_nonneg (stack (L x))) M (fun x => by rw [absolute_opNorm]; exact hM x)
  have hr : (∀ g h,Measurable (fun x => matrix (penaltyRoot (stack (L x))) g h)) ∧
      Covariant (fun x => penaltyRoot (stack (L x))) := by
    simpa only [← penaltyRoot_eq_positiveRoot] using hroot
  have hb (x : α) : ‖(((n+1:ℕ):ℂ) • penaltyRoot (stack (L x)))‖≤((n+1:ℕ):ℝ)*Real.sqrt M := by
    rw [norm_smul,Complex.norm_natCast,penaltyRoot_opNorm]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hM x)) (by positivity)
  have he := identity_observation_regular (fun x => (((n+1:ℕ):ℂ) • penaltyRoot (stack (L x))))
    (matrix_smul_measurable _ _ hr.1) (covariant_smul _ _ hr.2) _ hb
  simpa only [AsymptoticPolarIsometry.resolvent,amplified] using he

/-- Every row of the polar isometry of a labelled observation stack
inherits measurability and covariance from the original observation rows. -/
theorem stack_polarRow_regular (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) (i : ι) :
    (∀ g h,Measurable (fun x => matrix (polarRow (L x) i) g h)) ∧
      Covariant (fun x => polarRow (L x) i) := by
  have hr (n : ℕ) : (∀ g h,Measurable (fun x => matrix (regularizedRow (L x) n i) g h)) ∧
      Covariant (fun x => regularizedRow (L x) n i) := by
    obtain ⟨hb,hcb⟩ := stack_resolvent_regular L hm hc M hM n
    simp only [regularizedRow_formula]
    exact ⟨matrix_smul_measurable _ _ (matrix_comp_measurable _ _ (hm i) hb),
      covariant_smul _ _ (covariant_comp _ _ (hc i) hcb)⟩
  have ht := fun x v => polarRow_strong_limit (L x) i v
  exact ⟨strong_limit_matrix_measurable _ _ (fun n => (hr n).1) ht,
    covariant_of_strong_limit _ _ (fun n => (hr n).2) ht⟩

#print axioms stack_gram_regular
#print axioms stack_absolute_regular
#print axioms stack_resolvent_regular
#print axioms stack_polarRow_regular

end AsymptoticRegularTrace
