module

public import AsymptoticFunctionalCalculusApproxV1
public import AsymptoticRegularInfiniteKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Filter Polynomial ContinuousLinearMap AsymptoticFunctionalCalculus
open scoped lp Topology

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

omit [Countable G] [MeasurableSpace α] in
theorem real_polynomial_covariant (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Covariant B)
    (p : ℝ[X]) : Covariant (fun x => aeval (B x) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add]
    exact covariant_add _ _ hp hq
  | monomial n c =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact covariant_smul (c:ℂ) _ (covariant_pow B hB n)

omit [Group G] [MulAction G α] in
theorem real_polynomial_matrix_measurable (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h)) (p : ℝ[X]) (g h : G) :
    Measurable (fun x => matrix (aeval (B x) p) g h) := by
  induction p using Polynomial.induction_on' generalizing g h with
  | add p q hp hq =>
    simp only [map_add]
    exact matrix_add_measurable _ _ hp hq g h
  | monomial n c =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact matrix_smul_measurable (c:ℂ) _ (matrix_pow_measurable B hB n) g h

/-- Continuous real functional calculus preserves the measurable matrix
coefficients and covariance of a uniformly bounded self-adjoint family.
The proof uses one scalar polynomial approximation for the whole family. -/
theorem cfc_regular (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
    (hsa : ∀ x,IsSelfAdjoint (B x)) (M : ℝ) (hM : ∀ x,‖B x‖≤M)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ g h,Measurable (fun x => matrix (value f (B x)) g h)) ∧
      Covariant (fun x => value f (B x)) := by
  obtain ⟨p,hp⟩ := AsymptoticFunctionalCalculus.exists_polynomial_approximation B hsa M hM f hf
  have hs (x : α) (v : ℓ²(G,ℂ)) :
      Tendsto (fun n => aeval (B x) (p n) v) atTop (𝓝 (value f (B x) v)) :=
    ((ContinuousLinearMap.apply ℂ ℓ²(G,ℂ) v).continuous.tendsto _).comp (hp x)
  exact ⟨strong_limit_matrix_measurable _ _ (fun n => real_polynomial_matrix_measurable B hm (p n)) hs,
    covariant_of_strong_limit _ _ (fun n => real_polynomial_covariant B hc (p n)) hs⟩

/-- In particular, the positive square-root family is regular. -/
theorem sqrt_regular (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
    (hp : ∀ x,0≤B x) (M : ℝ) (hM : ∀ x,‖B x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (positiveRoot (B x)) g h)) ∧
      Covariant (fun x => positiveRoot (B x)) := by
  have he (x : α) : positiveRoot (B x)=value Real.sqrt (B x) := by
    exact positiveRoot_eq_value (B x) (hp x)
  simp only [he]
  exact cfc_regular B hm hc (fun x => (hp x).isSelfAdjoint) M hM Real.sqrt Real.continuous_sqrt

#print axioms real_polynomial_covariant
#print axioms real_polynomial_matrix_measurable
#print axioms cfc_regular
#print axioms sqrt_regular

end AsymptoticRegularTrace
