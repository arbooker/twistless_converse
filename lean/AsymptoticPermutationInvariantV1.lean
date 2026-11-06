module

public import AsymptoticRegularFunctionalCalculusV1
public import AsymptoticIdentityObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPermutationInvariant

open AsymptoticRegularTrace AsymptoticFunctionalCalculus ContinuousLinearMap InnerProductSpace Filter Polynomial
open scoped lp Topology InnerProduct

variable {ι : Type*}

/-- Simultaneous permutation of row and column labels leaves the
matrix unchanged. This form is stable under strong operator limits. -/
def Invariant (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) : Prop :=
  ∀ g h,matrix B (e g) (e h)=matrix B g h

theorem invariant_one (e : ι ≃ ι) : Invariant e (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) := by
  classical
  intro g h
  simp [matrix,delta,Pi.single_apply,e.injective.eq_iff]

theorem invariant_add (e : ι ≃ ι) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (hC : Invariant e C) : Invariant e (B+C) := by
  intro g h
  change matrixCLM (e g) (e h) (B+C)=matrixCLM g h (B+C)
  simp only [map_add,matrixCLM_apply,hB g h,hC g h]

theorem invariant_sub (e : ι ≃ ι) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (hC : Invariant e C) : Invariant e (B-C) := by
  intro g h
  change matrixCLM (e g) (e h) (B-C)=matrixCLM g h (B-C)
  simp only [map_sub,matrixCLM_apply,hB g h,hC g h]

theorem invariant_smul (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (c : ℂ) : Invariant e (c • B) := by
  intro g h
  change matrixCLM (e g) (e h) (c • B)=matrixCLM g h (c • B)
  simp only [map_smul,matrixCLM_apply,hB g h]

theorem invariant_comp (e : ι ≃ ι) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (hC : Invariant e C) : Invariant e (B.comp C) := by
  intro g h
  rw [matrix_comp,matrix_comp,← e.tsum_eq (fun i => matrix B (e g) i*matrix C i (e h))]
  apply tsum_congr
  intro i
  rw [hB g i,hC i h]

theorem invariant_adjoint (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) : Invariant e B.adjoint := by
  intro g h
  rw [matrix_adjoint,matrix_adjoint,hB h g]

theorem invariant_pow (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (n : ℕ) : Invariant e (B^n) := by
  induction n with
  | zero => simpa only [pow_zero] using invariant_one e
  | succ n ih => exact invariant_comp e _ _ ih hB

theorem invariant_tsum {η : Type*} (e : ι ≃ ι)
    (B : η → ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (hs : Summable B) (hB : ∀ i,Invariant e (B i)) :
    Invariant e (∑' i,B i) := by
  intro g h
  rw [matrix_tsum B hs,matrix_tsum B hs]
  exact tsum_congr (fun i => hB i g h)

theorem invariant_strong_limit (e : ι ≃ ι)
    (B : ℕ → ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : ∀ n,Invariant e (B n)) (ht : ∀ v,Tendsto (fun n => B n v) atTop (𝓝 (C v))) :
    Invariant e C := by
  intro g h
  have h₁ := matrix_tendsto_of_strong B C ht (e g) (e h)
  have h₂ := matrix_tendsto_of_strong B C ht g h
  have he : (fun n => matrix (B n) (e g) (e h))=(fun n => matrix (B n) g h) :=
    funext (fun n => hB n g h)
  rw [he] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem invariant_polynomial (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (p : ℝ[X]) : Invariant e (aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact invariant_add e _ _ hp hq
  | monomial n c =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact invariant_smul e _ (invariant_pow e B hB n) (c:ℂ)

theorem invariant_cfc (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (hsa : IsSelfAdjoint B) (f : ℝ → ℝ) (hf : Continuous f) :
    Invariant e (value f B) := by
  obtain ⟨p,hp⟩ := AsymptoticFunctionalCalculus.exists_polynomial_approximation
    (fun _ : Unit => B) (fun _ => hsa) ‖B‖ (fun _ => le_rfl) f hf
  apply invariant_strong_limit e (fun n => aeval B (p n)) _ (fun n => invariant_polynomial e B hB (p n))
  intro v
  exact ((ContinuousLinearMap.apply ℂ ℓ²(ι,ℂ) v).continuous.tendsto _).comp (hp ())

theorem invariant_positiveRoot (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (hp : 0≤B) : Invariant e (positiveRoot B) := by
  rw [positiveRoot_eq_value B hp]
  exact invariant_cfc e B hB hp.isSelfAdjoint Real.sqrt Real.continuous_sqrt

theorem invariant_inverse (e : ι ≃ ι) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Invariant e B) (C : ℝ) (hC : ‖B‖≤C)
    (hc : ∀ v,‖v‖^2≤(⟪B v,v⟫_ℂ).re) :
    Invariant e (AsymptoticCoerciveNeumann.inverse C B) := by
  apply invariant_smul
  apply invariant_tsum
  · exact summable_geometric_of_norm_lt_one (AsymptoticCoerciveNeumann.step_norm_lt_one C B hC hc)
  · intro n
    apply invariant_pow
    exact invariant_sub e _ _ (invariant_one e) (invariant_smul e B hB _)

#print axioms invariant_one
#print axioms invariant_add
#print axioms invariant_sub
#print axioms invariant_smul
#print axioms invariant_comp
#print axioms invariant_adjoint
#print axioms invariant_pow
#print axioms invariant_tsum
#print axioms invariant_strong_limit
#print axioms invariant_polynomial
#print axioms invariant_cfc
#print axioms invariant_positiveRoot
#print axioms invariant_inverse

end AsymptoticPermutationInvariant
