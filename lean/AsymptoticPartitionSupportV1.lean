module

public import AsymptoticRegularFunctionalCalculusV1
public import AsymptoticIdentityObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPartitionSupport

open AsymptoticRegularTrace AsymptoticFunctionalCalculus ContinuousLinearMap InnerProductSpace Filter Polynomial
open scoped lp Topology InnerProduct

variable {ι κ : Type*}

/-- A bounded operator respects a partition when its matrix vanishes
between different fibres. The index type need not be a group. -/
def Supported (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) : Prop :=
  ∀ g h,partition g≠partition h → matrix B g h=0

theorem supported_one (partition : ι → κ) : Supported partition (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) := by
  classical
  intro g h hgh
  have hne : g≠h := fun he => hgh (congrArg partition he)
  simp [matrix,delta,hne]

theorem supported_add (partition : ι → κ) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (hC : Supported partition C) : Supported partition (B+C) := by
  intro g h hgh
  change matrixCLM g h (B+C)=0
  rw [map_add,matrixCLM_apply,matrixCLM_apply,hB g h hgh,hC g h hgh,add_zero]

theorem supported_sub (partition : ι → κ) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (hC : Supported partition C) : Supported partition (B-C) := by
  intro g h hgh
  change matrixCLM g h (B-C)=0
  rw [map_sub,matrixCLM_apply,matrixCLM_apply,hB g h hgh,hC g h hgh,sub_zero]

theorem supported_smul (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (c : ℂ) : Supported partition (c • B) := by
  intro g h hgh
  change matrixCLM g h (c • B)=0
  rw [map_smul,matrixCLM_apply,hB g h hgh,smul_zero]

theorem supported_comp (partition : ι → κ) (B C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (hC : Supported partition C) : Supported partition (B.comp C) := by
  intro g h hgh
  rw [matrix_comp]
  suffices hz : ∀ i,matrix B g i*matrix C i h=0 by simp only [hz,tsum_zero]
  intro i
  by_cases hgi : partition g=partition i
  · have hih : partition i≠partition h := fun hi => hgh (hgi.trans hi)
    rw [hC i h hih,mul_zero]
  · rw [hB g i hgi,zero_mul]

theorem supported_adjoint (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) : Supported partition B.adjoint := by
  intro g h hgh
  rw [matrix_adjoint,hB h g hgh.symm,map_zero]

theorem supported_pow (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (n : ℕ) : Supported partition (B^n) := by
  induction n with
  | zero => simpa only [pow_zero] using supported_one partition
  | succ n ih => exact supported_comp partition _ _ ih hB

theorem supported_tsum {η : Type*} (partition : ι → κ)
    (B : η → ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (hs : Summable B) (hB : ∀ i,Supported partition (B i)) :
    Supported partition (∑' i,B i) := by
  intro g h hgh
  rw [matrix_tsum B hs]
  simpa only [tsum_zero] using tsum_congr (fun i => hB i g h hgh)

theorem supported_strong_limit (partition : ι → κ)
    (B : ℕ → ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (C : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : ∀ n,Supported partition (B n)) (ht : ∀ v,Tendsto (fun n => B n v) atTop (𝓝 (C v))) :
    Supported partition C := by
  intro g h hgh
  have hc := matrix_tendsto_of_strong B C ht g h
  have hz : Tendsto (fun n => matrix (B n) g h) atTop (𝓝 0) := by
    simpa only [fun n => hB n g h hgh] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hc hz

theorem supported_polynomial (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (p : ℝ[X]) : Supported partition (aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact supported_add partition _ _ hp hq
  | monomial n c =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact supported_smul partition _ (supported_pow partition B hB n) (c:ℂ)

theorem supported_cfc (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (hsa : IsSelfAdjoint B) (f : ℝ → ℝ) (hf : Continuous f) :
    Supported partition (value f B) := by
  obtain ⟨p,hp⟩ := AsymptoticFunctionalCalculus.exists_polynomial_approximation
    (fun _ : Unit => B) (fun _ => hsa) ‖B‖ (fun _ => le_rfl) f hf
  apply supported_strong_limit partition (fun n => aeval B (p n)) _ (fun n => supported_polynomial partition B hB (p n))
  intro v
  exact ((ContinuousLinearMap.apply ℂ ℓ²(ι,ℂ) v).continuous.tendsto _).comp (hp ())

theorem supported_positiveRoot (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (hp : 0≤B) : Supported partition (positiveRoot B) := by
  rw [positiveRoot_eq_value B hp]
  exact supported_cfc partition B hB hp.isSelfAdjoint Real.sqrt Real.continuous_sqrt

theorem supported_inverse (partition : ι → κ) (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hB : Supported partition B) (C : ℝ) (hC : ‖B‖≤C)
    (hc : ∀ v,‖v‖^2≤(⟪B v,v⟫_ℂ).re) :
    Supported partition (AsymptoticCoerciveNeumann.inverse C B) := by
  apply supported_smul
  apply supported_tsum
  · exact summable_geometric_of_norm_lt_one (AsymptoticCoerciveNeumann.step_norm_lt_one C B hC hc)
  · intro n
    apply supported_pow
    exact supported_sub partition _ _ (supported_one partition) (supported_smul partition B hB _)

#print axioms supported_one
#print axioms supported_add
#print axioms supported_sub
#print axioms supported_smul
#print axioms supported_comp
#print axioms supported_adjoint
#print axioms supported_pow
#print axioms supported_tsum
#print axioms supported_strong_limit
#print axioms supported_polynomial
#print axioms supported_cfc
#print axioms supported_positiveRoot
#print axioms supported_inverse

end AsymptoticPartitionSupport
