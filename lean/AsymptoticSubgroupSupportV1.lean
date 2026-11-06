module

public import AsymptoticRegularFunctionalCalculusV1
public import AsymptoticIdentityObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubgroupSupport

open AsymptoticRegularTrace AsymptoticFunctionalCalculus ContinuousLinearMap InnerProductSpace Filter Polynomial
open scoped lp Topology InnerProduct

variable {G : Type*} [Group G]

/-- A subgroup-supported operator has no matrix entries between distinct
left-subgroup orbits. For the q-integral subgroup this is the support
condition used in the fresh-prime argument. -/
def Supported (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : Prop :=
  ∀ g h,g*h⁻¹∉S → matrix B g h=0

theorem supported_one (S : Subgroup G) : Supported S (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) := by
  classical
  intro g h hgh
  have hne : g≠h := by intro he; subst h; exact hgh (by simp)
  simp [matrix,delta,hne]

theorem supported_add (S : Subgroup G) (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (hC : Supported S C) : Supported S (B+C) := by
  intro g h hgh
  change matrixCLM g h (B+C)=0
  rw [map_add,matrixCLM_apply,matrixCLM_apply,hB g h hgh,hC g h hgh,add_zero]

theorem supported_sub (S : Subgroup G) (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (hC : Supported S C) : Supported S (B-C) := by
  intro g h hgh
  change matrixCLM g h (B-C)=0
  rw [map_sub,matrixCLM_apply,matrixCLM_apply,hB g h hgh,hC g h hgh,sub_zero]

theorem supported_smul (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (c : ℂ) : Supported S (c • B) := by
  intro g h hgh
  change matrixCLM g h (c • B)=0
  rw [map_smul,matrixCLM_apply,hB g h hgh,smul_zero]

theorem supported_comp (S : Subgroup G) (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (hC : Supported S C) : Supported S (B.comp C) := by
  intro g h hgh
  rw [matrix_comp]
  suffices hz : ∀ i,matrix B g i*matrix C i h=0 by simp only [hz,tsum_zero]
  intro i
  by_cases hgi : g*i⁻¹∈S
  · have hih : i*h⁻¹∉S := by
      intro hi
      exact hgh (by simpa only [mul_assoc,inv_mul_cancel_left] using S.mul_mem hgi hi)
    rw [hC i h hih,mul_zero]
  · rw [hB g i hgi,zero_mul]

theorem supported_adjoint (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) : Supported S B.adjoint := by
  intro g h hgh
  have hhg : h*g⁻¹∉S := by
    intro hh
    exact hgh (by simpa only [mul_inv_rev,inv_inv] using S.inv_mem hh)
  rw [matrix_adjoint,hB h g hhg,map_zero]

theorem supported_pow (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (n : ℕ) : Supported S (B^n) := by
  induction n with
  | zero => simpa only [pow_zero] using supported_one S
  | succ n ih => exact supported_comp S _ _ ih hB

theorem supported_tsum {ι : Type*} (S : Subgroup G)
    (B : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hs : Summable B) (hB : ∀ i,Supported S (B i)) :
    Supported S (∑' i,B i) := by
  intro g h hgh
  rw [matrix_tsum B hs]
  simpa only [tsum_zero] using tsum_congr (fun i => hB i g h hgh)

theorem supported_strong_limit (S : Subgroup G)
    (B : ℕ → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ n,Supported S (B n)) (ht : ∀ v,Tendsto (fun n => B n v) atTop (𝓝 (C v))) :
    Supported S C := by
  intro g h hgh
  have hc := matrix_tendsto_of_strong B C ht g h
  have hz : Tendsto (fun n => matrix (B n) g h) atTop (𝓝 0) := by
    simpa only [fun n => hB n g h hgh] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hc hz

theorem supported_polynomial (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (p : ℝ[X]) : Supported S (aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact supported_add S _ _ hp hq
  | monomial n c =>
    simp only [aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact supported_smul S _ (supported_pow S B hB n) (c:ℂ)

theorem supported_cfc (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (hsa : IsSelfAdjoint B) (f : ℝ → ℝ) (hf : Continuous f) :
    Supported S (value f B) := by
  obtain ⟨p,hp⟩ := AsymptoticFunctionalCalculus.exists_polynomial_approximation
    (fun _ : Unit => B) (fun _ => hsa) ‖B‖ (fun _ => le_rfl) f hf
  apply supported_strong_limit S (fun n => aeval B (p n)) _ (fun n => supported_polynomial S B hB (p n))
  intro v
  exact ((ContinuousLinearMap.apply ℂ ℓ²(G,ℂ) v).continuous.tendsto _).comp (hp ())

theorem supported_positiveRoot (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (hp : 0≤B) : Supported S (positiveRoot B) := by
  rw [positiveRoot_eq_value B hp]
  exact supported_cfc S B hB hp.isSelfAdjoint Real.sqrt Real.continuous_sqrt

theorem supported_inverse (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (C : ℝ) (hC : ‖B‖≤C)
    (hc : ∀ v,‖v‖^2≤(⟪B v,v⟫_ℂ).re) :
    Supported S (AsymptoticCoerciveNeumann.inverse C B) := by
  apply supported_smul
  apply supported_tsum
  · exact summable_geometric_of_norm_lt_one (AsymptoticCoerciveNeumann.step_norm_lt_one C B hC hc)
  · intro n
    apply supported_pow
    exact supported_sub S _ _ (supported_one S) (supported_smul S B hB _)

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

end AsymptoticSubgroupSupport
