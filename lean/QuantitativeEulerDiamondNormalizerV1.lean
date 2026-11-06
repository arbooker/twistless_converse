module

public import QuantitativeEulerDiamondPrimesV1
public import QuantitativeArithmeticShiftedCertificateDefectV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic
open scoped MatrixGroups

/-- Actual congruence normality, used to turn fixed branch comparisons
into Γ₁ generator words. -/
theorem gamma1_conjugate (N : ℕ) (A B : SL(2,ℤ))
    (hA : A∈Gamma0 N) (hB : B∈Gamma1 N) : A⁻¹*B*A∈Gamma1 N := by
  have hb := (Gamma1_mem N B).mp hB
  have hr : (A 0 0 : ZMod N)=((B*A) 0 0 : ZMod N) := by
    simp only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Int.cast_add,Int.cast_mul,hb.1,Gamma0_mem.mp hA,one_mul,mul_zero,add_zero]
  simpa only [mul_assoc] using same_residue_quotient N A (B*A) hA
    ((Gamma0 N).mul_mem (Gamma1_in_Gamma0 N hB) hA) hr

def frickeConjugate (N : ℕ) (A : SL(2,ℤ)) (hA : A∈Gamma0 N) : SL(2,ℤ) :=
  ⟨!![A 1 1,-(A 1 0/(N : ℤ)); -(N : ℤ)*A 0 1,A 0 0],by
    have hc : (N : ℤ)*(A 1 0/(N : ℤ))=A 1 0 :=
      Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA)
    have hd := A.property
    rw [det_fin_two] at hd ⊢
    change A 1 1*A 0 0-(-(A 1 0/(N : ℤ)))*(-(N : ℤ)*A 0 1)=1
    nlinarith [congrArg (fun x : ℤ => x*A 0 1) hc]⟩

/-- W_N A equals the integral conjugate times W_N exactly, before
passing to a projective group or imposing any automorphy equation. -/
theorem frickeConjugate_identity (N : ℕ) (A : SL(2,ℤ)) (hA : A∈Gamma0 N) :
    integralFrickeMatrix N*A.val=(frickeConjugate N A hA).val*integralFrickeMatrix N := by
  have hc : (A 1 0/(N : ℤ))*(N : ℤ)=A 1 0 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralFrickeMatrix,frickeConjugate,Matrix.mul_apply,Fin.sum_univ_two,hc]
  all_goals ring

theorem frickeConjugate_gamma1 (N : ℕ) (A : SL(2,ℤ)) (hA : A∈Gamma1 N) :
    frickeConjugate N A (Gamma1_in_Gamma0 N hA)∈Gamma1 N := by
  have ha := (Gamma1_mem N A).mp hA
  rw [Gamma1_mem]
  change (A 1 1 : ZMod N)=1 ∧ (A 0 0 : ZMod N)=1 ∧
    ((-(N : ℤ)*A 0 1 : ℤ) : ZMod N)=0
  exact ⟨ha.2.1,ha.1,by simp⟩

/-- At level one no nonzero-leading-entry certificate is needed:
the two unipotent matrices themselves generate the full modular group. -/
def levelOneLower : SL(2,ℤ) :=
  ⟨!![1,0;1,1],by norm_num [det_fin_two]⟩

theorem levelOneS : ModularGroup.S=ModularGroup.T⁻¹*levelOneLower*ModularGroup.T⁻¹ := by
  decide

theorem levelOne_generators :
    Subgroup.closure ({ModularGroup.T,levelOneLower} : Set SL(2,ℤ))=⊤ := by
  apply top_unique
  rw [←SpecialLinearGroup.SL2Z_generators]
  rw [Subgroup.closure_le]
  have ht : ModularGroup.T∈Subgroup.closure ({ModularGroup.T,levelOneLower} : Set SL(2,ℤ)) :=
    Subgroup.subset_closure (by simp)
  have hv : levelOneLower∈Subgroup.closure ({ModularGroup.T,levelOneLower} : Set SL(2,ℤ)) :=
    Subgroup.subset_closure (by simp)
  intro A hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl
  · rw [levelOneS]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hv)
      (Subgroup.inv_mem _ ht)
  · exact ht

theorem levelOneLower_matrix : levelOneLower.val=lowerUnipotent 1 1 := rfl

#print axioms gamma1_conjugate
#print axioms frickeConjugate_identity
#print axioms frickeConjugate_gamma1
#print axioms levelOne_generators
end QuantitativeEulerDensityGenerators
