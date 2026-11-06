module

public import QuantitativeEulerDensityGeneratorsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic
open scoped MatrixGroups

theorem leading_times_trailing (N : ℕ) (A : SL(2,ℤ)) (hA : A∈Gamma0 N) :
    (A 0 0 : ZMod N)*(A 1 1 : ZMod N)=1 := by
  have hd := congrArg (fun x : ℤ => (x : ZMod N)) A.property
  rw [det_fin_two] at hd
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,Gamma0_mem.mp hA,mul_zero,sub_zero] using hd

/-- Two actual Γ₀ matrices with the same leading residue differ by an
actual Γ₁ matrix. This supplies the diamond quotient cancellation used
for the canonical prime matrices. -/
theorem same_residue_quotient (N : ℕ) (A B : SL(2,ℤ))
    (hA : A∈Gamma0 N) (hB : B∈Gamma0 N)
    (hab : (A 0 0 : ZMod N)=(B 0 0 : ZMod N)) : A⁻¹*B∈Gamma1 N := by
  have ha := leading_times_trailing N A hA
  have hb := leading_times_trailing N B hB
  rw [Gamma1_mem]
  simp only [SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_inv,adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  change
    ((A 1 1*B 0 0+(-A 0 1)*B 1 0 : ℤ) : ZMod N)=1 ∧
    (((-A 1 0)*B 0 1+A 0 0*B 1 1 : ℤ) : ZMod N)=1 ∧
    (((-A 1 0)*B 0 0+A 0 0*B 1 0 : ℤ) : ZMod N)=0
  simp only [Int.cast_add,Int.cast_mul,Int.cast_neg,Gamma0_mem.mp hA,Gamma0_mem.mp hB,
    neg_zero,zero_mul,mul_zero,zero_add,add_zero]
  exact ⟨by rw [←hab,mul_comm]; exact ha, by rw [hab]; exact hb, trivial⟩

theorem leading_unit (N : ℕ) (A : SL(2,ℤ)) (hA : A∈Gamma0 N) :
    IsUnit (A 0 0 : ZMod N) :=
  isUnit_iff_exists_inv.mpr ⟨(A 1 1 : ZMod N),leading_times_trailing N A hA⟩

theorem exists_leading_residue (N : ℕ) [NeZero N] (A : SL(2,ℤ)) (hA : A∈Gamma0 N) :
    ∃ a : UnitResidue N, (A 0 0 : ZMod N)=(a.val.val : ZMod N) := by
  let z : ZMod N := A 0 0
  have hu : IsUnit (z.val : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    exact leading_unit N A hA
  exact ⟨⟨⟨z.val,z.val_lt⟩,(ZMod.isUnit_iff_coprime _ _).mp hu⟩,
    (ZMod.natCast_zmod_val z).symm⟩

/-- The explicit finite unit lifts together with Γ₁ generate Γ₀. No
surjectivity or quotient-generation assertion is left as an assumption. -/
theorem gamma0_generated_by_lifts (N : ℕ) [NeZero N] :
    Gamma0 N=Gamma1 N ⊔ Subgroup.closure (Set.range (unitLift N)) := by
  apply le_antisymm
  · intro A hA
    obtain ⟨a,ha⟩ := exists_leading_residue N A hA
    have hq : (unitLift N a)⁻¹*A∈Gamma1 N :=
      same_residue_quotient N _ _ (unitLift_mem N a) hA (by
        simpa [unitLift] using ha.symm)
    have hl : unitLift N a∈Subgroup.closure (Set.range (unitLift N)) :=
      Subgroup.subset_closure ⟨a,rfl⟩
    have hp := (Gamma1 N ⊔ Subgroup.closure (Set.range (unitLift N))).mul_mem
      ((show Subgroup.closure (Set.range (unitLift N)) ≤
        Gamma1 N ⊔ Subgroup.closure (Set.range (unitLift N)) from le_sup_right) hl)
      ((show Gamma1 N ≤ Gamma1 N ⊔ Subgroup.closure (Set.range (unitLift N)) from le_sup_left) hq)
    simpa only [mul_inv_cancel_left] using hp
  · apply sup_le (Gamma1_in_Gamma0 N)
    rw [Subgroup.closure_le]
    rintro _ ⟨a,rfl⟩
    exact unitLift_mem N a

#print axioms same_residue_quotient
#print axioms exists_leading_residue
#print axioms gamma0_generated_by_lifts
end QuantitativeEulerDensityGenerators
