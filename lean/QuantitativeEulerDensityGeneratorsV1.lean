module

public import AsymptoticCongruenceGeneratorsV1
public import QuantitativeArithmeticShiftedDensityCertificatesPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic
open scoped MatrixGroups

/-- The actual principal-character congruence subgroup is finitely generated,
by finite index in SL₂(ℤ). -/
theorem exists_gamma1_generators (N : ℕ) [NeZero N] :
    ∃ S : Finset SL(2,ℤ), Subgroup.closure (S : Set SL(2,ℤ))=Gamma1 N := by
  let : Group.FG SL(2,ℤ) := Group.fg_iff.mpr
    ⟨{ModularGroup.S,ModularGroup.T},SpecialLinearGroup.SL2Z_generators,Set.toFinite _⟩
  have hf : (Gamma1 N).FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  obtain ⟨S,hS,hfin⟩ := (Subgroup.fg_iff _).mp hf
  exact ⟨hfin.toFinset,by simpa only [Set.Finite.coe_toFinset] using hS⟩

def generators (N : ℕ) [NeZero N] : Finset SL(2,ℤ) :=
  (exists_gamma1_generators N).choose

theorem generators_closure (N : ℕ) [NeZero N] :
    Subgroup.closure (generators N : Set SL(2,ℤ))=Gamma1 N :=
  (exists_gamma1_generators N).choose_spec

abbrev Generator (N : ℕ) [NeZero N] := {γ : SL(2,ℤ) // γ∈generators N}

theorem generator_mem (N : ℕ) [NeZero N] (γ : Generator N) : γ.val∈Gamma1 N := by
  rw [←generators_closure N]
  exact Subgroup.subset_closure γ.property

/-- An explicit Bezout lift of each unit residue, with lower-left entry N.
No surjectivity of an unspecified residue homomorphism is assumed. -/
def unitLift (N : ℕ) (a : UnitResidue N) : SL(2,ℤ) :=
  ⟨!![(a.val.val : ℤ),-Nat.gcdB a.val.val N; (N : ℤ),Nat.gcdA a.val.val N],by
    have hb := Nat.gcd_eq_gcd_ab a.val.val N
    rw [a.property] at hb
    rw [det_fin_two]
    change (a.val.val : ℤ)*Nat.gcdA a.val.val N -
      (-Nat.gcdB a.val.val N)*(N : ℤ)=1
    calc
      _ = (a.val.val : ℤ)*Nat.gcdA a.val.val N + (N : ℤ)*Nat.gcdB a.val.val N := by ring
      _ = 1 := by simpa only [Nat.cast_one] using hb.symm⟩

theorem unitLift_mem (N : ℕ) (a : UnitResidue N) : unitLift N a∈Gamma0 N := by
  change ((N : ℤ) : ZMod N)=0
  simp

def family (N : ℕ) [NeZero N] (a : UnitResidue N) : Option (Generator N) → SL(2,ℤ)
  | none => unitLift N a
  | some γ => unitLift N a * γ.val

theorem family_mem (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    family N a i∈Gamma0 N := by
  cases i with
  | none => exact unitLift_mem N a
  | some γ =>
    exact (Gamma0 N).mul_mem (unitLift_mem N a)
      (Gamma1_in_Gamma0 N (generator_mem N γ))

theorem family_residue (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    (family N a i 0 0 : ZMod N)=(a.val.val : ZMod N) := by
  cases i with
  | none => simp [family,unitLift]
  | some γ =>
    have hg := (Gamma1_mem N γ.val).mp (generator_mem N γ)
    change (((unitLift N a).val * γ.val.val) 0 0 : ZMod N)=_
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul,hg.1,hg.2.2,
      mul_one,mul_zero,add_zero]
    simp [unitLift]

theorem family_leading_nonzero (N : ℕ) [NeZero N] (hN : 2≤N)
    (a : UnitResidue N) (i : Option (Generator N)) : family N a i 0 0≠0 := by
  intro hz
  have ha := family_residue N a i
  rw [hz,Int.cast_zero] at ha
  have hd : N∣a.val.val := (CharP.cast_eq_zero_iff (ZMod N) N a.val.val).mp ha.symm
  have ha0 := Nat.eq_zero_of_dvd_of_lt hd a.val.isLt
  have hN1 : N=1 := by simpa only [ha0,Nat.coprime_zero_left] using a.property
  omega

def lowerEntry (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) : ℤ :=
  family N a i 1 0 / (N : ℤ)

theorem lowerEntry_spec (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    (N : ℤ)*lowerEntry N a i=family N a i 1 0 := by
  exact Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (family_mem N a i))

theorem family_matrix (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    certificateMatrix (family N a i 0 0) (family N a i 0 1) N
      (lowerEntry N a i) (family N a i 1 1)=(family N a i).val := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [certificateMatrix,lowerEntry_spec]

theorem family_det (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    family N a i 0 0 * family N a i 1 1 -
      (N : ℤ)*lowerEntry N a i*family N a i 0 1=1 := by
  rw [lowerEntry_spec]
  have h := (family N a i).property
  rw [det_fin_two] at h
  nlinarith [h]

theorem family_residue_dvd (N : ℕ) [NeZero N] (a : UnitResidue N) (i : Option (Generator N)) :
    (N : ℤ)∣family N a i 0 0-(a.val.val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub,family_residue]
  simp

/-- The fixed generator is recovered from two members of the same residue
branch. This is the exact reason one fresh-prime residue suffices for Γ₁(N). -/
theorem generator_recovery (N : ℕ) [NeZero N] (a : UnitResidue N) (γ : Generator N) :
    (family N a none)⁻¹ * family N a (some γ)=γ.val := by
  simp [family]

#print axioms generators_closure
#print axioms family_leading_nonzero
#print axioms family_matrix
#print axioms family_det
#print axioms family_residue_dvd
#print axioms generator_recovery
end QuantitativeEulerDensityGenerators
