module

public import SmallLevelSubgroupOrbitV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
@[expose] public section

namespace SmallLevelGenerators

open Matrix ModularGroup
open scoped MatrixGroups

def signTwo (A : SL(2,ZMod 2)) : ℤ :=
  match (A.1 0 0).val*8+(A.1 0 1).val*4+(A.1 1 0).val*2+(A.1 1 1).val with
  | 6 | 11 | 13 => -1
  | _ => 1

def signEight (A : SL(2,ZMod 8)) : ℤ :=
  if ((A.1 0 1).val+(A.1 1 0).val/4)%2=0 then 1 else -1

theorem signTwo_one : signTwo 1=1 := by decide
theorem signEight_one : signEight 1=1 := by decide

theorem signTwo_T : ∀ A : SL(2,ZMod 2),
    signTwo (A*reduction 2 T)= -signTwo A := by decide

theorem signTwo_U : ∀ A : SL(2,ZMod 2),
    signTwo (A*reduction 2 (lower 3))= -signTwo A := by decide

theorem signTwo_Z : ∀ A : SL(2,ZMod 2),
    signTwo (A*reduction 2 (-1))=signTwo A := by decide

theorem signEight_T : ∀ A : SL(2,ZMod 8), A.1 1 0=0 ∨ A.1 1 0=4 →
    signEight (A*reduction 8 T)= -signEight A := by decide

theorem signEight_U : ∀ A : SL(2,ZMod 8), A.1 1 0=0 ∨ A.1 1 0=4 →
    signEight (A*reduction 8 (lower 4))= -signEight A := by decide

theorem signEight_Z : ∀ A : SL(2,ZMod 8), A.1 1 0=0 ∨ A.1 1 0=4 →
    signEight (A*reduction 8 (-1))=signEight A := by decide

theorem signTwo_diagonal : ∀ A : SL(2,ZMod 2),
    A.1 0 1=0 → A.1 1 0=0 → signTwo A=1 := by decide

theorem signEight_even_upper (A : SL(2,ZMod 8)) (hc : A.1 1 0=0)
    (hb : (A.1 0 1).val%2=0) : signEight A=1 := by
  simp [signEight, hc, hb]

theorem eight_four_multiple : ∀ c : ZMod 8, 4*c=0 ∨ 4*c=4 := by decide
theorem eight_two_multiple : ∀ b : ZMod 8, (2*b).val%2=0 := by decide

theorem gamma_four_residue (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 4) :
    (reduction 8 A).1 1 0=0 ∨ (reduction 8 A).1 1 0=4 := by
  have hc : (4:ℤ)∣A 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (CongruenceSubgroup.Gamma0_mem.mp hA)
  obtain ⟨c,hc⟩ := hc
  change (A 1 0:ZMod 8)=0 ∨ (A 1 0:ZMod 8)=4
  rw [hc]
  push_cast
  exact eight_four_multiple _

#print axioms signTwo_T
#print axioms signTwo_U
#print axioms signTwo_Z
#print axioms signEight_T
#print axioms signEight_U
#print axioms signEight_Z
#print axioms gamma_four_residue

end SmallLevelGenerators
