module

public import SmallLevelOddWordsV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def rep5 (A : SL(2,ZMod 5)) : SL(2,ℤ) :=
  match (A.1 1 0).val*5+(A.1 1 1).val with
  | 5 | 10 | 15 | 20 => ⟨!![0,-1;1,0], by decide⟩
  | 6 | 12 | 18 | 24 => ⟨!![0,-1;1,1], by decide⟩
  | 9 | 13 | 17 | 21 => ⟨!![-1,0;1,-1], by decide⟩
  | 7 | 14 | 16 | 23 => ⟨!![0,-1;1,2], by decide⟩
  | 8 | 11 | 19 | 22 => ⟨!![0,-1;1,3], by decide⟩
  | _ => 1

def edge5S (A : SL(2,ZMod 5)) : List (Fin 7) :=
  match (A.1 1 0).val*5+(A.1 1 1).val with
  | 5 | 10 | 15 | 20 => [4]
  | 9 | 13 | 17 | 21 => [4]
  | 7 | 14 | 16 | 23 => [1, 5]
  | 8 | 11 | 19 | 22 => [6, 2]
  | _ => []

theorem edge5S_checked : ∀ A : SL(2,ZMod 5),
    rep5 A*S*(rep5 (A*reduction 5 S))⁻¹ =
      oddWord 5 3 (by decide) (edge5S A) := by decide

def edge5T (A : SL(2,ZMod 5)) : List (Fin 7) :=
  match (A.1 1 0).val*5+(A.1 1 1).val with
  | 1 | 2 | 3 | 4 => [0]
  | 9 | 13 | 17 | 21 => [1]
  | 8 | 11 | 19 | 22 => [3, 0]
  | _ => []

theorem edge5T_checked : ∀ A : SL(2,ZMod 5),
    rep5 A*T*(rep5 (A*reduction 5 T))⁻¹ =
      oddWord 5 3 (by decide) (edge5T A) := by decide

theorem rep5_one : rep5 1=1 := by decide

theorem rep5_upper : ∀ A : SL(2,ZMod 5), A.1 1 0=0 → rep5 A=1 := by decide

theorem gamma0_5_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 5∈K) (hZ : -1∈K)
    (hA : oddMatrix 5 3 (by decide)∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 5) : γ∈K := by
  apply transversal_mem (reduction 5) rep5 K
  · intro A
    rw [edge5S_checked]
    exact oddWord_mem 5 3 (by decide) K hT hU hZ hA _
  · intro A
    rw [edge5T_checked]
    exact oddWord_mem 5 3 (by decide) K hT hU hZ hA _
  · exact rep5_one
  · apply rep5_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge5S_checked
#print axioms edge5T_checked
#print axioms gamma0_5_mem

end SmallLevelGenerators
