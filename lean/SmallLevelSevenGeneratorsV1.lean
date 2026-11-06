module

public import SmallLevelOddWordsV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def rep7 (A : SL(2,ZMod 7)) : SL(2,ℤ) :=
  match (A.1 1 0).val*7+(A.1 1 1).val with
  | 7 | 14 | 21 | 28 | 35 | 42 => ⟨!![0,-1;1,0], by decide⟩
  | 8 | 16 | 24 | 32 | 40 | 48 => ⟨!![0,-1;1,1], by decide⟩
  | 13 | 19 | 25 | 31 | 37 | 43 => ⟨!![-1,0;1,-1], by decide⟩
  | 9 | 18 | 27 | 29 | 38 | 47 => ⟨!![0,-1;1,2], by decide⟩
  | 10 | 20 | 23 | 33 | 36 | 46 => ⟨!![-1,0;2,-1], by decide⟩
  | 11 | 15 | 26 | 30 | 41 | 45 => ⟨!![-1,-1;2,1], by decide⟩
  | 12 | 17 | 22 | 34 | 39 | 44 => ⟨!![-1,1;1,-2], by decide⟩
  | _ => 1

def edge7S (A : SL(2,ZMod 7)) : List (Fin 7) :=
  match (A.1 1 0).val*7+(A.1 1 1).val with
  | 7 | 14 | 21 | 28 | 35 | 42 => [4]
  | 13 | 19 | 25 | 31 | 37 | 43 => [4]
  | 10 | 20 | 23 | 33 | 36 | 46 => [4]
  | 12 | 17 | 22 | 34 | 39 | 44 => [4]
  | _ => []

theorem edge7S_checked : ∀ A : SL(2,ZMod 7),
    rep7 A*S*(rep7 (A*reduction 7 S))⁻¹ =
      oddWord 7 4 (by decide) (edge7S A) := by decide

def edge7T (A : SL(2,ZMod 7)) : List (Fin 7) :=
  match (A.1 1 0).val*7+(A.1 1 1).val with
  | 1 | 2 | 3 | 4 | 5 | 6 => [0]
  | 13 | 19 | 25 | 31 | 37 | 43 => [1]
  | 9 | 18 | 27 | 29 | 38 | 47 => [6, 0]
  | 11 | 15 | 26 | 30 | 41 | 45 => [1, 5, 3, 0]
  | _ => []

theorem edge7T_checked : ∀ A : SL(2,ZMod 7),
    rep7 A*T*(rep7 (A*reduction 7 T))⁻¹ =
      oddWord 7 4 (by decide) (edge7T A) := by decide

theorem rep7_one : rep7 1=1 := by decide

theorem rep7_upper : ∀ A : SL(2,ZMod 7), A.1 1 0=0 → rep7 A=1 := by decide

theorem gamma0_7_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 7∈K) (hZ : -1∈K)
    (hA : oddMatrix 7 4 (by decide)∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 7) : γ∈K := by
  apply transversal_mem (reduction 7) rep7 K
  · intro A
    rw [edge7S_checked]
    exact oddWord_mem 7 4 (by decide) K hT hU hZ hA _
  · intro A
    rw [edge7T_checked]
    exact oddWord_mem 7 4 (by decide) K hT hU hZ hA _
  · exact rep7_one
  · apply rep7_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge7S_checked
#print axioms edge7T_checked
#print axioms gamma0_7_mem

end SmallLevelGenerators
