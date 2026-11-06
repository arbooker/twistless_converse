module

public import SmallLevelOddWordsV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def rep9 (A : SL(2,ZMod 9)) : SL(2,ℤ) :=
  match (A.1 1 0).val*9+(A.1 1 1).val with
  | 9 | 18 | 36 | 45 | 63 | 72 => ⟨!![0,-1;1,0], by decide⟩
  | 10 | 20 | 40 | 50 | 70 | 80 => ⟨!![0,-1;1,1], by decide⟩
  | 17 | 25 | 41 | 49 | 65 | 73 => ⟨!![-1,0;1,-1], by decide⟩
  | 11 | 22 | 44 | 46 | 68 | 79 => ⟨!![0,-1;1,2], by decide⟩
  | 13 | 26 | 43 | 47 | 64 | 77 => ⟨!![-1,0;2,-1], by decide⟩
  | 12 | 24 | 39 | 51 | 66 | 78 => ⟨!![0,-1;1,3], by decide⟩
  | 14 | 19 | 38 | 52 | 71 | 76 => ⟨!![-1,-1;2,1], by decide⟩
  | 29 | 32 | 35 | 55 | 58 | 61 => ⟨!![-1,0;3,-1], by decide⟩
  | 16 | 23 | 37 | 53 | 67 | 74 => ⟨!![-1,1;1,-2], by decide⟩
  | 15 | 21 | 42 | 48 | 69 | 75 => ⟨!![-1,-2;2,3], by decide⟩
  | 28 | 31 | 34 | 56 | 59 | 62 => ⟨!![-2,1;3,-2], by decide⟩
  | _ => 1

def edge9S (A : SL(2,ZMod 9)) : List (Fin 7) :=
  match (A.1 1 0).val*9+(A.1 1 1).val with
  | 9 | 18 | 36 | 45 | 63 | 72 => [4]
  | 17 | 25 | 41 | 49 | 65 | 73 => [4]
  | 13 | 26 | 43 | 47 | 64 | 77 => [4]
  | 29 | 32 | 35 | 55 | 58 | 61 => [4]
  | 16 | 23 | 37 | 53 | 67 | 74 => [4]
  | 28 | 31 | 34 | 56 | 59 | 62 => [4]
  | _ => []

theorem edge9S_checked : ∀ A : SL(2,ZMod 9),
    rep9 A*S*(rep9 (A*reduction 9 S))⁻¹ =
      oddWord 9 5 (by decide) (edge9S A) := by decide

def edge9T (A : SL(2,ZMod 9)) : List (Fin 7) :=
  match (A.1 1 0).val*9+(A.1 1 1).val with
  | 1 | 2 | 4 | 5 | 7 | 8 => [0]
  | 17 | 25 | 41 | 49 | 65 | 73 => [1]
  | 12 | 24 | 39 | 51 | 66 | 78 => [6, 0]
  | 29 | 32 | 35 | 55 | 58 | 61 => [1, 4, 5]
  | 15 | 21 | 42 | 48 | 69 | 75 => [1, 5, 3, 0]
  | 28 | 31 | 34 | 56 | 59 | 62 => [1, 2, 4, 6, 0]
  | _ => []

theorem edge9T_checked : ∀ A : SL(2,ZMod 9),
    rep9 A*T*(rep9 (A*reduction 9 T))⁻¹ =
      oddWord 9 5 (by decide) (edge9T A) := by decide

theorem rep9_one : rep9 1=1 := by decide

theorem rep9_upper : ∀ A : SL(2,ZMod 9), A.1 1 0=0 → rep9 A=1 := by decide

theorem gamma0_9_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 9∈K) (hZ : -1∈K)
    (hA : oddMatrix 9 5 (by decide)∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 9) : γ∈K := by
  apply transversal_mem (reduction 9) rep9 K
  · intro A
    rw [edge9S_checked]
    exact oddWord_mem 9 5 (by decide) K hT hU hZ hA _
  · intro A
    rw [edge9T_checked]
    exact oddWord_mem 9 5 (by decide) K hT hU hZ hA _
  · exact rep9_one
  · apply rep9_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge9S_checked
#print axioms edge9T_checked
#print axioms gamma0_9_mem

end SmallLevelGenerators
