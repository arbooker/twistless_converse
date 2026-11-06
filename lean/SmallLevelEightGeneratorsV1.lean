module

public import SmallLevelHalfConjugateV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def eightLetter : Fin 7 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower 8
  | 3 => (lower 8)⁻¹
  | 4 => -1
  | 5 => halfConjugate 2
  | 6 => (halfConjugate 2)⁻¹

def eightWord (w : List (Fin 7)) : SL(2,ℤ) := (w.map eightLetter).prod

theorem eightWord_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 8∈K) (hZ : -1∈K) (hA : halfConjugate 2∈K)
    (w : List (Fin 7)) : eightWord w∈K := by
  have hl (i : Fin 7) : eightLetter i∈K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
    · exact hA
    · exact K.inv_mem hA
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rep8 (A : SL(2,ZMod 8)) : SL(2,ℤ) :=
  match (A.1 1 0).val*8+(A.1 1 1).val with
  | 8 | 24 | 40 | 56 => ⟨!![0,-1;1,0], by decide⟩
  | 9 | 27 | 45 | 63 => ⟨!![0,-1;1,1], by decide⟩
  | 15 | 29 | 43 | 57 => ⟨!![-1,0;1,-1], by decide⟩
  | 10 | 30 | 42 | 62 => ⟨!![0,-1;1,2], by decide⟩
  | 19 | 23 | 49 | 53 => ⟨!![-1,0;2,-1], by decide⟩
  | 11 | 25 | 47 | 61 => ⟨!![0,-1;1,3], by decide⟩
  | 17 | 21 | 51 | 55 => ⟨!![-1,-1;2,1], by decide⟩
  | 13 | 31 | 41 | 59 => ⟨!![-1,0;3,-1], by decide⟩
  | 12 | 28 | 44 | 60 => ⟨!![0,-1;1,4], by decide⟩
  | 14 | 26 | 46 | 58 => ⟨!![-1,1;1,-2], by decide⟩
  | 33 | 35 | 37 | 39 => ⟨!![-1,0;4,-1], by decide⟩
  | _ => 1

def edge8S (A : SL(2,ZMod 8)) : List (Fin 7) :=
  match (A.1 1 0).val*8+(A.1 1 1).val with
  | 8 | 24 | 40 | 56 => [4]
  | 15 | 29 | 43 | 57 => [4]
  | 19 | 23 | 49 | 53 => [4]
  | 13 | 31 | 41 | 59 => [4]
  | 14 | 26 | 46 | 58 => [4]
  | 33 | 35 | 37 | 39 => [4]
  | _ => []

theorem edge8S_checked : ∀ A : SL(2,ZMod 8),
    rep8 A*S*(rep8 (A*reduction 8 S))⁻¹ = eightWord (edge8S A) := by decide

def edge8T (A : SL(2,ZMod 8)) : List (Fin 7) :=
  match (A.1 1 0).val*8+(A.1 1 1).val with
  | 1 | 3 | 5 | 7 => [0]
  | 15 | 29 | 43 | 57 => [1]
  | 17 | 21 | 51 | 55 => [1, 6, 0]
  | 13 | 31 | 41 | 59 => [1, 4, 5, 0]
  | 12 | 28 | 44 | 60 => [3, 4, 6, 0]
  | 33 | 35 | 37 | 39 => [1, 5, 2]
  | _ => []

theorem edge8T_checked : ∀ A : SL(2,ZMod 8),
    rep8 A*T*(rep8 (A*reduction 8 T))⁻¹ = eightWord (edge8T A) := by decide

theorem rep8_one : rep8 1=1 := by decide

theorem rep8_upper : ∀ A : SL(2,ZMod 8), A.1 1 0=0 → rep8 A=1 := by decide

theorem gamma0_8_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 8∈K) (hZ : -1∈K) (hA : halfConjugate 2∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 8) : γ∈K := by
  apply transversal_mem (reduction 8) rep8 K
  · intro A
    rw [edge8S_checked]
    exact eightWord_mem K hT hU hZ hA _
  · intro A
    rw [edge8T_checked]
    exact eightWord_mem K hT hU hZ hA _
  · exact rep8_one
  · apply rep8_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge8S_checked
#print axioms edge8T_checked
#print axioms gamma0_8_mem

end SmallLevelGenerators
