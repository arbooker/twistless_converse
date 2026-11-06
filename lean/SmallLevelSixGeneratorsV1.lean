module

public import SmallLevelHalfConjugateLevelV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def sixLetter : Fin 7 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower 6
  | 3 => (lower 6)⁻¹
  | 4 => -1
  | 5 => halfConjugate 3
  | 6 => (halfConjugate 3)⁻¹

def sixWord (w : List (Fin 7)) : SL(2,ℤ) := (w.map sixLetter).prod

theorem sixWord_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 6∈K) (hZ : -1∈K) (hA : halfConjugate 3∈K)
    (w : List (Fin 7)) : sixWord w∈K := by
  have hl (i : Fin 7) : sixLetter i∈K := by
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

def rep6 (A : SL(2,ZMod 6)) : SL(2,ℤ) :=
  match (A.1 1 0).val*6+(A.1 1 1).val with
  | 6 | 30 => ⟨!![0,-1;1,0], by decide⟩
  | 7 | 35 => ⟨!![0,-1;1,1], by decide⟩
  | 11 | 31 => ⟨!![-1,0;1,-1], by decide⟩
  | 8 | 34 => ⟨!![0,-1;1,2], by decide⟩
  | 17 | 25 => ⟨!![-1,0;2,-1], by decide⟩
  | 9 | 33 => ⟨!![0,-1;1,3], by decide⟩
  | 13 | 29 => ⟨!![-1,-1;2,1], by decide⟩
  | 19 | 23 => ⟨!![-1,0;3,-1], by decide⟩
  | 10 | 32 => ⟨!![0,-1;1,4], by decide⟩
  | 15 | 27 => ⟨!![-1,-2;2,3], by decide⟩
  | 20 | 22 => ⟨!![-1,-1;3,2], by decide⟩
  | _ => 1

def edge6S (A : SL(2,ZMod 6)) : List (Fin 7) :=
  match (A.1 1 0).val*6+(A.1 1 1).val with
  | 6 | 30 => [4]
  | 11 | 31 => [4]
  | 17 | 25 => [4]
  | 13 | 29 => [1, 2]
  | 19 | 23 => [4]
  | 10 | 32 => [3, 0, 4]
  | 15 | 27 => [1, 4, 6, 0]
  | 20 | 22 => [1, 5, 0]
  | _ => []

theorem edge6S_checked : ∀ A : SL(2,ZMod 6),
    rep6 A*S*(rep6 (A*reduction 6 S))⁻¹ = sixWord (edge6S A) := by decide

def edge6T (A : SL(2,ZMod 6)) : List (Fin 7) :=
  match (A.1 1 0).val*6+(A.1 1 1).val with
  | 1 | 5 => [0]
  | 11 | 31 => [1]
  | 10 | 32 => [3, 0]
  | 15 | 27 => [1, 6, 0]
  | 20 | 22 => [1, 5, 2]
  | _ => []

theorem edge6T_checked : ∀ A : SL(2,ZMod 6),
    rep6 A*T*(rep6 (A*reduction 6 T))⁻¹ = sixWord (edge6T A) := by decide

theorem rep6_one : rep6 1=1 := by decide

theorem rep6_upper : ∀ A : SL(2,ZMod 6), A.1 1 0=0 → rep6 A=1 := by decide

theorem gamma0_6_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 6∈K) (hZ : -1∈K) (hA : halfConjugate 3∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 6) : γ∈K := by
  apply transversal_mem (reduction 6) rep6 K
  · intro A
    rw [edge6S_checked]
    exact sixWord_mem K hT hU hZ hA _
  · intro A
    rw [edge6T_checked]
    exact sixWord_mem K hT hU hZ hA _
  · exact rep6_one
  · apply rep6_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge6S_checked
#print axioms edge6T_checked
#print axioms gamma0_6_mem

end SmallLevelGenerators
