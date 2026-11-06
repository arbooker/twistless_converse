module

public import SmallLevelTransversalV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def rep2 (A : SL(2,ZMod 2)) : SL(2,ℤ) :=
  match (A.1 1 0).val*2+(A.1 1 1).val with
  | 2 => S
  | 3 => S*T
  | _ => 1

def edge2S (A : SL(2,ZMod 2)) : List (Fin 5) :=
  match (A.1 1 0).val*2+(A.1 1 1).val with
  | 2 => [4]
  | 3 => [1, 2]
  | _ => []

theorem edge2S_checked : ∀ A : SL(2,ZMod 2),
    rep2 A*S*(rep2 (A*reduction 2 S))⁻¹ = word 2 (edge2S A) := by decide

def edge2T (A : SL(2,ZMod 2)) : List (Fin 5) :=
  match (A.1 1 0).val*2+(A.1 1 1).val with
  | 1 => [0]
  | 3 => [3]
  | _ => []

theorem edge2T_checked : ∀ A : SL(2,ZMod 2),
    rep2 A*T*(rep2 (A*reduction 2 T))⁻¹ = word 2 (edge2T A) := by decide

theorem rep2_one : rep2 1=1 := by decide

theorem rep2_upper : ∀ A : SL(2,ZMod 2), A.1 1 0=0 → rep2 A=1 := by decide

theorem gamma0_2_mem (K : Subgroup SL(2,ℤ))
    (hT : T ∈ K) (hU : lower 2 ∈ K) (hZ : -1 ∈ K)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) : γ ∈ K := by
  apply transversal_mem (reduction 2) rep2 K
  · intro A
    rw [edge2S_checked]
    exact word_mem 2 K hT hU hZ _
  · intro A
    rw [edge2T_checked]
    exact word_mem 2 K hT hU hZ _
  · exact rep2_one
  · apply rep2_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge2S_checked
#print axioms edge2T_checked
#print axioms gamma0_2_mem

def rep3 (A : SL(2,ZMod 3)) : SL(2,ℤ) :=
  match (A.1 1 0).val*3+(A.1 1 1).val with
  | 3 | 6 => S
  | 4 | 8 => S*T
  | 5 | 7 => S*T*S
  | _ => 1

def edge3S (A : SL(2,ZMod 3)) : List (Fin 5) :=
  match (A.1 1 0).val*3+(A.1 1 1).val with
  | 3 | 6 => [4]
  | 5 | 7 => [4]
  | _ => []

theorem edge3S_checked : ∀ A : SL(2,ZMod 3),
    rep3 A*S*(rep3 (A*reduction 3 S))⁻¹ = word 3 (edge3S A) := by decide

def edge3T (A : SL(2,ZMod 3)) : List (Fin 5) :=
  match (A.1 1 0).val*3+(A.1 1 1).val with
  | 1 | 2 => [0]
  | 4 | 8 => [3, 0]
  | 5 | 7 => [1]
  | _ => []

theorem edge3T_checked : ∀ A : SL(2,ZMod 3),
    rep3 A*T*(rep3 (A*reduction 3 T))⁻¹ = word 3 (edge3T A) := by decide

theorem rep3_one : rep3 1=1 := by decide

theorem rep3_upper : ∀ A : SL(2,ZMod 3), A.1 1 0=0 → rep3 A=1 := by decide

theorem gamma0_3_mem (K : Subgroup SL(2,ℤ))
    (hT : T ∈ K) (hU : lower 3 ∈ K) (hZ : -1 ∈ K)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 3) : γ ∈ K := by
  apply transversal_mem (reduction 3) rep3 K
  · intro A
    rw [edge3S_checked]
    exact word_mem 3 K hT hU hZ _
  · intro A
    rw [edge3T_checked]
    exact word_mem 3 K hT hU hZ _
  · exact rep3_one
  · apply rep3_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge3S_checked
#print axioms edge3T_checked
#print axioms gamma0_3_mem

def rep4 (A : SL(2,ZMod 4)) : SL(2,ℤ) :=
  match (A.1 1 0).val*4+(A.1 1 1).val with
  | 4 | 12 => S
  | 5 | 15 => S*T
  | 7 | 13 => S*T*S
  | 6 | 14 => S*T^2
  | 9 | 11 => S*T^2*S
  | _ => 1

def edge4S (A : SL(2,ZMod 4)) : List (Fin 5) :=
  match (A.1 1 0).val*4+(A.1 1 1).val with
  | 4 | 12 => [4]
  | 7 | 13 => [4]
  | 9 | 11 => [4]
  | _ => []

theorem edge4S_checked : ∀ A : SL(2,ZMod 4),
    rep4 A*S*(rep4 (A*reduction 4 S))⁻¹ = word 4 (edge4S A) := by decide

def edge4T (A : SL(2,ZMod 4)) : List (Fin 5) :=
  match (A.1 1 0).val*4+(A.1 1 1).val with
  | 1 | 3 => [0]
  | 7 | 13 => [1]
  | 6 | 14 => [3, 0]
  | 9 | 11 => [1, 2, 4]
  | _ => []

theorem edge4T_checked : ∀ A : SL(2,ZMod 4),
    rep4 A*T*(rep4 (A*reduction 4 T))⁻¹ = word 4 (edge4T A) := by decide

theorem rep4_one : rep4 1=1 := by decide

theorem rep4_upper : ∀ A : SL(2,ZMod 4), A.1 1 0=0 → rep4 A=1 := by decide

theorem gamma0_4_mem (K : Subgroup SL(2,ℤ))
    (hT : T ∈ K) (hU : lower 4 ∈ K) (hZ : -1 ∈ K)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : γ ∈ K := by
  apply transversal_mem (reduction 4) rep4 K
  · intro A
    rw [edge4S_checked]
    exact word_mem 4 K hT hU hZ _
  · intro A
    rw [edge4T_checked]
    exact word_mem 4 K hT hU hZ _
  · exact rep4_one
  · apply rep4_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edge4S_checked
#print axioms edge4T_checked
#print axioms gamma0_4_mem

end SmallLevelGenerators
