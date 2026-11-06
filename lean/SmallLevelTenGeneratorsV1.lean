module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import SmallLevelTenMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelTen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 13 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => (kernel 0)⁻¹
  | 7 => (kernel 1)⁻¹
  | 8 => (kernel 2)⁻¹
  | 9 => (kernel 3)⁻¹
  | 10 => (kernel 4)⁻¹
  | 11 => (kernel 5)⁻¹
  | 12 => -1

def word (w : List (Fin 13)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 6, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 13)) : word w∈K := by
  have hl (i : Fin 13) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact hK 5
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact K.inv_mem (hK 5)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 10) : SL(2,ℤ) :=
  match c.val*10+d.val with
  | 10 | 30 | 70 | 90 => ⟨!![0,-1;1,0],by decide⟩
  | 11 | 33 | 77 | 99 => ⟨!![0,-1;1,1],by decide⟩
  | 19 | 37 | 73 | 91 => ⟨!![-1,0;1,-1],by decide⟩
  | 12 | 36 | 74 | 98 => ⟨!![0,-1;1,2],by decide⟩
  | 29 | 43 | 67 | 81 => ⟨!![-1,0;2,-1],by decide⟩
  | 13 | 39 | 71 | 97 => ⟨!![0,-1;1,3],by decide⟩
  | 21 | 47 | 63 | 89 => ⟨!![-1,-1;2,1],by decide⟩
  | 14 | 32 | 78 | 96 => ⟨!![0,-1;1,4],by decide⟩
  | 18 | 34 | 76 | 92 => ⟨!![-1,1;1,-2],by decide⟩
  | 23 | 41 | 69 | 87 => ⟨!![-1,-2;2,3],by decide⟩
  | 27 | 49 | 61 | 83 => ⟨!![-1,0;4,-1],by decide⟩
  | 15 | 35 | 75 | 95 => ⟨!![0,-1;1,5],by decide⟩
  | 16 | 38 | 72 | 94 => ⟨!![-2,1;3,-2],by decide⟩
  | 25 | 45 | 65 | 85 => ⟨!![-1,-3;2,5],by decide⟩
  | 51 | 53 | 57 | 59 => ⟨!![-1,0;5,-1],by decide⟩
  | 17 | 31 | 79 | 93 => ⟨!![-2,-1;3,1],by decide⟩
  | 52 | 54 | 56 | 58 => ⟨!![-3,1;5,-2],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 10) : List (Fin 13) :=
  match c.val*10+d.val with
  | 10 | 30 | 70 | 90 => [12]
  | 19 | 37 | 73 | 91 => [12]
  | 29 | 43 | 67 | 81 => [12]
  | 13 | 39 | 71 | 97 => [12, 4, 1, 0]
  | 18 | 34 | 76 | 92 => [12]
  | 27 | 49 | 61 | 83 => [12]
  | 16 | 38 | 72 | 94 => [12]
  | 51 | 53 | 57 | 59 => [12]
  | 17 | 31 | 79 | 93 => [12, 6, 5, 2, 3, 0]
  | 52 | 54 | 56 | 58 => [12]
  | _ => []

def edgeTRow (c d : ZMod 10) : List (Fin 13) :=
  match c.val*10+d.val with
  | 1 | 3 | 7 | 9 => [0]
  | 19 | 37 | 73 | 91 => [6]
  | 27 | 49 | 61 | 83 => [4, 1, 0]
  | 15 | 35 | 75 | 95 => [4, 11, 0]
  | 25 | 45 | 65 | 85 => [12, 6, 5, 7, 2]
  | 51 | 53 | 57 | 59 => [4, 1, 11, 0]
  | 17 | 31 | 79 | 93 => [6, 5, 2, 3, 0]
  | 52 | 54 | 56 | 58 => [12, 6, 5, 2]
  | _ => []

def rep (g : SL(2,ZMod 10)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 10)) :
    ∃ a b : ZMod 10, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

theorem edgeSRow_checked : ∀ c d : ZMod 10, (∃ a b : ZMod 10, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 10,
    Nat.gcd (Nat.gcd c.val d.val) 10 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 10, (∃ a b : ZMod 10, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 10,
    Nat.gcd (Nat.gcd c.val d.val) 10 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 10)) :
    rep g*S*(rep (g*reduction 10 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 10 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 10 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 10)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 10)) :
    rep g*T*(rep (g*reduction 10 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 10 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 10 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 10)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 10)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 10, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 6, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 10) : γ∈K := by
  apply transversal_mem (reduction 10) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeSRow_checked
#print axioms edgeTRow_checked
#print axioms gamma0_mem

end SmallLevelTen
