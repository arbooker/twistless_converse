module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import SmallLevelFourteenRigidityV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelFourteen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def generator : Fin 7 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => A

def letter : Fin 15 → SL(2,ℤ)
  | 0 => generator 0
  | 1 => generator 1
  | 2 => generator 2
  | 3 => generator 3
  | 4 => generator 4
  | 5 => generator 5
  | 6 => generator 6
  | 7 => (generator 0)⁻¹
  | 8 => (generator 1)⁻¹
  | 9 => (generator 2)⁻¹
  | 10 => (generator 3)⁻¹
  | 11 => (generator 4)⁻¹
  | 12 => (generator 5)⁻¹
  | 13 => (generator 6)⁻¹
  | 14 => -1

def word (w : List (Fin 15)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 7, generator i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 15)) : word w∈K := by
  have hl (i : Fin 15) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact hK 5
    · exact hK 6
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact K.inv_mem (hK 5)
    · exact K.inv_mem (hK 6)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 14) : SL(2,ℤ) :=
  match c.val*14+d.val with
  | 14 | 42 | 70 | 126 | 154 | 182 => ⟨!![0,-1;1,0],by decide⟩
  | 15 | 45 | 75 | 135 | 165 | 195 => ⟨!![0,-1;1,1],by decide⟩
  | 27 | 53 | 79 | 131 | 157 | 183 => ⟨!![-1,0;1,-1],by decide⟩
  | 16 | 48 | 80 | 130 | 162 | 194 => ⟨!![0,-1;1,2],by decide⟩
  | 41 | 61 | 95 | 115 | 149 | 169 => ⟨!![-1,0;2,-1],by decide⟩
  | 17 | 51 | 71 | 139 | 159 | 193 => ⟨!![0,-1;1,3],by decide⟩
  | 29 | 65 | 87 | 123 | 145 | 181 => ⟨!![-1,-1;2,1],by decide⟩
  | 23 | 55 | 73 | 137 | 155 | 187 => ⟨!![-1,0;3,-1],by decide⟩
  | 18 | 54 | 76 | 134 | 156 | 192 => ⟨!![0,-1;1,4],by decide⟩
  | 26 | 50 | 74 | 136 | 160 | 184 => ⟨!![-1,1;1,-2],by decide⟩
  | 31 | 69 | 93 | 117 | 141 | 179 => ⟨!![-1,-2;2,3],by decide⟩
  | 24 | 44 | 78 | 132 | 166 | 186 => ⟨!![-1,-1;3,2],by decide⟩
  | 19 | 43 | 81 | 129 | 167 | 191 => ⟨!![0,-1;1,5],by decide⟩
  | 33 | 59 | 85 | 125 | 151 | 177 => ⟨!![-1,-3;2,5],by decide⟩
  | 39 | 57 | 89 | 121 | 153 | 171 => ⟨!![-1,1;2,-3],by decide⟩
  | 25 | 47 | 83 | 127 | 163 | 185 => ⟨!![-1,-2;3,5],by decide⟩
  | 20 | 46 | 72 | 138 | 164 | 190 => ⟨!![0,-1;1,6],by decide⟩
  | 22 | 52 | 82 | 128 | 158 | 188 => ⟨!![-3,1;5,-2],by decide⟩
  | 35 | 63 | 91 | 119 | 147 | 175 => ⟨!![-1,-4;2,7],by decide⟩
  | 37 | 67 | 97 | 113 | 143 | 173 => ⟨!![-1,0;6,-1],by decide⟩
  | 21 | 49 | 77 | 133 | 161 | 189 => ⟨!![0,-1;1,7],by decide⟩
  | 100 | 102 | 104 | 106 | 108 | 110 => ⟨!![-4,1;7,-2],by decide⟩
  | 99 | 101 | 103 | 107 | 109 | 111 => ⟨!![-1,0;7,-1],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 14) : List (Fin 15) :=
  match c.val*14+d.val with
  | 14 | 42 | 70 | 126 | 154 | 182 => [14]
  | 27 | 53 | 79 | 131 | 157 | 183 => [14]
  | 41 | 61 | 95 | 115 | 149 | 169 => [14]
  | 23 | 55 | 73 | 137 | 155 | 187 => [14]
  | 18 | 54 | 76 | 134 | 156 | 192 => [4, 1, 0, 13, 0]
  | 26 | 50 | 74 | 136 | 160 | 184 => [14]
  | 31 | 69 | 93 | 117 | 141 | 179 => [14, 7, 5, 2, 3, 6]
  | 19 | 43 | 81 | 129 | 167 | 191 => [14, 4, 1, 0]
  | 39 | 57 | 89 | 121 | 153 | 171 => [14]
  | 25 | 47 | 83 | 127 | 163 | 185 => [7, 8, 2]
  | 22 | 52 | 82 | 128 | 158 | 188 => [14]
  | 37 | 67 | 97 | 113 | 143 | 173 => [14]
  | 100 | 102 | 104 | 106 | 108 | 110 => [14]
  | 99 | 101 | 103 | 107 | 109 | 111 => [14]
  | _ => []

def edgeTRow (c d : ZMod 14) : List (Fin 15) :=
  match c.val*14+d.val with
  | 1 | 3 | 5 | 9 | 11 | 13 => [0]
  | 27 | 53 | 79 | 131 | 157 | 183 => [7]
  | 25 | 47 | 83 | 127 | 163 | 185 => [13, 0]
  | 22 | 52 | 82 | 128 | 158 | 188 => [7, 5, 2, 3, 6]
  | 35 | 63 | 91 | 119 | 147 | 175 => [14, 7, 5, 8, 2]
  | 37 | 67 | 97 | 113 | 143 | 173 => [4, 1, 0]
  | 21 | 49 | 77 | 133 | 161 | 189 => [4, 12, 0]
  | 100 | 102 | 104 | 106 | 108 | 110 => [14, 7, 5, 2]
  | 99 | 101 | 103 | 107 | 109 | 111 => [4, 1, 12, 0]
  | _ => []

def rep (g : SL(2,ZMod 14)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 14)) :
    ∃ a b : ZMod 14, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

theorem edgeSRow_checked : ∀ c d : ZMod 14, (∃ a b : ZMod 14, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 14,
    Nat.gcd (Nat.gcd c.val d.val) 14 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 14, (∃ a b : ZMod 14, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 14,
    Nat.gcd (Nat.gcd c.val d.val) 14 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 14)) :
    rep g*S*(rep (g*reduction 14 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 14 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 14 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 14)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 14)) :
    rep g*T*(rep (g*reduction 14 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 14 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 14 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 14)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 14)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 14, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 7, generator i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 14) : γ∈K := by
  apply transversal_mem (reduction 14) rep K
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

end SmallLevelFourteen
