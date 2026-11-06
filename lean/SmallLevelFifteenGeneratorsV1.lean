module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import SmallLevelFifteenMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelFifteen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def generator : Fin 7 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => kernel 6

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

def repRow (c d : ZMod 15) : SL(2,ℤ) :=
  match c.val*15+d.val with
  | 15 | 30 | 60 | 105 | 120 | 165 | 195 | 210 => ⟨!![0,-1;1,0],by decide⟩
  | 16 | 32 | 64 | 112 | 128 | 176 | 208 | 224 => ⟨!![0,-1;1,1],by decide⟩
  | 29 | 43 | 71 | 113 | 127 | 169 | 197 | 211 => ⟨!![-1,0;1,-1],by decide⟩
  | 17 | 34 | 68 | 119 | 121 | 172 | 206 | 223 => ⟨!![0,-1;1,2],by decide⟩
  | 22 | 44 | 73 | 109 | 131 | 167 | 196 | 218 => ⟨!![-1,0;2,-1],by decide⟩
  | 18 | 36 | 72 | 111 | 129 | 168 | 204 | 222 => ⟨!![0,-1;1,3],by decide⟩
  | 23 | 31 | 62 | 116 | 124 | 178 | 209 | 217 => ⟨!![-1,-1;2,1],by decide⟩
  | 49 | 59 | 98 | 103 | 137 | 142 | 181 | 191 => ⟨!![-1,0;3,-1],by decide⟩
  | 19 | 38 | 61 | 118 | 122 | 179 | 202 | 221 => ⟨!![0,-1;1,4],by decide⟩
  | 28 | 41 | 67 | 106 | 134 | 173 | 199 | 212 => ⟨!![-1,1;1,-2],by decide⟩
  | 24 | 33 | 66 | 108 | 132 | 174 | 207 | 216 => ⟨!![-1,-2;2,3],by decide⟩
  | 47 | 52 | 94 | 104 | 136 | 146 | 188 | 193 => ⟨!![-1,-1;3,2],by decide⟩
  | 26 | 37 | 74 | 107 | 133 | 166 | 203 | 214 => ⟨!![-1,0;4,-1],by decide⟩
  | 20 | 40 | 65 | 110 | 130 | 175 | 200 | 220 => ⟨!![0,-1;1,5],by decide⟩
  | 53 | 58 | 91 | 101 | 139 | 149 | 182 | 187 => ⟨!![-2,1;3,-2],by decide⟩
  | 25 | 35 | 70 | 115 | 125 | 170 | 205 | 215 => ⟨!![-1,-3;2,5],by decide⟩
  | 21 | 42 | 69 | 117 | 123 | 171 | 198 | 219 => ⟨!![-1,1;2,-3],by decide⟩
  | 50 | 55 | 95 | 100 | 140 | 145 | 185 | 190 => ⟨!![-1,-2;3,5],by decide⟩
  | 27 | 39 | 63 | 114 | 126 | 177 | 201 | 213 => ⟨!![-1,-1;4,3],by decide⟩
  | 77 | 83 | 86 | 89 | 151 | 154 | 157 | 163 => ⟨!![-1,0;5,-1],by decide⟩
  | 46 | 56 | 92 | 97 | 143 | 148 | 184 | 194 => ⟨!![-2,-1;3,1],by decide⟩
  | 76 | 79 | 82 | 88 | 152 | 158 | 161 | 164 => ⟨!![-3,1;5,-2],by decide⟩
  | 78 | 81 | 84 | 87 | 153 | 156 | 159 | 162 => ⟨!![-2,1;5,-3],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 15) : List (Fin 15) :=
  match c.val*15+d.val with
  | 15 | 30 | 60 | 105 | 120 | 165 | 195 | 210 => [14]
  | 29 | 43 | 71 | 113 | 127 | 169 | 197 | 211 => [14]
  | 22 | 44 | 73 | 109 | 131 | 167 | 196 | 218 => [14]
  | 49 | 59 | 98 | 103 | 137 | 142 | 181 | 191 => [14]
  | 28 | 41 | 67 | 106 | 134 | 173 | 199 | 212 => [14]
  | 26 | 37 | 74 | 107 | 133 | 166 | 203 | 214 => [14]
  | 53 | 58 | 91 | 101 | 139 | 149 | 182 | 187 => [14]
  | 21 | 42 | 69 | 117 | 123 | 171 | 198 | 219 => [14]
  | 27 | 39 | 63 | 114 | 126 | 177 | 201 | 213 => [4, 12, 10, 13, 0]
  | 77 | 83 | 86 | 89 | 151 | 154 | 157 | 163 => [14]
  | 46 | 56 | 92 | 97 | 143 | 148 | 184 | 194 => [14, 7, 6, 3, 5, 2]
  | 76 | 79 | 82 | 88 | 152 | 158 | 161 | 164 => [14]
  | 78 | 81 | 84 | 87 | 153 | 156 | 159 | 162 => [14]
  | _ => []

def edgeTRow (c d : ZMod 15) : List (Fin 15) :=
  match c.val*15+d.val with
  | 1 | 2 | 4 | 7 | 8 | 11 | 13 | 14 => [0]
  | 29 | 43 | 71 | 113 | 127 | 169 | 197 | 211 => [7]
  | 20 | 40 | 65 | 110 | 130 | 175 | 200 | 220 => [13, 0]
  | 25 | 35 | 70 | 115 | 125 | 170 | 205 | 215 => [14, 7, 6, 3, 6, 3, 5, 2]
  | 50 | 55 | 95 | 100 | 140 | 145 | 185 | 190 => [14, 4, 10, 13, 0]
  | 27 | 39 | 63 | 114 | 126 | 177 | 201 | 213 => [14, 4, 12, 10, 13, 0]
  | 77 | 83 | 86 | 89 | 151 | 154 | 157 | 163 => [4, 12, 10, 13, 10, 13, 0]
  | 46 | 56 | 92 | 97 | 143 | 148 | 184 | 194 => [7, 6, 3, 5, 2]
  | 76 | 79 | 82 | 88 | 152 | 158 | 161 | 164 => [7, 6, 3, 2]
  | 78 | 81 | 84 | 87 | 153 | 156 | 159 | 162 => [14, 7, 6]
  | _ => []

def rep (g : SL(2,ZMod 15)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 15)) :
    ∃ a b : ZMod 15, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

theorem edgeSRow_checked : ∀ c d : ZMod 15, (∃ a b : ZMod 15, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 15,
    Nat.gcd (Nat.gcd c.val d.val) 15 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 15, (∃ a b : ZMod 15, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 15,
    Nat.gcd (Nat.gcd c.val d.val) 15 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 15)) :
    rep g*S*(rep (g*reduction 15 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 15 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 15 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 15)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 15)) :
    rep g*T*(rep (g*reduction 15 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 15 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 15 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 15)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 15)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 15, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 7, generator i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 15) : γ∈K := by
  apply transversal_mem (reduction 15) rep K
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

end SmallLevelFifteen
