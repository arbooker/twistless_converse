module

public import QuantitativeArithmeticPrimitiveResiduePairV4
public import QuantitativeArithmeticSmallLevelEighteenMatricesV1
public import SmallLevelModularCriterionV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelEighteen. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelEighteenGeneratorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelEighteen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 21 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => kernel 6
  | 7 => kernel 7
  | 8 => kernel 8
  | 9 => kernel 9
  | 10 => (kernel 0)⁻¹
  | 11 => (kernel 1)⁻¹
  | 12 => (kernel 2)⁻¹
  | 13 => (kernel 3)⁻¹
  | 14 => (kernel 4)⁻¹
  | 15 => (kernel 5)⁻¹
  | 16 => (kernel 6)⁻¹
  | 17 => (kernel 7)⁻¹
  | 18 => (kernel 8)⁻¹
  | 19 => (kernel 9)⁻¹
  | _ => -1

def word (w : List (Fin 21)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 10, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 21)) : word w∈K := by
  have hl (i : Fin 21) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact hK 5
    · exact hK 6
    · exact hK 7
    · exact hK 8
    · exact hK 9
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact K.inv_mem (hK 5)
    · exact K.inv_mem (hK 6)
    · exact K.inv_mem (hK 7)
    · exact K.inv_mem (hK 8)
    · exact K.inv_mem (hK 9)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 18) : SL(2,ℤ) :=
  match c.val*18+d.val with
  | 18 | 90 | 126 | 198 | 234 | 306 => ⟨!![0,-1;1,0],by decide⟩
  | 19 | 95 | 133 | 209 | 247 | 323 => ⟨!![0,-1;1,1],by decide⟩
  | 35 | 103 | 137 | 205 | 239 | 307 => ⟨!![0,-1;1,-1],by decide⟩
  | 20 | 100 | 140 | 202 | 242 | 322 => ⟨!![0,-1;1,2],by decide⟩
  | 34 | 98 | 130 | 212 | 244 | 308 => ⟨!![0,-1;1,-2],by decide⟩
  | 53 | 79 | 149 | 193 | 263 | 289 => ⟨!![-1,0;2,-1],by decide⟩
  | 21 | 105 | 129 | 213 | 237 | 321 => ⟨!![0,-1;1,3],by decide⟩
  | 37 | 83 | 157 | 185 | 259 | 305 => ⟨!![-1,0;-2,-1],by decide⟩
  | 33 | 93 | 141 | 201 | 249 | 309 => ⟨!![0,-1;1,-3],by decide⟩
  | 51 | 75 | 159 | 183 | 267 | 291 => ⟨!![-1,1;2,-3],by decide⟩
  | 59 | 65 | 71 | 271 | 277 | 283 => ⟨!![-1,0;3,-1],by decide⟩
  | 22 | 92 | 136 | 206 | 250 | 320 => ⟨!![0,-1;1,4],by decide⟩
  | 39 | 87 | 147 | 195 | 255 | 303 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 55 | 61 | 67 | 275 | 281 | 287 => ⟨!![-1,0;-3,-1],by decide⟩
  | 32 | 106 | 134 | 208 | 236 | 310 => ⟨!![0,-1;1,-4],by decide⟩
  | 56 | 62 | 68 | 274 | 280 | 286 => ⟨!![1,1;-3,-2],by decide⟩
  | 49 | 89 | 151 | 191 | 253 | 293 => ⟨!![-1,2;2,-5],by decide⟩
  | 23 | 97 | 143 | 199 | 245 | 319 => ⟨!![0,-1;1,5],by decide⟩
  | 58 | 64 | 70 | 272 | 278 | 284 => ⟨!![-1,1;-3,2],by decide⟩
  | 41 | 73 | 155 | 187 | 269 | 301 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 31 | 101 | 127 | 215 | 241 | 311 => ⟨!![0,-1;1,-5],by decide⟩
  | 47 | 85 | 161 | 181 | 257 | 295 => ⟨!![-1,3;2,-7],by decide⟩
  | 25 | 107 | 139 | 203 | 235 | 317 => ⟨!![-1,0;5,-1],by decide⟩
  | 24 | 102 | 132 | 210 | 240 | 318 => ⟨!![0,-1;1,6],by decide⟩
  | 43 | 77 | 145 | 197 | 265 | 299 => ⟨!![-1,-3;-2,-7],by decide⟩
  | 29 | 91 | 131 | 211 | 251 | 313 => ⟨!![-1,0;-5,-1],by decide⟩
  | 30 | 96 | 138 | 204 | 246 | 312 => ⟨!![0,-1;1,-6],by decide⟩
  | 26 | 94 | 128 | 214 | 248 | 316 => ⟨!![3,1;-7,-2],by decide⟩
  | 45 | 81 | 153 | 189 | 261 | 297 => ⟨!![-1,4;2,-9],by decide⟩
  | 113 | 119 | 125 | 217 | 223 | 229 => ⟨!![-1,0;6,-1],by decide⟩
  | 28 | 104 | 142 | 200 | 238 | 314 => ⟨!![-3,1;-7,2],by decide⟩
  | 109 | 115 | 121 | 221 | 227 | 233 => ⟨!![-1,0;-6,-1],by decide⟩
  | 27 | 99 | 135 | 207 | 243 | 315 => ⟨!![3,4;-7,-9],by decide⟩
  | 164 | 166 | 170 | 172 | 176 | 178 => ⟨!![4,1;-9,-2],by decide⟩
  | 163 | 167 | 169 | 173 | 175 | 179 => ⟨!![4,-3;-9,7],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 18) : List (Fin 21) :=
  match c.val*18+d.val with
  | 18 | 90 | 126 | 198 | 234 | 306 => [20]
  | 19 | 95 | 133 | 209 | 247 | 323 => [10]
  | 35 | 103 | 137 | 205 | 239 | 307 => [0, 20]
  | 53 | 79 | 149 | 193 | 263 | 289 => [20]
  | 37 | 83 | 157 | 185 | 259 | 305 => [20]
  | 59 | 65 | 71 | 271 | 277 | 283 => [20]
  | 22 | 92 | 136 | 206 | 250 | 320 => [6, 0]
  | 55 | 61 | 67 | 275 | 281 | 287 => [20]
  | 32 | 106 | 134 | 208 | 236 | 310 => [2, 8, 20, 5]
  | 56 | 62 | 68 | 274 | 280 | 286 => [20]
  | 49 | 89 | 151 | 191 | 253 | 293 => [10, 16, 20]
  | 58 | 64 | 70 | 272 | 278 | 284 => [20]
  | 41 | 73 | 155 | 187 | 269 | 301 => [3, 7, 12]
  | 25 | 107 | 139 | 203 | 235 | 317 => [20]
  | 29 | 91 | 131 | 211 | 251 | 313 => [20]
  | 26 | 94 | 128 | 214 | 248 | 316 => [20]
  | 113 | 119 | 125 | 217 | 223 | 229 => [20]
  | 28 | 104 | 142 | 200 | 238 | 314 => [20]
  | 109 | 115 | 121 | 221 | 227 | 233 => [20]
  | 164 | 166 | 170 | 172 | 176 | 178 => [20]
  | 163 | 167 | 169 | 173 | 175 | 179 => [20]
  | _ => []

def edgeTRow (c d : ZMod 18) : List (Fin 21) :=
  match c.val*18+d.val with
  | 1 | 5 | 7 | 11 | 13 | 17 => [0]
  | 53 | 79 | 149 | 193 | 263 | 289 => [10, 20]
  | 59 | 65 | 71 | 271 | 277 | 283 => [20]
  | 55 | 61 | 67 | 275 | 281 | 287 => [2, 8, 5]
  | 56 | 62 | 68 | 274 | 280 | 286 => [10, 16]
  | 25 | 107 | 139 | 203 | 235 | 317 => [6, 0, 20]
  | 24 | 102 | 132 | 210 | 240 | 318 => [8, 4, 20, 16]
  | 43 | 77 | 145 | 197 | 265 | 299 => [15, 0, 20]
  | 29 | 91 | 131 | 211 | 251 | 313 => [2, 11, 20]
  | 113 | 119 | 125 | 217 | 223 | 229 => [6, 3, 9]
  | 28 | 104 | 142 | 200 | 238 | 314 => [3, 7, 20, 12]
  | 109 | 115 | 121 | 221 | 227 | 233 => [1, 12, 20]
  | 27 | 99 | 135 | 207 | 243 | 315 => [10, 14, 5]
  | 164 | 166 | 170 | 172 | 176 | 178 => [10, 4, 0]
  | _ => []

def rep (g : SL(2,ZMod 18)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 18)) :
    ∃ a b : ZMod 18, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe



















theorem edgeSRow_checked : ∀ c d : ZMod 18, (∃ a b : ZMod 18, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 18,
    Nat.gcd (Nat.gcd c.val d.val) 18 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)



















theorem edgeTRow_checked : ∀ c d : ZMod 18, (∃ a b : ZMod 18, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 18,
    Nat.gcd (Nat.gcd c.val d.val) 18 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 18)) :
    rep g*S*(rep (g*reduction 18 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 18 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 18 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 18)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 18)) :
    rep g*T*(rep (g*reduction 18 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 18 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 18 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 18)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 18)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 18, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 10, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 18) : γ∈K := by
  apply transversal_mem (reduction 18) rep K
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

end QuantitativeArithmeticSmallLevelEighteen
end
end

/-! ## QuantitativeArithmeticSmallLevelEighteenModularV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEighteen
open Matrix SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

/-- Every Gamma0(18) transformation follows from the literal Euler input. -/
theorem gamma_zero_eighteen (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 18 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 18) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  change γ∈K
  exact gamma0_mem K (original_kernel m hf)
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Complete original-input level-18 modularity for every even weight.
Holomorphy and boundedness at all cusps come from the original input via
`modular_of_transformations`; they are not extra assumptions. -/
theorem level_eighteen {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 18 k f) : IsModular 18 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_eighteen m hf)

#print axioms gamma_zero_eighteen
#print axioms level_eighteen
end QuantitativeArithmeticSmallLevelEighteen
end
end
