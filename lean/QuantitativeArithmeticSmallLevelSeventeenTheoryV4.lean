module

public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelElevenDefectV1
public import SmallLevelModularCriterionV1
public import SmallLevelOddWordsV1
public import SmallLevelSixPairV1
public import SmallLevelThreeSlashV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelSeventeen. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelSeventeenPairsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelSeventeen

open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelThree
open scoped MatrixGroups ModularForm

def A : SL(2,ℤ) := ⟨!![3,-1;-17,6], by decide⟩
def B : SL(2,ℤ) := ⟨!![6,-1;-17,3], by decide⟩

theorem A_inv : A⁻¹ = (⟨!![6,1;17,3], by decide⟩ : SL(2,ℤ)) := by decide
theorem B_inv : B⁻¹ = (⟨!![3,1;17,6], by decide⟩ : SL(2,ℤ)) := by decide

theorem three_positive : lowerBranch 17 1 =
    SpecialLinearGroup.mapGL ℝ B⁻¹ * upperBranch (-1) := by
  rw [B_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem three_negative : lowerBranch 17 (-1) =
    SpecialLinearGroup.mapGL ℝ A * upperBranch 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, A, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem three_ratio : upperBranch (-1) * (upperBranch 1)⁻¹ = translation (-2/3) := by
  apply (mul_right_cancel_iff (a := upperBranch 1)).mp
  rw [inv_mul_cancel_right]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperBranch, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem original_three_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B⁻¹) ∣[(k:ℤ)] translation (-2/3)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-2/3)) := by
  have h := original_pair_slash (by decide : 0 < 17) (by decide) hf
  rw [three_positive, three_negative, SlashAction.slash_mul, SlashAction.slash_mul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] (upperBranch 1)⁻¹) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one, mul_assoc, three_ratio] at hh
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B⁻¹) ∣[(k:ℤ)] translation (-2/3)) = _
  simpa only [SlashAction.slash_mul, SlashAction.slash_one, add_comm] using hh.symm

theorem sqrt_conductor : Real.sqrt 612 = 6 * Real.sqrt 17 := by
  rw [show (612:ℝ)=36*17 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

theorem six_positive : fricke 17 (by decide) * SpecialLinearGroup.mapGL ℝ B *
    translation (1/6) = translation (1/6) * fricke 612 (by decide) := by
  have ht : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 17≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, B, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem six_negative : fricke 17 (by decide) * SpecialLinearGroup.mapGL ℝ A⁻¹ *
    translation (-(1/6)) = translation (-(1/6)) * fricke 612 (by decide) := by
  rw [A_inv]
  have ht : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 17≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem root_six (f : ℕ → ℂ) : FinitenessNormalizedTwistProduct.root 17 f 6 = 1 := by
  have hp : Nat.primeFactors 6 = {2,3} := by
    rw [show (6:ℕ)=2*3 by norm_num, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  simp [FinitenessNormalizedTwistProduct.root, hp, FinitenessNormalizedTwistLocal.sign]

theorem original_six_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A⁻¹) ∣[(k:ℤ)] translation (-1/3)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/3)) := by
  have h := original_six_pair (by decide : 0<17) (by decide : 0<612) (by decide) hf
  have hp : (fricke 17 (by decide))⁻¹ * translation (1/6) * fricke 612 (by decide) =
      SpecialLinearGroup.mapGL ℝ B * translation (1/6) := by
    rw [mul_assoc, ← six_positive]
    group
  have hn : (fricke 17 (by decide))⁻¹ * translation (-(1/6)) * fricke 612 (by decide) =
      SpecialLinearGroup.mapGL ℝ A⁻¹ * translation (-(1/6)) := by
    rw [mul_assoc, ← six_negative]
    group
  rw [hp, hn, root_six, one_smul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] translation (-(1/6))) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_assoc, translation_mul] at hh
  norm_num only [show (1/6:ℝ)+ -(1/6)=0 by ring,
    show (-(1/6):ℝ)+ -(1/6)= -1/3 by ring] at hh
  have ht : translation 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation, matrix, GeneralLinearGroup.mkOfDetNeZero]
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A⁻¹) ∣[(k:ℤ)] translation (-1/3)) = _
  simpa only [ht, mul_one, SlashAction.slash_one, SlashAction.slash_mul, neg_div] using hh

#print axioms original_three_reduced
#print axioms original_six_reduced

end QuantitativeArithmeticSmallLevelSeventeen
end
end

/-! ## QuantitativeArithmeticSmallLevelSeventeenGeneratorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelSeventeen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 11 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower 17
  | 3 => (lower 17)⁻¹
  | 4 => -1
  | 5 => oddMatrix 17 9 (by decide)
  | 6 => (oddMatrix 17 9 (by decide))⁻¹
  | 7 => A
  | 8 => A⁻¹
  | 9 => B
  | 10 => B⁻¹

def word (w : List (Fin 11)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 17∈K) (hZ : -1∈K)
    (h2 : oddMatrix 17 9 (by decide)∈K) (h3 : A∈K) (h6 : B∈K)
    (w : List (Fin 11)) : word w∈K := by
  have hl (i : Fin 11) : letter i∈K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
    · exact h2
    · exact K.inv_mem h2
    · exact h3
    · exact K.inv_mem h3
    · exact h6
    · exact K.inv_mem h6
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 17) : SL(2,ℤ) :=
  match c.val*17+d.val with
  | 17 | 34 | 51 | 68 | 85 | 102 | 119 | 136 | 153 | 170 | 187 | 204 | 221 | 238 | 255 | 272 => ⟨!![0,-1;1,0], by decide⟩
  | 18 | 36 | 54 | 72 | 90 | 108 | 126 | 144 | 162 | 180 | 198 | 216 | 234 | 252 | 270 | 288 => ⟨!![0,-1;1,1], by decide⟩
  | 19 | 38 | 57 | 76 | 95 | 114 | 133 | 152 | 154 | 173 | 192 | 211 | 230 | 249 | 268 | 287 => ⟨!![0,-1;1,2], by decide⟩
  | 20 | 40 | 60 | 80 | 100 | 103 | 123 | 143 | 163 | 183 | 203 | 206 | 226 | 246 | 266 | 286 => ⟨!![0,-1;1,3], by decide⟩
  | 21 | 42 | 63 | 84 | 88 | 109 | 130 | 151 | 155 | 176 | 197 | 218 | 222 | 243 | 264 | 285 => ⟨!![0,-1;1,4], by decide⟩
  | 22 | 44 | 66 | 71 | 93 | 115 | 120 | 142 | 164 | 186 | 191 | 213 | 235 | 240 | 262 | 284 => ⟨!![0,-1;1,5], by decide⟩
  | 23 | 46 | 52 | 75 | 98 | 104 | 127 | 150 | 156 | 179 | 202 | 208 | 231 | 254 | 260 | 283 => ⟨!![-1,0;-3,-1], by decide⟩
  | 24 | 48 | 55 | 79 | 86 | 110 | 134 | 141 | 165 | 172 | 196 | 220 | 227 | 251 | 258 | 282 => ⟨!![-1,1;2,-3], by decide⟩
  | 25 | 50 | 58 | 83 | 91 | 116 | 124 | 149 | 157 | 182 | 190 | 215 | 223 | 248 | 256 | 281 => ⟨!![-1,0;2,-1], by decide⟩
  | 26 | 35 | 61 | 70 | 96 | 105 | 131 | 140 | 166 | 175 | 201 | 210 | 236 | 245 | 271 | 280 => ⟨!![-1,0;-2,-1], by decide⟩
  | 27 | 37 | 64 | 74 | 101 | 111 | 121 | 148 | 158 | 185 | 195 | 205 | 232 | 242 | 269 | 279 => ⟨!![-1,-1;-2,-3], by decide⟩
  | 28 | 39 | 67 | 78 | 89 | 117 | 128 | 139 | 167 | 178 | 189 | 217 | 228 | 239 | 267 | 278 => ⟨!![-1,0;3,-1], by decide⟩
  | 29 | 41 | 53 | 82 | 94 | 106 | 135 | 147 | 159 | 171 | 200 | 212 | 224 | 253 | 265 | 277 => ⟨!![1,1;-3,-2], by decide⟩
  | 30 | 43 | 56 | 69 | 99 | 112 | 125 | 138 | 168 | 181 | 194 | 207 | 237 | 250 | 263 | 276 => ⟨!![0,-1;1,-4], by decide⟩
  | 31 | 45 | 59 | 73 | 87 | 118 | 132 | 146 | 160 | 174 | 188 | 219 | 233 | 247 | 261 | 275 => ⟨!![0,-1;1,-3], by decide⟩
  | 32 | 47 | 62 | 77 | 92 | 107 | 122 | 137 | 169 | 184 | 199 | 214 | 229 | 244 | 259 | 274 => ⟨!![0,-1;1,-2], by decide⟩
  | 33 | 49 | 65 | 81 | 97 | 113 | 129 | 145 | 161 | 177 | 193 | 209 | 225 | 241 | 257 | 273 => ⟨!![0,-1;1,-1], by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 17) : List (Fin 11) :=
  match c.val*17+d.val with
  | 17 | 34 | 51 | 68 | 85 | 102 | 119 | 136 | 153 | 170 | 187 | 204 | 221 | 238 | 255 | 272 => [4]
  | 18 | 36 | 54 | 72 | 90 | 108 | 126 | 144 | 162 | 180 | 198 | 216 | 234 | 252 | 270 | 288 => [1]
  | 21 | 42 | 63 | 84 | 88 | 109 | 130 | 151 | 155 | 176 | 197 | 218 | 222 | 243 | 264 | 285 => [7, 5, 3, 10]
  | 22 | 44 | 66 | 71 | 93 | 115 | 120 | 142 | 164 | 186 | 191 | 213 | 235 | 240 | 262 | 284 => [7]
  | 23 | 46 | 52 | 75 | 98 | 104 | 127 | 150 | 156 | 179 | 202 | 208 | 231 | 254 | 260 | 283 => [4]
  | 25 | 50 | 58 | 83 | 91 | 116 | 124 | 149 | 157 | 182 | 190 | 215 | 223 | 248 | 256 | 281 => [4]
  | 26 | 35 | 61 | 70 | 96 | 105 | 131 | 140 | 166 | 175 | 201 | 210 | 236 | 245 | 271 | 280 => [4]
  | 27 | 37 | 64 | 74 | 101 | 111 | 121 | 148 | 158 | 185 | 195 | 205 | 232 | 242 | 269 | 279 => [4, 8]
  | 28 | 39 | 67 | 78 | 89 | 117 | 128 | 139 | 167 | 178 | 189 | 217 | 228 | 239 | 267 | 278 => [4]
  | 29 | 41 | 53 | 82 | 94 | 106 | 135 | 147 | 159 | 171 | 200 | 212 | 224 | 253 | 265 | 277 => [4]
  | 30 | 43 | 56 | 69 | 99 | 112 | 125 | 138 | 168 | 181 | 194 | 207 | 237 | 250 | 263 | 276 => [8, 6, 0, 9]
  | 33 | 49 | 65 | 81 | 97 | 113 | 129 | 145 | 161 | 177 | 193 | 209 | 225 | 241 | 257 | 273 => [0, 4]
  | _ => []

def edgeTRow (c d : ZMod 17) : List (Fin 11) :=
  match c.val*17+d.val with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => [0]
  | 22 | 44 | 66 | 71 | 93 | 115 | 120 | 142 | 164 | 186 | 191 | 213 | 235 | 240 | 262 | 284 => [4, 7]
  | 23 | 46 | 52 | 75 | 98 | 104 | 127 | 150 | 156 | 179 | 202 | 208 | 231 | 254 | 260 | 283 => [4, 8, 6, 0]
  | 25 | 50 | 58 | 83 | 91 | 116 | 124 | 149 | 157 | 182 | 190 | 215 | 223 | 248 | 256 | 281 => [1, 4]
  | 27 | 37 | 64 | 74 | 101 | 111 | 121 | 148 | 158 | 185 | 195 | 205 | 232 | 242 | 269 | 279 => [4, 5, 3, 10]
  | 28 | 39 | 67 | 78 | 89 | 117 | 128 | 139 | 167 | 178 | 189 | 217 | 228 | 239 | 267 | 278 => [4]
  | 29 | 41 | 53 | 82 | 94 | 106 | 135 | 147 | 159 | 171 | 200 | 212 | 224 | 253 | 265 | 277 => [4, 9]
  | _ => []

def rep (g : SL(2,ZMod 17)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_nonzero (g : SL(2,ZMod 17)) : g.1 1 0≠0 ∨ g.1 1 1≠0 := by
  by_contra h
  push Not at h
  have hd := g.det_coe
  rw [det_fin_two, h.1, h.2] at hd
  norm_num at hd
  exact (by decide : (0:ZMod 17)≠1) hd

theorem edgeSRow_checked : ∀ c d : ZMod 17, c≠0 ∨ d≠0 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by decide

theorem edgeTRow_checked : ∀ c d : ZMod 17, c≠0 ∨ d≠0 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by decide

theorem edgeS_checked (g : SL(2,ZMod 17)) :
    rep g*S*(rep (g*reduction 17 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 17 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 17 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 17)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_nonzero g)

theorem edgeT_checked (g : SL(2,ZMod 17)) :
    rep g*T*(rep (g*reduction 17 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 17 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 17 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 17)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_nonzero g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 17)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 17, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 17∈K) (hZ : -1∈K)
    (h2 : oddMatrix 17 9 (by decide)∈K) (h3 : A∈K) (h6 : B∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 17) : γ∈K := by
  apply transversal_mem (reduction 17) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hT hU hZ h2 h3 h6 _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hT hU hZ h2 h3 h6 _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeS_checked
#print axioms edgeT_checked
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelSeventeen
end
end

/-! ## QuantitativeArithmeticSmallLevelSeventeenRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelSeventeen

open Matrix UpperHalfPlane SmallLevelNormalized Complex Filter Set
open scoped MatrixGroups ModularForm Manifold Topology

def elliptic : SL(2,ℚ) := ⟨!![1,-2/3;17/3,-25/9], by norm_num [det_fin_two]⟩
def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem elliptic_factor : ellipticReal =
    SpecialLinearGroup.mapGL ℝ A⁻¹ * translation (-1/3) *
      SpecialLinearGroup.mapGL ℝ B⁻¹ * translation (-2/3) := by
  rw [A_inv, B_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ellipticReal, elliptic, SmallLevelNormalized.translation, SmallLevelNormalized.matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Two paired Ramanujan equations transport the two transformation defects
into each other. The algebra requires no division by any eigenvalue. -/
theorem pair_transport (g : ℍ → ℂ) (k : ℤ) (C D R : GL (Fin 2) ℝ)
    (hp : (g ∣[k] C) + ((g ∣[k] D⁻¹) ∣[k] R) = g + (g ∣[k] R)) :
    (g ∣[k] C) - g = ((g ∣[k] D) - g) ∣[k] (D⁻¹ * R) := by
  simp only [SmallLevelEleven.sub_slash, ← SlashAction.slash_mul,
    ← mul_assoc, mul_inv_cancel, one_mul]
  rw [SlashAction.slash_mul]
  linear_combination hp

theorem original_defect_elliptic {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) -
      SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] ellipticReal =
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) -
      SmallLevelOriginal.fourierFunction k f := by
  let g := SmallLevelOriginal.fourierFunction k f
  let a := SpecialLinearGroup.mapGL ℝ A
  let b := SpecialLinearGroup.mapGL ℝ B
  have h3 : (g ∣[(k:ℤ)] a) + ((g ∣[(k:ℤ)] b⁻¹) ∣[(k:ℤ)] translation (-2/3)) =
      g + (g ∣[(k:ℤ)] translation (-2/3)) := by
    rw [show b⁻¹=SpecialLinearGroup.mapGL ℝ B⁻¹ from (map_inv _ _).symm]
    exact original_three_reduced hf
  have h6 : (g ∣[(k:ℤ)] b) + ((g ∣[(k:ℤ)] a⁻¹) ∣[(k:ℤ)] translation (-1/3)) =
      g + (g ∣[(k:ℤ)] translation (-1/3)) := by
    rw [show a⁻¹=SpecialLinearGroup.mapGL ℝ A⁻¹ from (map_inv _ _).symm]
    exact original_six_reduced hf
  have ht3 := pair_transport g k a b (translation (-2/3)) h3
  have ht6 := pair_transport g k b a (translation (-1/3)) h6
  have he : ellipticReal = (a⁻¹ * translation (-1/3)) * (b⁻¹ * translation (-2/3)) := by
    simpa only [a, b, map_inv, mul_assoc] using elliptic_factor
  change ((g ∣[(k:ℤ)] a)-g) ∣[(k:ℤ)] ellipticReal = (g ∣[(k:ℤ)] a)-g
  rw [he, SlashAction.slash_mul, ← ht6, ← ht3]

def fixedPoint : ℂ := ⟨1/3, Real.sqrt 17/51⟩

theorem fixedPoint_positive : 0 < fixedPoint.im := by
  change 0 < Real.sqrt 17/51
  positivity

theorem fixedPoint_denom : (17/3:ℂ)*fixedPoint-25/9 ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (fixedPoint-2/3)/((17/3)*fixedPoint-25/9) = fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((z-2/3)/((17/3)*z-25/9))=((17/3)*z-25/9)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-16/9:ℚ)≠m := by
    intro hm
    have hh : (9:ℚ)*m = -16 := by rw [← hm]; norm_num
    have hi : (9:ℤ)*m = -16 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((1*z+(-2/3))/((17/3)*z+(-25/9)))=((17/3)*z+(-25/9))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [one_mul, sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1) (b:= -2/3) (c:=17/3) (d:= -25/9) (t:=(-16/9:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [one_mul, sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z = (17/3)*(z:ℂ)-25/9 := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=((z:ℂ)-2/3)/((17/3)*(z:ℂ)-25/9) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num, denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F ((z-2/3)/((17/3)*z-25/9))=((17/3)*z-25/9)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    change F ((z-2/3)/((17/3)*z-25/9))*(((17/3)*z-25/9)^k)⁻¹=F z at hh
    have hd : ((17/3)*z-25/9:ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*((17/3)*z-25/9)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

theorem original_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A =
      SmallLevelOriginal.fourierFunction k f := by
  have hhol := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hd := (hhol.slash (k:ℤ) (SpecialLinearGroup.mapGL ℝ A)).sub hhol
  exact sub_eq_zero.mp (invariant_zero hk _ hd (original_defect_elliptic hf))

theorem original_B {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B =
      SmallLevelOriginal.fourierFunction k f := by
  have ha := original_A hk hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] A⁻¹) ha
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  have hh := original_six_reduced hf
  rw [← hi] at hh
  exact add_right_cancel hh

#print axioms original_defect_elliptic
#print axioms elliptic_defect_zero
#print axioms original_A
#print axioms original_B

end QuantitativeArithmeticSmallLevelSeventeen
end
end

/-! ## QuantitativeArithmeticSmallLevelSeventeenModularV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelSeventeen

open Matrix ModularGroup SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

theorem gamma_zero_seventeen (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 17) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 17∈K := original_lower (by decide) hf
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  change γ∈K
  exact gamma0_mem K ht hu hz
    (original_odd (by decide) (by decide : 2*9=17+1) (by decide) hf)
    (original_A (by omega) hf) (original_B (by omega) hf) γ hγ

/-- The literal Euler input gives a genuine Mathlib modular form at level
17 in every positive even weight, with no extra twist or eigenvalue premise. -/
theorem level_seventeen {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 17 k f) : IsModular 17 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_seventeen m (by omega) hf)

#print axioms gamma_zero_seventeen
#print axioms level_seventeen

end QuantitativeArithmeticSmallLevelSeventeen
end
end
