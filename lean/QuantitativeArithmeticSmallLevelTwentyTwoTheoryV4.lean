module

public import QuantitativeArithmeticPrimitiveResiduePairV4
public import QuantitativeArithmeticSmallLevelTwentyTwoFivePairCriterionV1
public import QuantitativeArithmeticSmallLevelTwentyTwoGridWordRowsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyTwo. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoKernelMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

def kernel : Fin 14 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![35,3;198,17],by decide⟩
  | 2 => ⟨!![3,1;-22,-7],by decide⟩
  | 3 => ⟨!![23,2;-242,-21],by decide⟩
  | 4 => ⟨!![13,-7;-154,83],by decide⟩
  | 5 => ⟨!![7,2;-88,-25],by decide⟩
  | 6 => ⟨!![267,23;-3146,-271],by decide⟩
  | 7 => ⟨!![1,0;-22,1],by decide⟩
  | 8 => ⟨!![83,7;154,13],by decide⟩
  | 9 => ⟨!![25,2;-88,-7],by decide⟩
  | 10 => ⟨!![7,-1;22,-3],by decide⟩
  | 11 => ⟨!![133,11;-1584,-131],by decide⟩
  | 12 => ⟨!![17,-3;-198,35],by decide⟩
  | 13 => ⟨!![37,3;-506,-41],by decide⟩

def kernelRep : Fin 4 → GL (Fin 2) ℝ
  | 0 => 1
  | 1 => E
  | 2 => W
  | _ => E*W

def kernelGenerator : Fin 5 → GL (Fin 2) ℝ
  | 0 => translation 1
  | 1 => E
  | 2 => W
  | 3 => P
  | _ => SpecialLinearGroup.mapGL ℝ Y

def sourceIndex : Fin 14 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 3
  | 12 => 3
  | 13 => 3

def symbolIndex : Fin 14 → Fin 5
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 3
  | 6 => 4
  | 7 => 0
  | 8 => 1
  | 9 => 3
  | 10 => 4
  | 11 => 0
  | 12 => 3
  | 13 => 4

def targetIndex : Fin 14 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | 9 => 3
  | 10 => 2
  | 11 => 3
  | 12 => 2
  | 13 => 3

def kernelNegative : Fin 14 → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => false
  | 4 => false
  | 5 => true
  | 6 => false
  | 7 => false
  | 8 => false
  | 9 => false
  | 10 => true
  | 11 => false
  | 12 => false
  | 13 => false

/-- Exact determinant-one versions of the Schreier generators. Central
minus signs are retained explicitly and vanish only at even weight. -/
theorem kernel_relation (i : Fin 14) :
    SpecialLinearGroup.mapGL ℝ (kernel i)*kernelRep (targetIndex i)=
      (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex i)*kernelGenerator (symbolIndex i) := by
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [kernel,kernelRep,kernelGenerator,sourceIndex,symbolIndex,targetIndex,kernelNegative,
      E_explicit,P,Y,W,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

#print axioms kernel_relation
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoGeneratorDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 29 → SL(2,ℤ)
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
  | 10 => kernel 10
  | 11 => kernel 11
  | 12 => kernel 12
  | 13 => kernel 13
  | 14 => (kernel 0)⁻¹
  | 15 => (kernel 1)⁻¹
  | 16 => (kernel 2)⁻¹
  | 17 => (kernel 3)⁻¹
  | 18 => (kernel 4)⁻¹
  | 19 => (kernel 5)⁻¹
  | 20 => (kernel 6)⁻¹
  | 21 => (kernel 7)⁻¹
  | 22 => (kernel 8)⁻¹
  | 23 => (kernel 9)⁻¹
  | 24 => (kernel 10)⁻¹
  | 25 => (kernel 11)⁻¹
  | 26 => (kernel 12)⁻¹
  | 27 => (kernel 13)⁻¹
  | _ => -1

def word (w : List (Fin 29)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 14, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 29)) : word w∈K := by
  have hl (i : Fin 29) : letter i∈K := by
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
    · exact hK 10
    · exact hK 11
    · exact hK 12
    · exact hK 13
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
    · exact K.inv_mem (hK 10)
    · exact K.inv_mem (hK 11)
    · exact K.inv_mem (hK 12)
    · exact K.inv_mem (hK 13)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 22) : SL(2,ℤ) :=
  match c.val*22+d.val with
  | 22 | 66 | 110 | 154 | 198 | 286 | 330 | 374 | 418 | 462 => ⟨!![0,-1;1,0],by decide⟩
  | 23 | 69 | 115 | 161 | 207 | 299 | 345 | 391 | 437 | 483 => ⟨!![0,-1;1,1],by decide⟩
  | 43 | 85 | 127 | 169 | 211 | 295 | 337 | 379 | 421 | 463 => ⟨!![0,-1;1,-1],by decide⟩
  | 24 | 72 | 120 | 168 | 216 | 290 | 338 | 386 | 434 | 482 => ⟨!![0,-1;1,2],by decide⟩
  | 42 | 82 | 122 | 162 | 202 | 304 | 344 | 384 | 424 | 464 => ⟨!![0,-1;1,-2],by decide⟩
  | 65 | 97 | 151 | 183 | 237 | 269 | 323 | 355 | 409 | 441 => ⟨!![-1,0;2,-1],by decide⟩
  | 25 | 75 | 125 | 175 | 203 | 303 | 331 | 381 | 431 | 481 => ⟨!![0,-1;1,3],by decide⟩
  | 45 | 101 | 135 | 191 | 225 | 281 | 315 | 371 | 405 | 461 => ⟨!![-1,0;-2,-1],by decide⟩
  | 41 | 79 | 117 | 155 | 215 | 291 | 351 | 389 | 427 | 465 => ⟨!![0,-1;1,-3],by decide⟩
  | 63 | 93 | 145 | 197 | 227 | 279 | 309 | 361 | 413 | 443 => ⟨!![-1,1;2,-3],by decide⟩
  | 29 | 87 | 123 | 159 | 217 | 289 | 347 | 383 | 419 | 477 => ⟨!![-1,0;3,-1],by decide⟩
  | 26 | 78 | 130 | 160 | 212 | 294 | 346 | 376 | 428 | 480 => ⟨!![0,-1;1,4],by decide⟩
  | 47 | 105 | 141 | 177 | 235 | 271 | 329 | 365 | 401 | 459 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 37 | 67 | 119 | 171 | 201 | 305 | 335 | 387 | 439 | 469 => ⟨!![-1,0;-3,-1],by decide⟩
  | 40 | 76 | 112 | 170 | 206 | 300 | 336 | 394 | 430 | 466 => ⟨!![0,-1;1,-4],by decide⟩
  | 30 | 68 | 128 | 166 | 204 | 302 | 340 | 378 | 438 | 476 => ⟨!![1,1;-3,-2],by decide⟩
  | 61 | 89 | 139 | 189 | 239 | 267 | 317 | 367 | 417 | 445 => ⟨!![-1,2;2,-5],by decide⟩
  | 28 | 84 | 118 | 174 | 208 | 298 | 332 | 388 | 422 | 478 => ⟨!![-1,1;3,-4],by decide⟩
  | 49 | 109 | 147 | 185 | 223 | 283 | 321 | 359 | 397 | 457 => ⟨!![-1,0;4,-1],by decide⟩
  | 27 | 81 | 113 | 167 | 199 | 307 | 339 | 393 | 425 | 479 => ⟨!![0,-1;1,5],by decide⟩
  | 36 | 86 | 114 | 164 | 214 | 292 | 342 | 392 | 420 | 470 => ⟨!![-1,1;-3,2],by decide⟩
  | 38 | 70 | 124 | 156 | 210 | 296 | 350 | 382 | 436 | 468 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 39 | 73 | 129 | 163 | 219 | 287 | 343 | 377 | 433 | 467 => ⟨!![0,-1;1,-5],by decide⟩
  | 31 | 71 | 111 | 173 | 213 | 293 | 333 | 395 | 435 | 475 => ⟨!![1,2;-3,-5],by decide⟩
  | 59 | 107 | 133 | 181 | 229 | 277 | 325 | 373 | 399 | 447 => ⟨!![-1,3;2,-7],by decide⟩
  | 51 | 91 | 153 | 193 | 233 | 273 | 313 | 353 | 415 | 455 => ⟨!![1,1;-4,-3],by decide⟩
  | 35 | 83 | 131 | 157 | 205 | 301 | 349 | 375 | 423 | 471 => ⟨!![-1,0;5,-1],by decide⟩
  | 32 | 74 | 116 | 158 | 200 | 306 | 348 | 390 | 432 | 474 => ⟨!![1,3;-3,-8],by decide⟩
  | 57 | 103 | 149 | 195 | 241 | 265 | 311 | 357 | 403 | 449 => ⟨!![-1,4;2,-9],by decide⟩
  | 53 | 95 | 137 | 179 | 221 | 285 | 327 | 369 | 411 | 453 => ⟨!![1,2;-4,-7],by decide⟩
  | 34 | 80 | 126 | 172 | 218 | 288 | 334 | 380 | 426 | 472 => ⟨!![-1,1;5,-6],by decide⟩
  | 33 | 77 | 121 | 165 | 209 | 297 | 341 | 385 | 429 | 473 => ⟨!![1,4;-3,-11],by decide⟩
  | 55 | 99 | 143 | 187 | 231 | 275 | 319 | 363 | 407 | 451 => ⟨!![-1,5;2,-11],by decide⟩
  | 243 | 245 | 247 | 249 | 251 | 255 | 257 | 259 | 261 | 263 => ⟨!![4,-1;-11,3],by decide⟩
  | 244 | 246 | 248 | 250 | 252 | 254 | 256 | 258 | 260 | 262 => ⟨!![5,1;-11,-2],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 22) : List (Fin 29) :=
  match c.val*22+d.val with
  | 22 | 66 | 110 | 154 | 198 | 286 | 330 | 374 | 418 | 462 => [28]
  | 23 | 69 | 115 | 161 | 207 | 299 | 345 | 391 | 437 | 483 => [14]
  | 43 | 85 | 127 | 169 | 211 | 295 | 337 | 379 | 421 | 463 => [0,28]
  | 65 | 97 | 151 | 183 | 237 | 269 | 323 | 355 | 409 | 441 => [28]
  | 45 | 101 | 135 | 191 | 225 | 281 | 315 | 371 | 405 | 461 => [28]
  | 29 | 87 | 123 | 159 | 217 | 289 | 347 | 383 | 419 | 477 => [28]
  | 37 | 67 | 119 | 171 | 201 | 305 | 335 | 387 | 439 | 469 => [28]
  | 40 | 76 | 112 | 170 | 206 | 300 | 336 | 394 | 430 | 466 => [1,20,4,0]
  | 30 | 68 | 128 | 166 | 204 | 302 | 340 | 378 | 438 | 476 => [28]
  | 61 | 89 | 139 | 189 | 239 | 267 | 317 | 367 | 417 | 445 => [16,3,12]
  | 49 | 109 | 147 | 185 | 223 | 283 | 321 | 359 | 397 | 457 => [28]
  | 36 | 86 | 114 | 164 | 214 | 292 | 342 | 392 | 420 | 470 => [28]
  | 38 | 70 | 124 | 156 | 210 | 296 | 350 | 382 | 436 | 468 => [1,20,4,0]
  | 39 | 73 | 129 | 163 | 219 | 287 | 343 | 377 | 433 | 467 => [1,20,4,0]
  | 31 | 71 | 111 | 173 | 213 | 293 | 333 | 395 | 435 | 475 => [16,3,12]
  | 59 | 107 | 133 | 181 | 229 | 277 | 325 | 373 | 399 | 447 => [16,3,12]
  | 51 | 91 | 153 | 193 | 233 | 273 | 313 | 353 | 415 | 455 => [28]
  | 35 | 83 | 131 | 157 | 205 | 301 | 349 | 375 | 423 | 471 => [28]
  | 32 | 74 | 116 | 158 | 200 | 306 | 348 | 390 | 432 | 474 => [16,3,4,0]
  | 57 | 103 | 149 | 195 | 241 | 265 | 311 | 357 | 403 | 449 => [14,8,20,4,0]
  | 53 | 95 | 137 | 179 | 221 | 285 | 327 | 369 | 411 | 453 => [16]
  | 34 | 80 | 126 | 172 | 218 | 288 | 334 | 380 | 426 | 472 => [2,28]
  | 243 | 245 | 247 | 249 | 251 | 255 | 257 | 259 | 261 | 263 => [28]
  | 244 | 246 | 248 | 250 | 252 | 254 | 256 | 258 | 260 | 262 => [28]
  | _ => []

def edgeTRow (c d : ZMod 22) : List (Fin 29) :=
  match c.val*22+d.val with
  | 1 | 3 | 5 | 7 | 9 | 13 | 15 | 17 | 19 | 21 => [0]
  | 65 | 97 | 151 | 183 | 237 | 269 | 323 | 355 | 409 | 441 => [14,28]
  | 29 | 87 | 123 | 159 | 217 | 289 | 347 | 383 | 419 | 477 => [28]
  | 47 | 105 | 141 | 177 | 235 | 271 | 329 | 365 | 401 | 459 => [8,11,5]
  | 49 | 109 | 147 | 185 | 223 | 283 | 321 | 359 | 397 | 457 => [28]
  | 27 | 81 | 113 | 167 | 199 | 307 | 339 | 393 | 425 | 479 => [2]
  | 38 | 70 | 124 | 156 | 210 | 296 | 350 | 382 | 436 | 468 => [10]
  | 35 | 83 | 131 | 157 | 205 | 301 | 349 | 375 | 423 | 471 => [9,25,4]
  | 53 | 95 | 137 | 179 | 221 | 285 | 327 | 369 | 411 | 453 => [19,4,0]
  | 33 | 77 | 121 | 165 | 209 | 297 | 341 | 385 | 429 | 473 => [16,5,16]
  | 243 | 245 | 247 | 249 | 251 | 255 | 257 | 259 | 261 | 263 => [14,8,6,4,0]
  | 244 | 246 | 248 | 250 | 252 | 254 | 256 | 258 | 260 | 262 => [14,8,28,2]
  | _ => []

def rep (g : SL(2,ZMod 22)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 22)) :
    ∃ a b : ZMod 22, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe


end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoGeneratorRowsSV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups























theorem edgeSRow_checked : ∀ c d : ZMod 22, (∃ a b : ZMod 22, a*d-b*c=1) →
    repRow c d*ModularGroup.S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 22,
    Nat.gcd (Nat.gcd c.val d.val) 22 = 1 →
    repRow c d*ModularGroup.S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeSRow_checked
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoGeneratorRowsTV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups























theorem edgeTRow_checked : ∀ c d : ZMod 22, (∃ a b : ZMod 22, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 22,
    Nat.gcd (Nat.gcd c.val d.val) 22 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeTRow_checked
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoGridTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open scoped MatrixGroups ModularForm

/-- The original signed word laws provide all Taylor orders, with the precise
positive geometric leading factor and a holomorphic error on the enlarged
half-plane. The matrix entries are the determinant-one normalization. -/
theorem original_grid_word_taylor (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ w : List (Fin 4 × Bool),
      let A := (gridWord w).val 0 0
      let B := (gridWord w).val 0 1
      let C := (gridWord w).val 1 0
      let D := (gridWord w).val 1 1
      ∀ j : ℝ, C≠0 → C*j+D≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          original (2*m) f j s-gridWordSign (root 22 f 2) η w*
            (((C*j+D)^2:ℝ):ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (Complex.I*((C*(C*j+D):ℝ):ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              original (2*m) f ((A*j+B)/(C*j+D)) (s+(n:ℂ))) = error M s := by
  obtain ⟨η,hη,hw⟩:=original_grid_words m hf
  obtain ⟨τ,_,hg⟩:=hf.growth
  refine ⟨η,hη,?_⟩
  intro w
  dsimp only
  intro j hC hj
  have hd : (gridWord w).val 0 0*(gridWord w).val 1 1-
      (gridWord w).val 0 1*(gridWord w).val 1 0=1 := by
    have hh:=gridWord_det w
    change (gridWord w).val.det=1 at hh
    simpa only [det_fin_two] using hh
  have hF:=grid_word_fourier (gridWordSign_unit (root_unit hf.toEulerData 2) hη w) (hw w)
  have hh:=QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    ((gridWord w).val 0 0) ((gridWord w).val 0 1) ((gridWord w).val 1 0)
    ((gridWord w).val 1 1) j hC (by rw [hd]; norm_num) hj
    (gridWordSign (root 22 f 2) η w) (by
      intro z hz
      simpa only [hd,Complex.ofReal_one,one_pow,mul_one] using hF z hz)
  simpa only [hd,div_one,original] using hh

#print axioms original_grid_word_taylor
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyTwoGridSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- Only these eight matrix words are needed by the common 66-row system. -/
def gridSourceWord : Fin 8 → List (Fin 4 × Bool)
  | 0 => [(3,false),(0,false)]
  | 1 => [(3,false)]
  | 2 => [(3,false),(0,true)]
  | 3 => [(1,false),(0,true)]
  | 4 => [(1,true),(1,true),(2,false)]
  | 5 => [(1,true),(2,false)]
  | 6 => [(2,false)]
  | 7 => [(1,false),(2,false)]

def gridSourceRaw : Fin 8 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![0,-1;22,22]
  | 1 => !![0,-1;22,0]
  | 2 => !![0,-1;22,-22]
  | 3 => !![1,-1;22,-21]
  | 4 => !![2,-1;-110,56]
  | 5 => !![2,-1;-66,34]
  | 6 => !![2,-1;-22,12]
  | 7 => !![2,-1;22,-10]

def gridSourceDet : Fin 8 → ℕ
  | 0 | 1 | 2 => 22
  | 3 => 1
  | _ => 2

theorem gridSourceRaw_det (i : Fin 8) : (gridSourceRaw i).det=(gridSourceDet i:ℤ) := by
  fin_cases i <;> norm_num [gridSourceRaw,gridSourceDet,det_fin_two]

theorem gridSourceDet_pos (i : Fin 8) : 0<gridSourceDet i := by
  fin_cases i <;> decide

/-- Exact normalization of every selected raw matrix, checked entrywise. -/
theorem gridSource_coordinates (i : Fin 8) :
    (gridWord (gridSourceWord i)).val=
      (1/Real.sqrt (gridSourceDet i)) • (gridSourceRaw i).map (Int.castRingHom ℝ) := by
  have hT : (SpecialLinearGroup.mapGL ℝ T)⁻¹=
      SpecialLinearGroup.mapGL ℝ (⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) := by
    rw [← map_inv,show T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hU : (SpecialLinearGroup.mapGL ℝ (lower 22))⁻¹=
      SpecialLinearGroup.mapGL ℝ (⟨!![1,0;-22,1],by decide⟩ : SL(2,ℤ)) := by
    rw [← map_inv,show (lower 22)⁻¹=(⟨!![1,0;-22,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 22)^2=22:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs2 : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have hn2 : Real.sqrt 2≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;>
    simp only [gridSourceWord,gridWord,gridLetter,gridBase,Bool.false_eq_true,
      ite_false,ite_true,mul_one,hT,hU] <;>
    try rw [E_explicit]
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [gridSourceRaw,gridSourceDet,W,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        T,lower,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
      field_simp [hn,hn2] <;> nlinarith

theorem gridSource_sign (δ η : ℂ) (i : Fin 8) :
    gridWordSign δ η (gridSourceWord i)=
      if i.val<3 then η else if i.val=3 then 1 else δ := by
  fin_cases i <;> simp [gridSourceWord,gridWordSign,gridBaseSign]

#print axioms gridSourceRaw_det
#print axioms gridSource_coordinates
#print axioms gridSource_sign
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end
