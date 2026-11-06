module

public import QuantitativeArithmeticPrimitiveResiduePairV4
public import SmallLevelModularCriterionV1
public import SmallLevelTransversalV1
public import SmallLevelTwentySixPairMatricesV1
public import SmallLevelTwentySixTwelfthCentersV1

/-! Consolidated chapter: SmallLevelTwentySixGroup. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixGroupKernelMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelTwentySixTwelfth (E W E_det)
open SmallLevelTwentySix (P P_det)

def Y : SL(2,ℤ) := ⟨!![3,-1;-26,9],by decide⟩

def kernel : Fin 14 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![15,1;104,7],by decide⟩
  | 2 => ⟨!![3,-1;-26,9],by decide⟩
  | 3 => ⟨!![27,2;-338,-25],by decide⟩
  | 4 => ⟨!![15,-8;-208,111],by decide⟩
  | 5 => ⟨!![9,-2;-130,29],by decide⟩
  | 6 => ⟨!![81,5;-1118,-69],by decide⟩
  | 7 => ⟨!![1,0;-26,1],by decide⟩
  | 8 => ⟨!![111,8;208,15],by decide⟩
  | 9 => ⟨!![55,4;-234,-17],by decide⟩
  | 10 => ⟨!![9,1;26,3],by decide⟩
  | 11 => ⟨!![183,13;-2548,-181],by decide⟩
  | 12 => ⟨!![19,3;-260,-41],by decide⟩
  | 13 => ⟨!![69,5;-1118,-81],by decide⟩

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
  | 9 => true
  | 10 => false
  | 11 => false
  | 12 => true
  | 13 => true

/-- Exact determinant-one versions of the Schreier generators. Central
minus signs are retained explicitly and vanish only at even weight. -/
theorem kernel_relation (i : Fin 14) :
    SpecialLinearGroup.mapGL ℝ (kernel i)*kernelRep (targetIndex i)=
      (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex i)*kernelGenerator (symbolIndex i) := by
  have hs : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 26≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [kernel,kernelRep,kernelGenerator,sourceIndex,symbolIndex,targetIndex,kernelNegative,
      E,P,Y,W,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 26)^2) ht]

#print axioms kernel_relation
end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupGeneratorDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelTwentySixGroup
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

def repRow (c d : ZMod 26) : SL(2,ℤ) :=
  match c.val*26+d.val with
  | 26 | 78 | 130 | 182 | 234 | 286 | 390 | 442 | 494 | 546 | 598 | 650 => ⟨!![0,-1;1,0],by decide⟩
  | 27 | 81 | 135 | 189 | 243 | 297 | 405 | 459 | 513 | 567 | 621 | 675 => ⟨!![0,-1;1,1],by decide⟩
  | 51 | 101 | 151 | 201 | 251 | 301 | 401 | 451 | 501 | 551 | 601 | 651 => ⟨!![0,-1;1,-1],by decide⟩
  | 28 | 84 | 140 | 196 | 252 | 308 | 394 | 450 | 506 | 562 | 618 | 674 => ⟨!![0,-1;1,2],by decide⟩
  | 50 | 98 | 146 | 194 | 242 | 290 | 412 | 460 | 508 | 556 | 604 | 652 => ⟨!![0,-1;1,-2],by decide⟩
  | 77 | 115 | 179 | 217 | 281 | 319 | 383 | 421 | 485 | 523 | 587 | 625 => ⟨!![-1,0;2,-1],by decide⟩
  | 29 | 87 | 145 | 203 | 235 | 293 | 409 | 467 | 499 | 557 | 615 | 673 => ⟨!![0,-1;1,3],by decide⟩
  | 53 | 119 | 159 | 225 | 265 | 331 | 371 | 437 | 477 | 543 | 583 | 649 => ⟨!![-1,0;-2,-1],by decide⟩
  | 49 | 95 | 141 | 187 | 259 | 305 | 397 | 443 | 515 | 561 | 607 | 653 => ⟨!![0,-1;1,-3],by decide⟩
  | 75 | 111 | 173 | 209 | 271 | 333 | 369 | 431 | 493 | 529 | 591 | 627 => ⟨!![-1,1;2,-3],by decide⟩
  | 43 | 103 | 137 | 197 | 257 | 291 | 411 | 445 | 505 | 565 | 599 | 659 => ⟨!![-1,0;3,-1],by decide⟩
  | 30 | 90 | 150 | 184 | 244 | 304 | 398 | 458 | 518 | 552 | 612 | 672 => ⟨!![0,-1;1,4],by decide⟩
  | 55 | 123 | 165 | 233 | 275 | 317 | 385 | 427 | 469 | 537 | 579 | 647 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 35 | 79 | 149 | 193 | 237 | 307 | 395 | 465 | 509 | 553 | 623 | 667 => ⟨!![-1,0;-3,-1],by decide⟩
  | 48 | 92 | 136 | 206 | 250 | 294 | 408 | 452 | 496 | 566 | 610 | 654 => ⟨!![0,-1;1,-4],by decide⟩
  | 44 | 80 | 142 | 204 | 240 | 302 | 400 | 462 | 498 | 560 | 622 | 658 => ⟨!![1,1;-3,-2],by decide⟩
  | 73 | 107 | 167 | 227 | 261 | 321 | 381 | 441 | 475 | 535 | 595 | 629 => ⟨!![-1,2;2,-5],by decide⟩
  | 42 | 100 | 132 | 190 | 248 | 306 | 396 | 454 | 512 | 570 | 602 | 660 => ⟨!![-1,1;3,-4],by decide⟩
  | 71 | 129 | 161 | 219 | 277 | 335 | 367 | 425 | 483 | 541 | 573 | 631 => ⟨!![-1,0;4,-1],by decide⟩
  | 31 | 93 | 155 | 191 | 253 | 289 | 413 | 449 | 511 | 547 | 609 | 671 => ⟨!![0,-1;1,5],by decide⟩
  | 34 | 102 | 144 | 186 | 254 | 296 | 406 | 448 | 516 | 558 | 600 | 668 => ⟨!![-1,1;-3,2],by decide⟩
  | 57 | 127 | 171 | 215 | 285 | 329 | 373 | 417 | 487 | 531 | 575 | 645 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 36 | 82 | 154 | 200 | 246 | 292 | 410 | 456 | 502 | 548 | 620 | 666 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 59 | 105 | 177 | 223 | 269 | 315 | 387 | 433 | 479 | 525 | 597 | 643 => ⟨!![-1,0;-4,-1],by decide⟩
  | 47 | 89 | 131 | 199 | 241 | 309 | 393 | 461 | 503 | 571 | 613 | 655 => ⟨!![0,-1;1,-5],by decide⟩
  | 45 | 83 | 147 | 185 | 249 | 287 | 415 | 453 | 517 | 555 | 619 | 657 => ⟨!![1,2;-3,-5],by decide⟩
  | 41 | 97 | 153 | 183 | 239 | 295 | 407 | 463 | 519 | 549 | 605 | 661 => ⟨!![-1,2;3,-7],by decide⟩
  | 69 | 125 | 181 | 211 | 267 | 323 | 379 | 435 | 491 | 521 | 577 | 633 => ⟨!![-1,1;4,-5],by decide⟩
  | 32 | 96 | 134 | 198 | 236 | 300 | 402 | 466 | 504 | 568 | 606 | 670 => ⟨!![0,-1;1,6],by decide⟩
  | 33 | 99 | 139 | 205 | 245 | 311 | 391 | 457 | 497 | 563 | 603 | 669 => ⟨!![-1,2;-3,5],by decide⟩
  | 37 | 85 | 133 | 207 | 255 | 303 | 399 | 447 | 495 | 569 | 617 | 665 => ⟨!![-1,-2;-3,-7],by decide⟩
  | 61 | 109 | 157 | 231 | 279 | 327 | 375 | 423 | 471 | 545 | 593 | 641 => ⟨!![-1,-1;-4,-5],by decide⟩
  | 46 | 86 | 152 | 192 | 258 | 298 | 404 | 444 | 510 | 550 | 616 | 656 => ⟨!![0,-1;1,-6],by decide⟩
  | 40 | 94 | 148 | 202 | 256 | 310 | 392 | 446 | 500 | 554 | 608 | 662 => ⟨!![-1,3;3,-10],by decide⟩
  | 67 | 121 | 175 | 229 | 283 | 337 | 365 | 419 | 473 | 527 | 581 | 635 => ⟨!![-1,2;4,-9],by decide⟩
  | 38 | 88 | 138 | 188 | 238 | 288 | 414 | 464 | 514 | 564 | 614 | 664 => ⟨!![-1,-3;-3,-10],by decide⟩
  | 63 | 113 | 163 | 213 | 263 | 313 | 389 | 439 | 489 | 539 | 589 | 639 => ⟨!![-1,-2;-4,-9],by decide⟩
  | 39 | 91 | 143 | 195 | 247 | 299 | 403 | 455 | 507 | 559 | 611 | 663 => ⟨!![-1,4;3,-13],by decide⟩
  | 65 | 117 | 169 | 221 | 273 | 325 | 377 | 429 | 481 | 533 | 585 | 637 => ⟨!![-1,3;4,-13],by decide⟩
  | 339 | 341 | 343 | 345 | 347 | 349 | 353 | 355 | 357 | 359 | 361 | 363 => ⟨!![4,1;-13,-3],by decide⟩
  | 340 | 342 | 344 | 346 | 348 | 350 | 352 | 354 | 356 | 358 | 360 | 362 => ⟨!![3,1;-13,-4],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 26) : List (Fin 29) :=
  match c.val*26+d.val with
  | 26 | 78 | 130 | 182 | 234 | 286 | 390 | 442 | 494 | 546 | 598 | 650 => [28]
  | 27 | 81 | 135 | 189 | 243 | 297 | 405 | 459 | 513 | 567 | 621 | 675 => [14]
  | 51 | 101 | 151 | 201 | 251 | 301 | 401 | 451 | 501 | 551 | 601 | 651 => [0,28]
  | 77 | 115 | 179 | 217 | 281 | 319 | 383 | 421 | 485 | 523 | 587 | 625 => [28]
  | 53 | 119 | 159 | 225 | 265 | 331 | 371 | 437 | 477 | 543 | 583 | 649 => [28]
  | 43 | 103 | 137 | 197 | 257 | 291 | 411 | 445 | 505 | 565 | 599 | 659 => [28]
  | 35 | 79 | 149 | 193 | 237 | 307 | 395 | 465 | 509 | 553 | 623 | 667 => [28]
  | 44 | 80 | 142 | 204 | 240 | 302 | 400 | 462 | 498 | 560 | 622 | 658 => [28]
  | 73 | 107 | 167 | 227 | 261 | 321 | 381 | 441 | 475 | 535 | 595 | 629 => [14,8,28,23]
  | 42 | 100 | 132 | 190 | 248 | 306 | 396 | 454 | 512 | 570 | 602 | 660 => [9,4,0]
  | 71 | 129 | 161 | 219 | 277 | 335 | 367 | 425 | 483 | 541 | 573 | 631 => [28]
  | 31 | 93 | 155 | 191 | 253 | 289 | 413 | 449 | 511 | 547 | 609 | 671 => [26,23]
  | 34 | 102 | 144 | 186 | 254 | 296 | 406 | 448 | 516 | 558 | 600 | 668 => [28]
  | 57 | 127 | 171 | 215 | 285 | 329 | 373 | 417 | 487 | 531 | 575 | 645 => [8,11,5]
  | 36 | 82 | 154 | 200 | 246 | 292 | 410 | 456 | 502 | 548 | 620 | 666 => [19,25,28,4]
  | 59 | 105 | 177 | 223 | 269 | 315 | 387 | 433 | 479 | 525 | 597 | 643 => [28]
  | 47 | 89 | 131 | 199 | 241 | 309 | 393 | 461 | 503 | 571 | 613 | 655 => [1,5]
  | 45 | 83 | 147 | 185 | 249 | 287 | 415 | 453 | 517 | 555 | 619 | 657 => [14,8,28,23]
  | 41 | 97 | 153 | 183 | 239 | 295 | 407 | 463 | 519 | 549 | 605 | 661 => [9,4,0]
  | 69 | 125 | 181 | 211 | 267 | 323 | 379 | 435 | 491 | 521 | 577 | 633 => [9,12]
  | 32 | 96 | 134 | 198 | 236 | 300 | 402 | 466 | 504 | 568 | 606 | 670 => [9,12]
  | 33 | 99 | 139 | 205 | 245 | 311 | 391 | 457 | 497 | 563 | 603 | 669 => [8,11,28,5]
  | 37 | 85 | 133 | 207 | 255 | 303 | 399 | 447 | 495 | 569 | 617 | 665 => [19,25,4]
  | 61 | 109 | 157 | 231 | 279 | 327 | 375 | 423 | 471 | 545 | 593 | 641 => [1,5]
  | 46 | 86 | 152 | 192 | 258 | 298 | 404 | 444 | 510 | 550 | 616 | 656 => [1,5]
  | 40 | 94 | 148 | 202 | 256 | 310 | 392 | 446 | 500 | 554 | 608 | 662 => [9,6,5]
  | 67 | 121 | 175 | 229 | 283 | 337 | 365 | 419 | 473 | 527 | 581 | 635 => [9,17,2]
  | 38 | 88 | 138 | 188 | 238 | 288 | 414 | 464 | 514 | 564 | 614 | 664 => [10,3,28,23]
  | 63 | 113 | 163 | 213 | 263 | 313 | 389 | 439 | 489 | 539 | 589 | 639 => [19,13,23]
  | 339 | 341 | 343 | 345 | 347 | 349 | 353 | 355 | 357 | 359 | 361 | 363 => [28]
  | 340 | 342 | 344 | 346 | 348 | 350 | 352 | 354 | 356 | 358 | 360 | 362 => [28]
  | _ => []

def edgeTRow (c d : ZMod 26) : List (Fin 29) :=
  match c.val*26+d.val with
  | 1 | 3 | 5 | 7 | 9 | 11 | 15 | 17 | 19 | 21 | 23 | 25 => [0]
  | 77 | 115 | 179 | 217 | 281 | 319 | 383 | 421 | 485 | 523 | 587 | 625 => [14,28]
  | 43 | 103 | 137 | 197 | 257 | 291 | 411 | 445 | 505 | 565 | 599 | 659 => [28]
  | 71 | 129 | 161 | 219 | 277 | 335 | 367 | 425 | 483 | 541 | 573 | 631 => [9,4,28,0]
  | 57 | 127 | 171 | 215 | 285 | 329 | 373 | 417 | 487 | 531 | 575 | 645 => [8,11,28,5]
  | 45 | 83 | 147 | 185 | 249 | 287 | 415 | 453 | 517 | 555 | 619 | 657 => [9,27,7]
  | 32 | 96 | 134 | 198 | 236 | 300 | 402 | 466 | 504 | 568 | 606 | 670 => [2,28]
  | 38 | 88 | 138 | 188 | 238 | 288 | 414 | 464 | 514 | 564 | 614 | 664 => [10,13,23]
  | 63 | 113 | 163 | 213 | 263 | 313 | 389 | 439 | 489 | 539 | 589 | 639 => [19,23,28]
  | 339 | 341 | 343 | 345 | 347 | 349 | 353 | 355 | 357 | 359 | 361 | 363 => [9,27,3,23]
  | 340 | 342 | 344 | 346 | 348 | 350 | 352 | 354 | 356 | 358 | 360 | 362 => [9,13,23]
  | _ => []

def rep (g : SL(2,ZMod 26)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 26)) :
    ∃ a b : ZMod 26, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe


end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupGeneratorRowsSV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelTwentySixGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups



























theorem edgeSRow_checked : ∀ c d : ZMod 26, (∃ a b : ZMod 26, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 26,
    Nat.gcd (Nat.gcd c.val d.val) 26 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeSRow_checked
end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupGeneratorRowsTV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelTwentySixGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups



























theorem edgeTRow_checked : ∀ c d : ZMod 26, (∃ a b : ZMod 26, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 26,
    Nat.gcd (Nat.gcd c.val d.val) 26 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeTRow_checked
end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupGeneratorsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace SmallLevelTwentySixGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeS_checked (g : SL(2,ZMod 26)) :
    rep g*S*(rep (g*reduction 26 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 26 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 26 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 26)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 26)) :
    rep g*T*(rep (g*reduction 26 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 26 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 26 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 26)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 26)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 26, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 14, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 26) : γ∈K := by
  apply transversal_mem (reduction 26) rep K
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

end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupKernelActionsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelTwentySixTwelfth (E W E_det)
open SmallLevelTwentySix (P P_det)

def repCharacter (δ η : ℂ) : Fin 4 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | _ => δ*η

def generatorCharacter (δ η : ℂ) : Fin 5 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | 3 => δ
  | _ => 1

theorem kernelGenerator_det (j : Fin 5) : (GeneralLinearGroup.det (kernelGenerator j):ℝ)=1 := by
  fin_cases j
  · exact translation_det _
  · exact E_det
  · exact fricke_det 26 (by decide)
  · exact P_det
  · simp [kernelGenerator]

theorem rep_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hE : F ∣[k] E=δ • F) (hW : F ∣[k] W=η • F) (j : Fin 4) :
    F ∣[k] kernelRep j=repCharacter δ η j • F := by
  fin_cases j
  · simp [kernelRep,repCharacter]
  · exact hE
  · exact hW
  · change F ∣[k] (E*W)=(δ*η) • F
    rw [SlashAction.slash_mul,hE,det_one_smul _ (show (GeneralLinearGroup.det W:ℝ)=1 from fricke_det _ _),hW,smul_smul]

theorem generator_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hT : F ∣[k] translation 1=F) (hE : F ∣[k] E=δ • F)
    (hW : F ∣[k] W=η • F) (hP : F ∣[k] P=δ • F)
    (hY : F ∣[k] Y=F) (j : Fin 5) :
    F ∣[k] kernelGenerator j=generatorCharacter δ η j • F := by
  fin_cases j
  · change F ∣[k] translation 1=(1:ℂ) • F
    simpa only [one_smul] using hT
  · exact hE
  · exact hW
  · exact hP
  · change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=(1:ℂ) • F
    rw [one_smul]
    change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=F at hY
    exact hY

theorem character_relation (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1) (i : Fin 14) :
    repCharacter δ η (sourceIndex i)*generatorCharacter δ η (symbolIndex i)=
      repCharacter δ η (targetIndex i) := by
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> fin_cases i <;>
    norm_num [repCharacter,generatorCharacter,sourceIndex,symbolIndex,targetIndex]

/-- Every integral Schreier generator has trivial character. -/
theorem kernel_invariant (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hP : F ∣[((2*m:ℕ):ℤ)] P=δ • F)
    (hY : F ∣[((2*m:ℕ):ℤ)] Y=F) (i : Fin 14) :
    F ∣[((2*m:ℕ):ℤ)] kernel i=F := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hc : F ∣[k] (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)=F := by
    split_ifs
    · exact central_even F m
    · simp only [SlashAction.slash_one]
  have hh : (F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)) ∣[k] kernelRep (targetIndex i)=
      F ∣[k] kernelRep (targetIndex i) := by
    rw [← SlashAction.slash_mul,kernel_relation,SlashAction.slash_mul,SlashAction.slash_mul,hc,
      rep_eigen F δ η hE hW,det_one_smul _ (kernelGenerator_det _),
      generator_eigen F δ η hT hE hW hP hY,smul_smul,character_relation δ η hδ hη,
      rep_eigen F δ η hE hW]
  have he:=congrArg (fun G : ℍ→ℂ => G ∣[k] (kernelRep (targetIndex i))⁻¹) hh
  change F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)=F
  simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using he

#print axioms kernel_invariant
end SmallLevelTwentySixGroup
end
end

/-! ## SmallLevelTwentySixGroupModularCriterionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open scoped MatrixGroups ModularForm
open SmallLevelTwentySixTwelfth (E W)
open SmallLevelTwentySix (P)

/-- Conditional group endgame. The P and denominator-three G laws remain
explicit analytic obligations; this does not assert level26 modularity. -/
theorem modular_of_P_G (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hP : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • fourierFunction (2*m) f)
    (hG : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Y=fourierFunction (2*m) f) :
    IsModular 26 (2*m) f := by
  let F:=fourierFunction (2*m) f
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<26) m hf
  have hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  apply modular_of_transformations (by decide) hf
  intro γ hγ
  let K:=slashStabilizer ((2*m:ℕ):ℤ) F
  change γ∈K
  apply gamma0_mem K ?_ (SmallLevelThirtySix.slash_neg_one_even F m) γ hγ
  intro i
  exact kernel_invariant m F (FinitenessNormalizedTwistProduct.root 26 f 2) η
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) hη hT
    (SmallLevelTwentySixTwelfth.original_E hf) hW hP hG i

#print axioms modular_of_P_G
end SmallLevelTwentySixGroup
end
end
