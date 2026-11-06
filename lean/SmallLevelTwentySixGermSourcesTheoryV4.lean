module

public import QuantitativeArithmeticAnalyticGermTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelContinuedRegularShiftedV1
public import SmallLevelFiniteGridSupportV1
public import SmallLevelPrimeGridRowsV1
public import SmallLevelRegularPoleTailV1
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelTwentySixGermCoordinateDataV4
public import SmallLevelTwentySixGridCoherentFrickeV1
public import SmallLevelTwentySixGridContinuationV1
public import SmallLevelTwentySixGridParametersV1
public import SmallLevelTwentySixGridPoleSystemV1
public import SmallLevelTwentySixGridRawWordsV1
public import SmallLevelTwentySixGridWordEntireV1
public import SmallLevelTwentySixUnitMMMLinearSystemV1

/-! Consolidated chapter: SmallLevelTwentySixGermSources. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixGermSourceMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open Matrix SmallLevelTwentySixGrid

def sourceWord : Fin 32→List (Fin 4×Bool) :=
  ![[(0,false),(1,false),(0,false)],
    [(0,false),(1,false),(1,false)],
    [(0,false),(1,false),(2,false)],
    [(0,false),(1,true),(0,true)],
    [(0,false),(1,true),(2,false)],
    [(0,false),(2,false)],
    [(0,false),(2,false),(0,false)],
    [(0,true),(0,true),(1,true)],
    [(0,true),(1,false),(3,false)],
    [(0,true),(2,false),(2,false)],
    [(0,true),(2,true),(3,false)],
    [(1,false),(1,false),(2,false)],
    [(1,false),(2,false),(1,true)],
    [(1,false),(2,false),(2,false)],
    [(1,true),(0,false),(1,true)],
    [(1,true),(1,true),(1,true)],
    [(1,true),(1,true),(2,false)],
    [(2,false),(0,true)],
    [(2,false),(0,true),(0,true)],
    [(2,true),(0,false),(2,false)],
    [(2,true),(0,true)],
    [(2,true),(0,true),(0,true)],
    [(2,true),(1,false),(2,false)],
    [(2,true),(1,true)],
    [(2,true),(1,true),(1,true)],
    [(3,false),(0,false),(0,false)],
    [(3,false),(0,false),(1,false)],
    [(3,false),(0,false),(2,false)],
    [(3,false),(0,true),(1,false)],
    [(3,false),(1,false)],
    [(3,false),(1,false),(0,false)],
    [(3,false),(2,false),(1,true)]]

def sourceRaw : Fin 32→Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![27,28;26,27],
    !![53,1;52,1],
    !![28,-13;26,-12],
    !![25,-26;26,-27],
    !![76,-39;78,-40],
    !![24,-13;26,-14],
    !![24,11;26,12],
    !![53,-2;-26,1],
    !![26,-25;-26,26],
    !![223,-119;-208,111],
    !![13,-6;-26,13],
    !![2,-1;78,-38],
    !![28,-1;338,-12],
    !![15,-8;182,-97],
    !![25,-1;-624,25],
    !![1,0;-78,1],
    !![2,-1;-130,66],
    !![2,-3;-26,40],
    !![2,-5;-26,66],
    !![181,-98;338,-183],
    !![14,-13;26,-24],
    !![14,-27;26,-50],
    !![27,-13;52,-25],
    !![12,-1;26,-2],
    !![38,-1;78,-2],
    !![0,1;-26,-52],
    !![26,1;-702,-26],
    !![13,-7;-312,169],
    !![26,1;650,26],
    !![26,1;-26,0],
    !![26,27;-26,-26],
    !![195,-7;364,-13]]

def sourceMultiple : Fin 32→ℤ :=
  ![1,1,1,-1,-1,-1,-1,1,-1,2,-2,1,1,2,-1,1,1,1,1,-2,1,1,2,-1,-1,-1,-1,2,-1,-1,-1,2]

theorem source_primitive (i : Fin 32) :
    rawWord (sourceWord i)=sourceMultiple i • sourceRaw i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [sourceWord,sourceRaw,sourceMultiple,rawWord,rawLetter,rawBase,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem source_nonaffine (i : Fin 32) : sourceRaw i 1 0≠0 := by
  fin_cases i <;> decide

theorem source_det_pos (i : Fin 32) : 0<(sourceRaw i).det := by
  fin_cases i <;> decide

theorem source_coordinates (i : Fin 32) :
    (gridWord (sourceWord i)).val=
      (wordScale (sourceWord i)*(sourceMultiple i:ℝ)) • (sourceRaw i).map (Int.castRingHom ℝ) :=
  primitive_word_coordinates _ _ _ (source_primitive i)

#print axioms source_primitive
#print axioms source_coordinates

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSourceTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

def sourceRate (i : Fin 32) (r : ℝ) : ℝ :=
  ((sourceRaw i 1 0:ℝ)*r+(sourceRaw i 1 1:ℝ))^2/((sourceRaw i).det:ℝ)

def sourceDerivative (i : Fin 32) (r : ℝ) : ℝ :=
  (sourceRaw i 1 0:ℝ)*((sourceRaw i 1 0:ℝ)*r+(sourceRaw i 1 1:ℝ))/((sourceRaw i).det:ℝ)

def sourcePartner (i : Fin 32) (r : ℝ) : ℝ :=
  ((sourceRaw i 0 0:ℝ)*r+(sourceRaw i 0 1:ℝ))/
    ((sourceRaw i 1 0:ℝ)*r+(sourceRaw i 1 1:ℝ))

/-- All 32 source matrices have original-input Taylor expansions of every
order, with the same physical Fricke sign as the Ramanujan rows. -/
theorem source_taylor_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 26 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (i : Fin 32) (r : ℝ) (hr : (sourceRaw i 1 0:ℝ)*r+(sourceRaw i 1 1:ℝ)≠0) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f r s-gridWordSign (root 26 f 2) η (sourceWord i)*
          (sourceRate i r:ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*(sourceDerivative i r:ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f (sourcePartner i r) (s+(n:ℂ)))=error M s := by
  have hc : (gridWord (sourceWord i)).val=
      (wordScale (sourceWord i)*(sourceMultiple i:ℝ)) •
        !![(sourceRaw i 0 0:ℝ),(sourceRaw i 0 1:ℝ);
           (sourceRaw i 1 0:ℝ),(sourceRaw i 1 1:ℝ)] := by
    rw [source_coordinates]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have hd : (sourceRaw i 0 0:ℝ)*(sourceRaw i 1 1:ℝ)-
      (sourceRaw i 0 1:ℝ)*(sourceRaw i 1 0:ℝ)=((sourceRaw i).det:ℝ) := by
    simp only [det_fin_two,Int.cast_sub,Int.cast_mul]
  have hC : (sourceRaw i 1 0:ℝ)≠0 := by exact_mod_cast source_nonaffine i
  have hpos : 0<(sourceRaw i 0 0:ℝ)*(sourceRaw i 1 1:ℝ)-
      (sourceRaw i 0 1:ℝ)*(sourceRaw i 1 0:ℝ) := by
    rw [hd]
    exact_mod_cast source_det_pos i
  have hh:=raw_word_taylor_of_fricke m hf hη hW (sourceWord i)
    (sourceRaw i 0 0) (sourceRaw i 0 1) (sourceRaw i 1 0) (sourceRaw i 1 1)
    (wordScale (sourceWord i)*(sourceMultiple i:ℝ)) r hc hC hpos hr
  simpa only [hd,sourceRate,sourceDerivative,sourcePartner] using hh

#print axioms source_taylor_of_fricke
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermGeometryDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open Matrix SmallLevelAdditive

def gridGroupSource : Fin 235→Fin 32
  | 0 => 25
  | 1 => 15
  | 2 => 15
  | 3 => 15
  | 4 => 15
  | 5 => 15
  | 6 => 15
  | 7 => 15
  | 8 => 15
  | 9 => 15
  | 10 => 15
  | 11 => 15
  | 12 => 15
  | 13 => 15
  | 14 => 18
  | 15 => 17
  | 16 => 17
  | 17 => 16
  | 18 => 11
  | 19 => 23
  | 20 => 23
  | 21 => 23
  | 22 => 23
  | 23 => 23
  | 24 => 23
  | 25 => 23
  | 26 => 23
  | 27 => 23
  | 28 => 23
  | 29 => 23
  | 30 => 23
  | 31 => 23
  | 32 => 23
  | 33 => 23
  | 34 => 23
  | 35 => 23
  | 36 => 23
  | 37 => 23
  | 38 => 23
  | 39 => 23
  | 40 => 23
  | 41 => 23
  | 42 => 23
  | 43 => 23
  | 44 => 23
  | 45 => 23
  | 46 => 23
  | 47 => 23
  | 48 => 23
  | 49 => 23
  | 50 => 23
  | 51 => 23
  | 52 => 23
  | 53 => 23
  | 54 => 23
  | 55 => 23
  | 56 => 23
  | 57 => 23
  | 58 => 23
  | 59 => 23
  | 60 => 23
  | 61 => 23
  | 62 => 23
  | 63 => 23
  | 64 => 23
  | 65 => 23
  | 66 => 23
  | 67 => 23
  | 68 => 23
  | 69 => 23
  | 70 => 23
  | 71 => 27
  | 72 => 27
  | 73 => 27
  | 74 => 10
  | 75 => 10
  | 76 => 10
  | 77 => 10
  | 78 => 10
  | 79 => 10
  | 80 => 10
  | 81 => 10
  | 82 => 10
  | 83 => 10
  | 84 => 10
  | 85 => 10
  | 86 => 10
  | 87 => 10
  | 88 => 10
  | 89 => 10
  | 90 => 10
  | 91 => 10
  | 92 => 10
  | 93 => 10
  | 94 => 10
  | 95 => 10
  | 96 => 10
  | 97 => 10
  | 98 => 10
  | 99 => 10
  | 100 => 10
  | 101 => 10
  | 102 => 10
  | 103 => 10
  | 104 => 10
  | 105 => 10
  | 106 => 10
  | 107 => 10
  | 108 => 10
  | 109 => 10
  | 110 => 10
  | 111 => 10
  | 112 => 10
  | 113 => 10
  | 114 => 10
  | 115 => 10
  | 116 => 10
  | 117 => 10
  | 118 => 10
  | 119 => 10
  | 120 => 10
  | 121 => 10
  | 122 => 21
  | 123 => 20
  | 124 => 13
  | 125 => 13
  | 126 => 5
  | 127 => 5
  | 128 => 5
  | 129 => 5
  | 130 => 5
  | 131 => 5
  | 132 => 5
  | 133 => 5
  | 134 => 5
  | 135 => 5
  | 136 => 5
  | 137 => 5
  | 138 => 5
  | 139 => 5
  | 140 => 5
  | 141 => 5
  | 142 => 5
  | 143 => 5
  | 144 => 5
  | 145 => 5
  | 146 => 5
  | 147 => 5
  | 148 => 5
  | 149 => 5
  | 150 => 5
  | 151 => 5
  | 152 => 6
  | 153 => 6
  | 154 => 6
  | 155 => 3
  | 156 => 3
  | 157 => 14
  | 158 => 8
  | 159 => 8
  | 160 => 8
  | 161 => 8
  | 162 => 8
  | 163 => 8
  | 164 => 8
  | 165 => 26
  | 166 => 26
  | 167 => 29
  | 168 => 29
  | 169 => 29
  | 170 => 29
  | 171 => 29
  | 172 => 29
  | 173 => 29
  | 174 => 29
  | 175 => 29
  | 176 => 28
  | 177 => 30
  | 178 => 22
  | 179 => 22
  | 180 => 0
  | 181 => 2
  | 182 => 2
  | 183 => 2
  | 184 => 2
  | 185 => 2
  | 186 => 2
  | 187 => 2
  | 188 => 2
  | 189 => 12
  | 190 => 12
  | 191 => 12
  | 192 => 12
  | 193 => 12
  | 194 => 24
  | 195 => 24
  | 196 => 24
  | 197 => 24
  | 198 => 24
  | 199 => 24
  | 200 => 24
  | 201 => 24
  | 202 => 7
  | 203 => 7
  | 204 => 7
  | 205 => 1
  | 206 => 4
  | 207 => 4
  | 208 => 4
  | 209 => 4
  | 210 => 4
  | 211 => 4
  | 212 => 4
  | 213 => 4
  | 214 => 4
  | 215 => 4
  | 216 => 4
  | 217 => 4
  | 218 => 4
  | 219 => 4
  | 220 => 4
  | 221 => 19
  | 222 => 19
  | 223 => 19
  | 224 => 19
  | 225 => 31
  | 226 => 9
  | 227 => 9
  | 228 => 9
  | 229 => 9
  | 230 => 9
  | 231 => 9
  | 232 => 9
  | 233 => 9
  | _ => 9

def gridGroupIndex : Fin 235→Fin 780
  | 0 => 240
  | 1 => 5
  | 2 => 6
  | 3 => 8
  | 4 => 9
  | 5 => 11
  | 6 => 12
  | 7 => 14
  | 8 => 15
  | 9 => 20
  | 10 => 30
  | 11 => 35
  | 12 => 60
  | 13 => 110
  | 14 => 180
  | 15 => 300
  | 16 => 750
  | 17 => 397
  | 18 => 382
  | 19 => 0
  | 20 => 10
  | 21 => 15
  | 22 => 20
  | 23 => 24
  | 24 => 30
  | 25 => 35
  | 26 => 36
  | 27 => 40
  | 28 => 42
  | 29 => 45
  | 30 => 48
  | 31 => 50
  | 32 => 51
  | 33 => 52
  | 34 => 54
  | 35 => 55
  | 36 => 56
  | 37 => 57
  | 38 => 58
  | 39 => 59
  | 40 => 61
  | 41 => 62
  | 42 => 63
  | 43 => 64
  | 44 => 65
  | 45 => 66
  | 46 => 69
  | 47 => 70
  | 48 => 72
  | 49 => 75
  | 50 => 78
  | 51 => 80
  | 52 => 84
  | 53 => 90
  | 54 => 96
  | 55 => 100
  | 56 => 105
  | 57 => 110
  | 58 => 120
  | 59 => 132
  | 60 => 150
  | 61 => 160
  | 62 => 180
  | 63 => 210
  | 64 => 240
  | 65 => 260
  | 66 => 285
  | 67 => 360
  | 68 => 420
  | 69 => 510
  | 70 => 660
  | 71 => 260
  | 72 => 435
  | 73 => 585
  | 74 => 0
  | 75 => 65
  | 76 => 90
  | 77 => 130
  | 78 => 156
  | 79 => 165
  | 80 => 195
  | 81 => 210
  | 82 => 234
  | 83 => 240
  | 84 => 260
  | 85 => 273
  | 86 => 290
  | 87 => 300
  | 88 => 312
  | 89 => 315
  | 90 => 325
  | 91 => 330
  | 92 => 338
  | 93 => 340
  | 94 => 345
  | 95 => 354
  | 96 => 364
  | 97 => 365
  | 98 => 370
  | 99 => 372
  | 100 => 375
  | 101 => 377
  | 102 => 378
  | 103 => 380
  | 104 => 381
  | 105 => 384
  | 106 => 385
  | 107 => 386
  | 108 => 387
  | 109 => 388
  | 110 => 389
  | 111 => 391
  | 112 => 392
  | 113 => 393
  | 114 => 394
  | 115 => 395
  | 116 => 399
  | 117 => 402
  | 118 => 403
  | 119 => 408
  | 120 => 410
  | 121 => 415
  | 122 => 600
  | 123 => 719
  | 124 => 414
  | 125 => 417
  | 126 => 195
  | 127 => 220
  | 128 => 270
  | 129 => 320
  | 130 => 345
  | 131 => 411
  | 132 => 412
  | 133 => 419
  | 134 => 421
  | 135 => 424
  | 136 => 425
  | 137 => 428
  | 138 => 432
  | 139 => 438
  | 140 => 440
  | 141 => 445
  | 142 => 456
  | 143 => 460
  | 144 => 465
  | 145 => 470
  | 146 => 495
  | 147 => 510
  | 148 => 570
  | 149 => 600
  | 150 => 620
  | 151 => 720
  | 152 => 90
  | 153 => 240
  | 154 => 540
  | 155 => 510
  | 156 => 774
  | 157 => 25
  | 158 => 771
  | 159 => 772
  | 160 => 774
  | 161 => 776
  | 162 => 777
  | 163 => 778
  | 164 => 779
  | 165 => 0
  | 166 => 260
  | 167 => 1
  | 168 => 2
  | 169 => 3
  | 170 => 4
  | 171 => 13
  | 172 => 104
  | 173 => 117
  | 174 => 200
  | 175 => 225
  | 176 => 156
  | 177 => 120
  | 178 => 150
  | 179 => 374
  | 180 => 90
  | 181 => 358
  | 182 => 359
  | 183 => 361
  | 184 => 362
  | 185 => 363
  | 186 => 366
  | 187 => 368
  | 188 => 369
  | 189 => 20
  | 190 => 27
  | 191 => 28
  | 192 => 30
  | 193 => 45
  | 194 => 16
  | 195 => 18
  | 196 => 19
  | 197 => 21
  | 198 => 22
  | 199 => 25
  | 200 => 70
  | 201 => 220
  | 202 => 32
  | 203 => 33
  | 204 => 39
  | 205 => 210
  | 206 => 200
  | 207 => 300
  | 208 => 350
  | 209 => 380
  | 210 => 398
  | 211 => 401
  | 212 => 402
  | 213 => 404
  | 214 => 408
  | 215 => 410
  | 216 => 425
  | 217 => 440
  | 218 => 450
  | 219 => 500
  | 220 => 600
  | 221 => 405
  | 222 => 422
  | 223 => 423
  | 224 => 430
  | 225 => 26
  | 226 => 360
  | 227 => 405
  | 228 => 410
  | 229 => 414
  | 230 => 415
  | 231 => 416
  | 232 => 417
  | 233 => 420
  | _ => 435

def gridGroupPartner : Fin 235→ℤ
  | 0 => -13
  | 1 => 10
  | 2 => 15
  | 3 => 40
  | 4 => 90
  | 5 => -110
  | 6 => -60
  | 7 => -35
  | 8 => -30
  | 9 => -20
  | 10 => -15
  | 11 => -14
  | 12 => -12
  | 13 => -11
  | 14 => -59
  | 15 => -58
  | 16 => -56
  | 17 => -84
  | 18 => -80
  | 19 => 390
  | 20 => 396
  | 21 => 400
  | 22 => 405
  | 23 => 410
  | 24 => 420
  | 25 => 432
  | 26 => 435
  | 27 => 450
  | 28 => 460
  | 29 => 480
  | 30 => 510
  | 31 => 540
  | 32 => 560
  | 33 => 585
  | 34 => 660
  | 35 => 720
  | 36 => 810
  | 37 => 960
  | 38 => 1260
  | 39 => 2160
  | 40 => -1440
  | 41 => -540
  | 42 => -240
  | 43 => -90
  | 44 => 0
  | 45 => 60
  | 46 => 160
  | 47 => 180
  | 48 => 210
  | 49 => 240
  | 50 => 260
  | 51 => 270
  | 52 => 285
  | 53 => 300
  | 54 => 310
  | 55 => 315
  | 56 => 320
  | 57 => 324
  | 58 => 330
  | 59 => 335
  | 60 => 340
  | 61 => 342
  | 62 => 345
  | 63 => 348
  | 64 => 350
  | 65 => 351
  | 66 => 352
  | 67 => 354
  | 68 => 355
  | 69 => 356
  | 70 => 357
  | 71 => -32
  | 72 => -39
  | 73 => -33
  | 74 => -360
  | 75 => -354
  | 76 => -351
  | 77 => -345
  | 78 => -340
  | 79 => -338
  | 80 => -330
  | 81 => -325
  | 82 => -315
  | 83 => -312
  | 84 => -300
  | 85 => -290
  | 86 => -273
  | 87 => -260
  | 88 => -240
  | 89 => -234
  | 90 => -210
  | 91 => -195
  | 92 => -165
  | 93 => -156
  | 94 => -130
  | 95 => -65
  | 96 => 60
  | 97 => 78
  | 98 => 195
  | 99 => 260
  | 100 => 390
  | 101 => 510
  | 102 => 585
  | 103 => 780
  | 104 => 910
  | 105 => 1560
  | 106 => 1950
  | 107 => 2535
  | 108 => 3510
  | 109 => 5460
  | 110 => 11310
  | 111 => -12090
  | 112 => -6240
  | 113 => -4290
  | 114 => -3315
  | 115 => -2730
  | 116 => -1690
  | 117 => -1365
  | 118 => -1290
  | 119 => -1040
  | 120 => -975
  | 121 => -858
  | 122 => 422
  | 123 => 2220
  | 124 => 75
  | 125 => 50
  | 126 => 728
  | 127 => 729
  | 128 => 732
  | 129 => 738
  | 130 => 744
  | 131 => 920
  | 132 => 945
  | 133 => 2520
  | 134 => -1080
  | 135 => 270
  | 136 => 360
  | 137 => 495
  | 138 => 570
  | 139 => 620
  | 140 => 630
  | 141 => 648
  | 142 => 670
  | 143 => 675
  | 144 => 680
  | 145 => 684
  | 146 => 696
  | 147 => 700
  | 148 => 708
  | 149 => 710
  | 150 => 711
  | 151 => 714
  | 152 => 716
  | 153 => 717
  | 154 => 718
  | 155 => 753
  | 156 => 775
  | 157 => -31
  | 158 => 1820
  | 159 => 2145
  | 160 => 3120
  | 161 => 5070
  | 162 => 7020
  | 163 => 10920
  | 164 => 22620
  | 165 => -30
  | 166 => -29
  | 167 => -24180
  | 168 => -12480
  | 169 => -8580
  | 170 => -6630
  | 171 => -2580
  | 172 => -1005
  | 173 => -980
  | 174 => -897
  | 175 => -884
  | 176 => 31
  | 177 => -806
  | 178 => 406
  | 179 => 630
  | 180 => 809
  | 181 => 1740
  | 182 => 2640
  | 183 => -960
  | 184 => -60
  | 185 => 240
  | 186 => 540
  | 187 => 615
  | 188 => 640
  | 189 => 66
  | 190 => 80
  | 191 => 30
  | 192 => 60
  | 193 => 64
  | 194 => 430
  | 195 => 480
  | 196 => 580
  | 197 => 180
  | 198 => 280
  | 199 => 340
  | 200 => 376
  | 201 => 379
  | 202 => -2040
  | 203 => -1890
  | 204 => -1690
  | 205 => 794
  | 206 => 761
  | 207 => 762
  | 208 => 764
  | 209 => 770
  | 210 => 860
  | 211 => 560
  | 212 => 660
  | 213 => 710
  | 214 => 735
  | 215 => 740
  | 216 => 752
  | 217 => 755
  | 218 => 756
  | 219 => 758
  | 220 => 759
  | 221 => 418
  | 222 => 435
  | 223 => 410
  | 224 => 417
  | 225 => 450
  | 226 => -836
  | 227 => -835
  | 228 => -834
  | 229 => -830
  | 230 => -825
  | 231 => -780
  | 232 => -855
  | 233 => -840
  | _ => -837

def gridGroupTarget : Fin 235→Fin 780
  | 0 => 767
  | 1 => 10
  | 2 => 15
  | 3 => 40
  | 4 => 90
  | 5 => 670
  | 6 => 720
  | 7 => 745
  | 8 => 750
  | 9 => 760
  | 10 => 765
  | 11 => 766
  | 12 => 768
  | 13 => 769
  | 14 => 721
  | 15 => 722
  | 16 => 724
  | 17 => 696
  | 18 => 700
  | 19 => 390
  | 20 => 396
  | 21 => 400
  | 22 => 405
  | 23 => 410
  | 24 => 420
  | 25 => 432
  | 26 => 435
  | 27 => 450
  | 28 => 460
  | 29 => 480
  | 30 => 510
  | 31 => 540
  | 32 => 560
  | 33 => 585
  | 34 => 660
  | 35 => 720
  | 36 => 30
  | 37 => 180
  | 38 => 480
  | 39 => 600
  | 40 => 120
  | 41 => 240
  | 42 => 540
  | 43 => 690
  | 44 => 0
  | 45 => 60
  | 46 => 160
  | 47 => 180
  | 48 => 210
  | 49 => 240
  | 50 => 260
  | 51 => 270
  | 52 => 285
  | 53 => 300
  | 54 => 310
  | 55 => 315
  | 56 => 320
  | 57 => 324
  | 58 => 330
  | 59 => 335
  | 60 => 340
  | 61 => 342
  | 62 => 345
  | 63 => 348
  | 64 => 350
  | 65 => 351
  | 66 => 352
  | 67 => 354
  | 68 => 355
  | 69 => 356
  | 70 => 357
  | 71 => 748
  | 72 => 741
  | 73 => 747
  | 74 => 420
  | 75 => 426
  | 76 => 429
  | 77 => 435
  | 78 => 440
  | 79 => 442
  | 80 => 450
  | 81 => 455
  | 82 => 465
  | 83 => 468
  | 84 => 480
  | 85 => 490
  | 86 => 507
  | 87 => 520
  | 88 => 540
  | 89 => 546
  | 90 => 570
  | 91 => 585
  | 92 => 615
  | 93 => 624
  | 94 => 650
  | 95 => 715
  | 96 => 60
  | 97 => 78
  | 98 => 195
  | 99 => 260
  | 100 => 390
  | 101 => 510
  | 102 => 585
  | 103 => 0
  | 104 => 130
  | 105 => 0
  | 106 => 390
  | 107 => 195
  | 108 => 390
  | 109 => 0
  | 110 => 390
  | 111 => 390
  | 112 => 0
  | 113 => 390
  | 114 => 585
  | 115 => 390
  | 116 => 650
  | 117 => 195
  | 118 => 270
  | 119 => 520
  | 120 => 585
  | 121 => 702
  | 122 => 422
  | 123 => 660
  | 124 => 75
  | 125 => 50
  | 126 => 728
  | 127 => 729
  | 128 => 732
  | 129 => 738
  | 130 => 744
  | 131 => 140
  | 132 => 165
  | 133 => 180
  | 134 => 480
  | 135 => 270
  | 136 => 360
  | 137 => 495
  | 138 => 570
  | 139 => 620
  | 140 => 630
  | 141 => 648
  | 142 => 670
  | 143 => 675
  | 144 => 680
  | 145 => 684
  | 146 => 696
  | 147 => 700
  | 148 => 708
  | 149 => 710
  | 150 => 711
  | 151 => 714
  | 152 => 716
  | 153 => 717
  | 154 => 718
  | 155 => 753
  | 156 => 775
  | 157 => 749
  | 158 => 260
  | 159 => 585
  | 160 => 0
  | 161 => 390
  | 162 => 0
  | 163 => 0
  | 164 => 0
  | 165 => 750
  | 166 => 751
  | 167 => 0
  | 168 => 0
  | 169 => 0
  | 170 => 390
  | 171 => 540
  | 172 => 555
  | 173 => 580
  | 174 => 663
  | 175 => 676
  | 176 => 31
  | 177 => 754
  | 178 => 406
  | 179 => 630
  | 180 => 29
  | 181 => 180
  | 182 => 300
  | 183 => 600
  | 184 => 720
  | 185 => 240
  | 186 => 540
  | 187 => 615
  | 188 => 640
  | 189 => 66
  | 190 => 80
  | 191 => 30
  | 192 => 60
  | 193 => 64
  | 194 => 430
  | 195 => 480
  | 196 => 580
  | 197 => 180
  | 198 => 280
  | 199 => 340
  | 200 => 376
  | 201 => 379
  | 202 => 300
  | 203 => 450
  | 204 => 650
  | 205 => 14
  | 206 => 761
  | 207 => 762
  | 208 => 764
  | 209 => 770
  | 210 => 80
  | 211 => 560
  | 212 => 660
  | 213 => 710
  | 214 => 735
  | 215 => 740
  | 216 => 752
  | 217 => 755
  | 218 => 756
  | 219 => 758
  | 220 => 759
  | 221 => 418
  | 222 => 435
  | 223 => 410
  | 224 => 417
  | 225 => 450
  | 226 => 724
  | 227 => 725
  | 228 => 726
  | 229 => 730
  | 230 => 735
  | 231 => 0
  | 232 => 705
  | 233 => 720
  | _ => 723

def gridGroupRate : Fin 235→ℚ
  | 0 => (1800/13)
  | 1 => (1/4)
  | 2 => (4/25)
  | 3 => (1/25)
  | 4 => (1/100)
  | 5 => (1/100)
  | 6 => (1/25)
  | 7 => (4/25)
  | 8 => (1/4)
  | 9 => 1
  | 10 => 4
  | 11 => (25/4)
  | 12 => 25
  | 13 => 100
  | 14 => 1800
  | 15 => 450
  | 16 => (225/2)
  | 17 => (1/72)
  | 18 => (1/50)
  | 19 => 2
  | 20 => (25/18)
  | 21 => (9/8)
  | 22 => (8/9)
  | 23 => (18/25)
  | 24 => (1/2)
  | 25 => (25/72)
  | 26 => (8/25)
  | 27 => (2/9)
  | 28 => (9/50)
  | 29 => (1/8)
  | 30 => (2/25)
  | 31 => (1/18)
  | 32 => (9/200)
  | 33 => (8/225)
  | 34 => (1/50)
  | 35 => (1/72)
  | 36 => (2/225)
  | 37 => (1/200)
  | 38 => (1/450)
  | 39 => (1/1800)
  | 40 => (1/1800)
  | 41 => (1/450)
  | 42 => (1/200)
  | 43 => (2/225)
  | 44 => (1/72)
  | 45 => (1/50)
  | 46 => (9/200)
  | 47 => (1/18)
  | 48 => (2/25)
  | 49 => (1/8)
  | 50 => (9/50)
  | 51 => (2/9)
  | 52 => (8/25)
  | 53 => (1/2)
  | 54 => (18/25)
  | 55 => (8/9)
  | 56 => (9/8)
  | 57 => (25/18)
  | 58 => 2
  | 59 => (72/25)
  | 60 => (9/2)
  | 61 => (50/9)
  | 62 => 8
  | 63 => (25/2)
  | 64 => 18
  | 65 => (200/9)
  | 66 => (225/8)
  | 67 => 50
  | 68 => 72
  | 69 => (225/2)
  | 70 => 200
  | 71 => 325
  | 72 => (25/13)
  | 73 => 325
  | 74 => 13
  | 75 => (325/36)
  | 76 => (100/13)
  | 77 => (52/9)
  | 78 => (117/25)
  | 79 => (225/52)
  | 80 => (13/4)
  | 81 => (36/13)
  | 82 => (52/25)
  | 83 => (25/13)
  | 84 => (13/9)
  | 85 => (117/100)
  | 86 => (100/117)
  | 87 => (9/13)
  | 88 => (13/25)
  | 89 => (25/52)
  | 90 => (13/36)
  | 91 => (4/13)
  | 92 => (52/225)
  | 93 => (25/117)
  | 94 => (9/52)
  | 95 => (36/325)
  | 96 => (13/225)
  | 97 => (25/468)
  | 98 => (4/117)
  | 99 => (9/325)
  | 100 => (1/52)
  | 101 => (13/900)
  | 102 => (4/325)
  | 103 => (1/117)
  | 104 => (9/1300)
  | 105 => (1/325)
  | 106 => (1/468)
  | 107 => (4/2925)
  | 108 => (1/1300)
  | 109 => (1/2925)
  | 110 => (1/11700)
  | 111 => (1/11700)
  | 112 => (1/2925)
  | 113 => (1/1300)
  | 114 => (4/2925)
  | 115 => (1/468)
  | 116 => (9/1300)
  | 117 => (4/325)
  | 118 => (13/900)
  | 119 => (9/325)
  | 120 => (4/117)
  | 121 => (25/468)
  | 122 => 450
  | 123 => (1/1800)
  | 124 => (4/25)
  | 125 => (9/100)
  | 126 => (225/8)
  | 127 => (200/9)
  | 128 => (25/2)
  | 129 => (50/9)
  | 130 => (25/8)
  | 131 => (9/200)
  | 132 => (8/225)
  | 133 => (1/1800)
  | 134 => (1/1800)
  | 135 => (2/225)
  | 136 => (1/72)
  | 137 => (8/225)
  | 138 => (2/25)
  | 139 => (9/50)
  | 140 => (2/9)
  | 141 => (25/72)
  | 142 => (18/25)
  | 143 => (8/9)
  | 144 => (9/8)
  | 145 => (25/18)
  | 146 => (25/8)
  | 147 => (9/2)
  | 148 => (25/2)
  | 149 => 18
  | 150 => (200/9)
  | 151 => 50
  | 152 => (225/2)
  | 153 => 200
  | 154 => 450
  | 155 => 100
  | 156 => (36/25)
  | 157 => 25
  | 158 => (9/2600)
  | 159 => (8/2925)
  | 160 => (1/650)
  | 161 => (2/2925)
  | 162 => (1/2600)
  | 163 => (1/5850)
  | 164 => (1/23400)
  | 165 => 26
  | 166 => 2600
  | 167 => (1/23400)
  | 168 => (1/5850)
  | 169 => (1/2600)
  | 170 => (2/2925)
  | 171 => (13/1800)
  | 172 => (104/225)
  | 173 => (117/200)
  | 174 => (200/117)
  | 175 => (225/104)
  | 176 => 936
  | 177 => (450/13)
  | 178 => 225
  | 179 => (1/225)
  | 180 => 900
  | 181 => (1/450)
  | 182 => (1/1800)
  | 183 => (1/1800)
  | 184 => (1/450)
  | 185 => (1/200)
  | 186 => (1/50)
  | 187 => (8/225)
  | 188 => (9/200)
  | 189 => (50/9)
  | 190 => (9/200)
  | 191 => (2/225)
  | 192 => (1/2)
  | 193 => (225/8)
  | 194 => (2/25)
  | 195 => (1/50)
  | 196 => (1/200)
  | 197 => (1/200)
  | 198 => (1/50)
  | 199 => (1/8)
  | 200 => (25/2)
  | 201 => 200
  | 202 => (1/225)
  | 203 => (1/100)
  | 204 => (9/100)
  | 205 => 225
  | 206 => 200
  | 207 => 50
  | 208 => (25/2)
  | 209 => 2
  | 210 => (1/50)
  | 211 => (1/200)
  | 212 => (1/50)
  | 213 => (2/25)
  | 214 => (8/25)
  | 215 => (1/2)
  | 216 => (25/8)
  | 217 => 8
  | 218 => (25/2)
  | 219 => 50
  | 220 => 200
  | 221 => (225/4)
  | 222 => (4/225)
  | 223 => (9/100)
  | 224 => (100/9)
  | 225 => (13/225)
  | 226 => 225
  | 227 => 9
  | 228 => (25/9)
  | 229 => (9/25)
  | 230 => (1/9)
  | 231 => (1/225)
  | 232 => (1/25)
  | 233 => 1
  | _ => 25

def gridGroupDerivative : Fin 235→ℚ
  | 0 => 60
  | 1 => -39
  | 2 => (-156/5)
  | 3 => (-78/5)
  | 4 => (-39/5)
  | 5 => (39/5)
  | 6 => (78/5)
  | 7 => (156/5)
  | 8 => 39
  | 9 => 78
  | 10 => 156
  | 11 => 195
  | 12 => 390
  | 13 => 780
  | 14 => -780
  | 15 => -390
  | 16 => -195
  | 17 => (65/6)
  | 18 => (39/5)
  | 19 => -26
  | 20 => (-65/3)
  | 21 => (-39/2)
  | 22 => (-52/3)
  | 23 => (-78/5)
  | 24 => -13
  | 25 => (-65/6)
  | 26 => (-52/5)
  | 27 => (-26/3)
  | 28 => (-39/5)
  | 29 => (-13/2)
  | 30 => (-26/5)
  | 31 => (-13/3)
  | 32 => (-39/10)
  | 33 => (-52/15)
  | 34 => (-13/5)
  | 35 => (-13/6)
  | 36 => (-26/15)
  | 37 => (-13/10)
  | 38 => (-13/15)
  | 39 => (-13/30)
  | 40 => (13/30)
  | 41 => (13/15)
  | 42 => (13/10)
  | 43 => (26/15)
  | 44 => (13/6)
  | 45 => (13/5)
  | 46 => (39/10)
  | 47 => (13/3)
  | 48 => (26/5)
  | 49 => (13/2)
  | 50 => (39/5)
  | 51 => (26/3)
  | 52 => (52/5)
  | 53 => 13
  | 54 => (78/5)
  | 55 => (52/3)
  | 56 => (39/2)
  | 57 => (65/3)
  | 58 => 26
  | 59 => (156/5)
  | 60 => 39
  | 61 => (130/3)
  | 62 => 52
  | 63 => 65
  | 64 => 78
  | 65 => (260/3)
  | 66 => (195/2)
  | 67 => 130
  | 68 => 156
  | 69 => 195
  | 70 => 260
  | 71 => -1560
  | 72 => 120
  | 73 => 1560
  | 74 => -26
  | 75 => (-65/3)
  | 76 => -20
  | 77 => (-52/3)
  | 78 => (-78/5)
  | 79 => -15
  | 80 => -13
  | 81 => -12
  | 82 => (-52/5)
  | 83 => -10
  | 84 => (-26/3)
  | 85 => (-39/5)
  | 86 => (-20/3)
  | 87 => -6
  | 88 => (-26/5)
  | 89 => -5
  | 90 => (-13/3)
  | 91 => -4
  | 92 => (-52/15)
  | 93 => (-10/3)
  | 94 => -3
  | 95 => (-12/5)
  | 96 => (-26/15)
  | 97 => (-5/3)
  | 98 => (-4/3)
  | 99 => (-6/5)
  | 100 => -1
  | 101 => (-13/15)
  | 102 => (-4/5)
  | 103 => (-2/3)
  | 104 => (-3/5)
  | 105 => (-2/5)
  | 106 => (-1/3)
  | 107 => (-4/15)
  | 108 => (-1/5)
  | 109 => (-2/15)
  | 110 => (-1/15)
  | 111 => (1/15)
  | 112 => (2/15)
  | 113 => (1/5)
  | 114 => (4/15)
  | 115 => (1/3)
  | 116 => (3/5)
  | 117 => (4/5)
  | 118 => (13/15)
  | 119 => (6/5)
  | 120 => (4/3)
  | 121 => (5/3)
  | 122 => -390
  | 123 => (-13/30)
  | 124 => (-364/5)
  | 125 => (273/5)
  | 126 => (-195/2)
  | 127 => (-260/3)
  | 128 => -65
  | 129 => (-130/3)
  | 130 => (-65/2)
  | 131 => (-39/10)
  | 132 => (-52/15)
  | 133 => (-13/30)
  | 134 => (13/30)
  | 135 => (26/15)
  | 136 => (13/6)
  | 137 => (52/15)
  | 138 => (26/5)
  | 139 => (39/5)
  | 140 => (26/3)
  | 141 => (65/6)
  | 142 => (78/5)
  | 143 => (52/3)
  | 144 => (39/2)
  | 145 => (65/3)
  | 146 => (65/2)
  | 147 => 39
  | 148 => 65
  | 149 => 78
  | 150 => (260/3)
  | 151 => 130
  | 152 => 195
  | 153 => 260
  | 154 => 390
  | 155 => -260
  | 156 => (-156/5)
  | 157 => -3120
  | 158 => (-3/10)
  | 159 => (-4/15)
  | 160 => (-1/5)
  | 161 => (-2/15)
  | 162 => (-1/10)
  | 163 => (-1/15)
  | 164 => (-1/30)
  | 165 => 702
  | 166 => 7020
  | 167 => (1/30)
  | 168 => (1/15)
  | 169 => (1/10)
  | 170 => (2/15)
  | 171 => (13/30)
  | 172 => (52/15)
  | 173 => (39/10)
  | 174 => (20/3)
  | 175 => (15/2)
  | 176 => 3900
  | 177 => 30
  | 178 => -780
  | 179 => (-52/15)
  | 180 => 780
  | 181 => (-13/15)
  | 182 => (-13/30)
  | 183 => (13/30)
  | 184 => (13/15)
  | 185 => (13/10)
  | 186 => (13/5)
  | 187 => (52/15)
  | 188 => (39/10)
  | 189 => (-1690/3)
  | 190 => (-507/10)
  | 191 => (338/15)
  | 192 => 169
  | 193 => (2535/2)
  | 194 => (-78/5)
  | 195 => (-39/5)
  | 196 => (-39/10)
  | 197 => (39/10)
  | 198 => (39/5)
  | 199 => (39/2)
  | 200 => 195
  | 201 => 780
  | 202 => (26/15)
  | 203 => (13/5)
  | 204 => (39/5)
  | 205 => 780
  | 206 => -780
  | 207 => -390
  | 208 => -195
  | 209 => -78
  | 210 => (-39/5)
  | 211 => (39/10)
  | 212 => (39/5)
  | 213 => (78/5)
  | 214 => (156/5)
  | 215 => 39
  | 216 => (195/2)
  | 217 => 156
  | 218 => 195
  | 219 => 390
  | 220 => 780
  | 221 => -2535
  | 222 => (-676/15)
  | 223 => (507/5)
  | 224 => (3380/3)
  | 225 => (-364/15)
  | 226 => -3120
  | 227 => -624
  | 228 => (-1040/3)
  | 229 => (-624/5)
  | 230 => (-208/3)
  | 231 => (-208/15)
  | 232 => (208/5)
  | 233 => 208
  | _ => 1040

def GridGroupGeometry (i : Fin 235) : Prop :=
    (sourceRaw (gridGroupSource i) 1 0:ℝ)*((gridGroupIndex i:ℕ):ℝ)/780+
      (sourceRaw (gridGroupSource i) 1 1:ℝ)≠0 ∧
    sourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780)=
      (gridGroupPartner i:ℝ)/780 ∧
    sourceRate (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780)=(gridGroupRate i:ℝ) ∧
    sourceDerivative (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780)=(gridGroupDerivative i:ℝ)

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermGeometryBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGermSources
open Matrix SmallLevelAdditive

theorem gridGroup_geometry_0 : GridGroupGeometry 0 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 0=(25:Fin 32) from rfl,
    show gridGroupIndex 0=(240:Fin 780) from rfl,
    show gridGroupPartner 0=(-13:ℤ) from rfl,
    show gridGroupRate 0=((1800/13):ℚ) from rfl,
    show gridGroupDerivative 0=(60:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![0,1;-26,-52] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_1 : GridGroupGeometry 1 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 1=(15:Fin 32) from rfl,
    show gridGroupIndex 1=(5:Fin 780) from rfl,
    show gridGroupPartner 1=(10:ℤ) from rfl,
    show gridGroupRate 1=((1/4):ℚ) from rfl,
    show gridGroupDerivative 1=(-39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_2 : GridGroupGeometry 2 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 2=(15:Fin 32) from rfl,
    show gridGroupIndex 2=(6:Fin 780) from rfl,
    show gridGroupPartner 2=(15:ℤ) from rfl,
    show gridGroupRate 2=((4/25):ℚ) from rfl,
    show gridGroupDerivative 2=((-156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_3 : GridGroupGeometry 3 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 3=(15:Fin 32) from rfl,
    show gridGroupIndex 3=(8:Fin 780) from rfl,
    show gridGroupPartner 3=(40:ℤ) from rfl,
    show gridGroupRate 3=((1/25):ℚ) from rfl,
    show gridGroupDerivative 3=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_4 : GridGroupGeometry 4 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 4=(15:Fin 32) from rfl,
    show gridGroupIndex 4=(9:Fin 780) from rfl,
    show gridGroupPartner 4=(90:ℤ) from rfl,
    show gridGroupRate 4=((1/100):ℚ) from rfl,
    show gridGroupDerivative 4=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_5 : GridGroupGeometry 5 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 5=(15:Fin 32) from rfl,
    show gridGroupIndex 5=(11:Fin 780) from rfl,
    show gridGroupPartner 5=(-110:ℤ) from rfl,
    show gridGroupRate 5=((1/100):ℚ) from rfl,
    show gridGroupDerivative 5=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_6 : GridGroupGeometry 6 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 6=(15:Fin 32) from rfl,
    show gridGroupIndex 6=(12:Fin 780) from rfl,
    show gridGroupPartner 6=(-60:ℤ) from rfl,
    show gridGroupRate 6=((1/25):ℚ) from rfl,
    show gridGroupDerivative 6=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_7 : GridGroupGeometry 7 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 7=(15:Fin 32) from rfl,
    show gridGroupIndex 7=(14:Fin 780) from rfl,
    show gridGroupPartner 7=(-35:ℤ) from rfl,
    show gridGroupRate 7=((4/25):ℚ) from rfl,
    show gridGroupDerivative 7=((156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_8 : GridGroupGeometry 8 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 8=(15:Fin 32) from rfl,
    show gridGroupIndex 8=(15:Fin 780) from rfl,
    show gridGroupPartner 8=(-30:ℤ) from rfl,
    show gridGroupRate 8=((1/4):ℚ) from rfl,
    show gridGroupDerivative 8=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_9 : GridGroupGeometry 9 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 9=(15:Fin 32) from rfl,
    show gridGroupIndex 9=(20:Fin 780) from rfl,
    show gridGroupPartner 9=(-20:ℤ) from rfl,
    show gridGroupRate 9=(1:ℚ) from rfl,
    show gridGroupDerivative 9=(78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_10 : GridGroupGeometry 10 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 10=(15:Fin 32) from rfl,
    show gridGroupIndex 10=(30:Fin 780) from rfl,
    show gridGroupPartner 10=(-15:ℤ) from rfl,
    show gridGroupRate 10=(4:ℚ) from rfl,
    show gridGroupDerivative 10=(156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_11 : GridGroupGeometry 11 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 11=(15:Fin 32) from rfl,
    show gridGroupIndex 11=(35:Fin 780) from rfl,
    show gridGroupPartner 11=(-14:ℤ) from rfl,
    show gridGroupRate 11=((25/4):ℚ) from rfl,
    show gridGroupDerivative 11=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_12 : GridGroupGeometry 12 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 12=(15:Fin 32) from rfl,
    show gridGroupIndex 12=(60:Fin 780) from rfl,
    show gridGroupPartner 12=(-12:ℤ) from rfl,
    show gridGroupRate 12=(25:ℚ) from rfl,
    show gridGroupDerivative 12=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_13 : GridGroupGeometry 13 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 13=(15:Fin 32) from rfl,
    show gridGroupIndex 13=(110:Fin 780) from rfl,
    show gridGroupPartner 13=(-11:ℤ) from rfl,
    show gridGroupRate 13=(100:ℚ) from rfl,
    show gridGroupDerivative 13=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_14 : GridGroupGeometry 14 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 14=(18:Fin 32) from rfl,
    show gridGroupIndex 14=(180:Fin 780) from rfl,
    show gridGroupPartner 14=(-59:ℤ) from rfl,
    show gridGroupRate 14=(1800:ℚ) from rfl,
    show gridGroupDerivative 14=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 18=!![2,-5;-26,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_15 : GridGroupGeometry 15 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 15=(17:Fin 32) from rfl,
    show gridGroupIndex 15=(300:Fin 780) from rfl,
    show gridGroupPartner 15=(-58:ℤ) from rfl,
    show gridGroupRate 15=(450:ℚ) from rfl,
    show gridGroupDerivative 15=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 17=!![2,-3;-26,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_16 : GridGroupGeometry 16 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 16=(17:Fin 32) from rfl,
    show gridGroupIndex 16=(750:Fin 780) from rfl,
    show gridGroupPartner 16=(-56:ℤ) from rfl,
    show gridGroupRate 16=((225/2):ℚ) from rfl,
    show gridGroupDerivative 16=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 17=!![2,-3;-26,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_17 : GridGroupGeometry 17 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 17=(16:Fin 32) from rfl,
    show gridGroupIndex 17=(397:Fin 780) from rfl,
    show gridGroupPartner 17=(-84:ℤ) from rfl,
    show gridGroupRate 17=((1/72):ℚ) from rfl,
    show gridGroupDerivative 17=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 16=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_18 : GridGroupGeometry 18 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 18=(11:Fin 32) from rfl,
    show gridGroupIndex 18=(382:Fin 780) from rfl,
    show gridGroupPartner 18=(-80:ℤ) from rfl,
    show gridGroupRate 18=((1/50):ℚ) from rfl,
    show gridGroupDerivative 18=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 11=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_19 : GridGroupGeometry 19 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 19=(23:Fin 32) from rfl,
    show gridGroupIndex 19=(0:Fin 780) from rfl,
    show gridGroupPartner 19=(390:ℤ) from rfl,
    show gridGroupRate 19=(2:ℚ) from rfl,
    show gridGroupDerivative 19=(-26:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_20 : GridGroupGeometry 20 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 20=(23:Fin 32) from rfl,
    show gridGroupIndex 20=(10:Fin 780) from rfl,
    show gridGroupPartner 20=(396:ℤ) from rfl,
    show gridGroupRate 20=((25/18):ℚ) from rfl,
    show gridGroupDerivative 20=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_21 : GridGroupGeometry 21 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 21=(23:Fin 32) from rfl,
    show gridGroupIndex 21=(15:Fin 780) from rfl,
    show gridGroupPartner 21=(400:ℤ) from rfl,
    show gridGroupRate 21=((9/8):ℚ) from rfl,
    show gridGroupDerivative 21=((-39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_22 : GridGroupGeometry 22 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 22=(23:Fin 32) from rfl,
    show gridGroupIndex 22=(20:Fin 780) from rfl,
    show gridGroupPartner 22=(405:ℤ) from rfl,
    show gridGroupRate 22=((8/9):ℚ) from rfl,
    show gridGroupDerivative 22=((-52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_23 : GridGroupGeometry 23 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 23=(23:Fin 32) from rfl,
    show gridGroupIndex 23=(24:Fin 780) from rfl,
    show gridGroupPartner 23=(410:ℤ) from rfl,
    show gridGroupRate 23=((18/25):ℚ) from rfl,
    show gridGroupDerivative 23=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_24 : GridGroupGeometry 24 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 24=(23:Fin 32) from rfl,
    show gridGroupIndex 24=(30:Fin 780) from rfl,
    show gridGroupPartner 24=(420:ℤ) from rfl,
    show gridGroupRate 24=((1/2):ℚ) from rfl,
    show gridGroupDerivative 24=(-13:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_25 : GridGroupGeometry 25 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 25=(23:Fin 32) from rfl,
    show gridGroupIndex 25=(35:Fin 780) from rfl,
    show gridGroupPartner 25=(432:ℤ) from rfl,
    show gridGroupRate 25=((25/72):ℚ) from rfl,
    show gridGroupDerivative 25=((-65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_26 : GridGroupGeometry 26 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 26=(23:Fin 32) from rfl,
    show gridGroupIndex 26=(36:Fin 780) from rfl,
    show gridGroupPartner 26=(435:ℤ) from rfl,
    show gridGroupRate 26=((8/25):ℚ) from rfl,
    show gridGroupDerivative 26=((-52/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_27 : GridGroupGeometry 27 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 27=(23:Fin 32) from rfl,
    show gridGroupIndex 27=(40:Fin 780) from rfl,
    show gridGroupPartner 27=(450:ℤ) from rfl,
    show gridGroupRate 27=((2/9):ℚ) from rfl,
    show gridGroupDerivative 27=((-26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_28 : GridGroupGeometry 28 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 28=(23:Fin 32) from rfl,
    show gridGroupIndex 28=(42:Fin 780) from rfl,
    show gridGroupPartner 28=(460:ℤ) from rfl,
    show gridGroupRate 28=((9/50):ℚ) from rfl,
    show gridGroupDerivative 28=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_29 : GridGroupGeometry 29 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 29=(23:Fin 32) from rfl,
    show gridGroupIndex 29=(45:Fin 780) from rfl,
    show gridGroupPartner 29=(480:ℤ) from rfl,
    show gridGroupRate 29=((1/8):ℚ) from rfl,
    show gridGroupDerivative 29=((-13/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_30 : GridGroupGeometry 30 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 30=(23:Fin 32) from rfl,
    show gridGroupIndex 30=(48:Fin 780) from rfl,
    show gridGroupPartner 30=(510:ℤ) from rfl,
    show gridGroupRate 30=((2/25):ℚ) from rfl,
    show gridGroupDerivative 30=((-26/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_31 : GridGroupGeometry 31 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 31=(23:Fin 32) from rfl,
    show gridGroupIndex 31=(50:Fin 780) from rfl,
    show gridGroupPartner 31=(540:ℤ) from rfl,
    show gridGroupRate 31=((1/18):ℚ) from rfl,
    show gridGroupDerivative 31=((-13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_32 : GridGroupGeometry 32 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 32=(23:Fin 32) from rfl,
    show gridGroupIndex 32=(51:Fin 780) from rfl,
    show gridGroupPartner 32=(560:ℤ) from rfl,
    show gridGroupRate 32=((9/200):ℚ) from rfl,
    show gridGroupDerivative 32=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_33 : GridGroupGeometry 33 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 33=(23:Fin 32) from rfl,
    show gridGroupIndex 33=(52:Fin 780) from rfl,
    show gridGroupPartner 33=(585:ℤ) from rfl,
    show gridGroupRate 33=((8/225):ℚ) from rfl,
    show gridGroupDerivative 33=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_34 : GridGroupGeometry 34 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 34=(23:Fin 32) from rfl,
    show gridGroupIndex 34=(54:Fin 780) from rfl,
    show gridGroupPartner 34=(660:ℤ) from rfl,
    show gridGroupRate 34=((1/50):ℚ) from rfl,
    show gridGroupDerivative 34=((-13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_35 : GridGroupGeometry 35 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 35=(23:Fin 32) from rfl,
    show gridGroupIndex 35=(55:Fin 780) from rfl,
    show gridGroupPartner 35=(720:ℤ) from rfl,
    show gridGroupRate 35=((1/72):ℚ) from rfl,
    show gridGroupDerivative 35=((-13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_36 : GridGroupGeometry 36 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 36=(23:Fin 32) from rfl,
    show gridGroupIndex 36=(56:Fin 780) from rfl,
    show gridGroupPartner 36=(810:ℤ) from rfl,
    show gridGroupRate 36=((2/225):ℚ) from rfl,
    show gridGroupDerivative 36=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_37 : GridGroupGeometry 37 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 37=(23:Fin 32) from rfl,
    show gridGroupIndex 37=(57:Fin 780) from rfl,
    show gridGroupPartner 37=(960:ℤ) from rfl,
    show gridGroupRate 37=((1/200):ℚ) from rfl,
    show gridGroupDerivative 37=((-13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_38 : GridGroupGeometry 38 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 38=(23:Fin 32) from rfl,
    show gridGroupIndex 38=(58:Fin 780) from rfl,
    show gridGroupPartner 38=(1260:ℤ) from rfl,
    show gridGroupRate 38=((1/450):ℚ) from rfl,
    show gridGroupDerivative 38=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_39 : GridGroupGeometry 39 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 39=(23:Fin 32) from rfl,
    show gridGroupIndex 39=(59:Fin 780) from rfl,
    show gridGroupPartner 39=(2160:ℤ) from rfl,
    show gridGroupRate 39=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 39=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_40 : GridGroupGeometry 40 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 40=(23:Fin 32) from rfl,
    show gridGroupIndex 40=(61:Fin 780) from rfl,
    show gridGroupPartner 40=(-1440:ℤ) from rfl,
    show gridGroupRate 40=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 40=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_41 : GridGroupGeometry 41 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 41=(23:Fin 32) from rfl,
    show gridGroupIndex 41=(62:Fin 780) from rfl,
    show gridGroupPartner 41=(-540:ℤ) from rfl,
    show gridGroupRate 41=((1/450):ℚ) from rfl,
    show gridGroupDerivative 41=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_42 : GridGroupGeometry 42 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 42=(23:Fin 32) from rfl,
    show gridGroupIndex 42=(63:Fin 780) from rfl,
    show gridGroupPartner 42=(-240:ℤ) from rfl,
    show gridGroupRate 42=((1/200):ℚ) from rfl,
    show gridGroupDerivative 42=((13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_43 : GridGroupGeometry 43 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 43=(23:Fin 32) from rfl,
    show gridGroupIndex 43=(64:Fin 780) from rfl,
    show gridGroupPartner 43=(-90:ℤ) from rfl,
    show gridGroupRate 43=((2/225):ℚ) from rfl,
    show gridGroupDerivative 43=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_44 : GridGroupGeometry 44 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 44=(23:Fin 32) from rfl,
    show gridGroupIndex 44=(65:Fin 780) from rfl,
    show gridGroupPartner 44=(0:ℤ) from rfl,
    show gridGroupRate 44=((1/72):ℚ) from rfl,
    show gridGroupDerivative 44=((13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_45 : GridGroupGeometry 45 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 45=(23:Fin 32) from rfl,
    show gridGroupIndex 45=(66:Fin 780) from rfl,
    show gridGroupPartner 45=(60:ℤ) from rfl,
    show gridGroupRate 45=((1/50):ℚ) from rfl,
    show gridGroupDerivative 45=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_46 : GridGroupGeometry 46 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 46=(23:Fin 32) from rfl,
    show gridGroupIndex 46=(69:Fin 780) from rfl,
    show gridGroupPartner 46=(160:ℤ) from rfl,
    show gridGroupRate 46=((9/200):ℚ) from rfl,
    show gridGroupDerivative 46=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_47 : GridGroupGeometry 47 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 47=(23:Fin 32) from rfl,
    show gridGroupIndex 47=(70:Fin 780) from rfl,
    show gridGroupPartner 47=(180:ℤ) from rfl,
    show gridGroupRate 47=((1/18):ℚ) from rfl,
    show gridGroupDerivative 47=((13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_48 : GridGroupGeometry 48 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 48=(23:Fin 32) from rfl,
    show gridGroupIndex 48=(72:Fin 780) from rfl,
    show gridGroupPartner 48=(210:ℤ) from rfl,
    show gridGroupRate 48=((2/25):ℚ) from rfl,
    show gridGroupDerivative 48=((26/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_49 : GridGroupGeometry 49 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 49=(23:Fin 32) from rfl,
    show gridGroupIndex 49=(75:Fin 780) from rfl,
    show gridGroupPartner 49=(240:ℤ) from rfl,
    show gridGroupRate 49=((1/8):ℚ) from rfl,
    show gridGroupDerivative 49=((13/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_50 : GridGroupGeometry 50 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 50=(23:Fin 32) from rfl,
    show gridGroupIndex 50=(78:Fin 780) from rfl,
    show gridGroupPartner 50=(260:ℤ) from rfl,
    show gridGroupRate 50=((9/50):ℚ) from rfl,
    show gridGroupDerivative 50=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_51 : GridGroupGeometry 51 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 51=(23:Fin 32) from rfl,
    show gridGroupIndex 51=(80:Fin 780) from rfl,
    show gridGroupPartner 51=(270:ℤ) from rfl,
    show gridGroupRate 51=((2/9):ℚ) from rfl,
    show gridGroupDerivative 51=((26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_52 : GridGroupGeometry 52 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 52=(23:Fin 32) from rfl,
    show gridGroupIndex 52=(84:Fin 780) from rfl,
    show gridGroupPartner 52=(285:ℤ) from rfl,
    show gridGroupRate 52=((8/25):ℚ) from rfl,
    show gridGroupDerivative 52=((52/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_53 : GridGroupGeometry 53 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 53=(23:Fin 32) from rfl,
    show gridGroupIndex 53=(90:Fin 780) from rfl,
    show gridGroupPartner 53=(300:ℤ) from rfl,
    show gridGroupRate 53=((1/2):ℚ) from rfl,
    show gridGroupDerivative 53=(13:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_54 : GridGroupGeometry 54 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 54=(23:Fin 32) from rfl,
    show gridGroupIndex 54=(96:Fin 780) from rfl,
    show gridGroupPartner 54=(310:ℤ) from rfl,
    show gridGroupRate 54=((18/25):ℚ) from rfl,
    show gridGroupDerivative 54=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_55 : GridGroupGeometry 55 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 55=(23:Fin 32) from rfl,
    show gridGroupIndex 55=(100:Fin 780) from rfl,
    show gridGroupPartner 55=(315:ℤ) from rfl,
    show gridGroupRate 55=((8/9):ℚ) from rfl,
    show gridGroupDerivative 55=((52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_56 : GridGroupGeometry 56 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 56=(23:Fin 32) from rfl,
    show gridGroupIndex 56=(105:Fin 780) from rfl,
    show gridGroupPartner 56=(320:ℤ) from rfl,
    show gridGroupRate 56=((9/8):ℚ) from rfl,
    show gridGroupDerivative 56=((39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_57 : GridGroupGeometry 57 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 57=(23:Fin 32) from rfl,
    show gridGroupIndex 57=(110:Fin 780) from rfl,
    show gridGroupPartner 57=(324:ℤ) from rfl,
    show gridGroupRate 57=((25/18):ℚ) from rfl,
    show gridGroupDerivative 57=((65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_58 : GridGroupGeometry 58 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 58=(23:Fin 32) from rfl,
    show gridGroupIndex 58=(120:Fin 780) from rfl,
    show gridGroupPartner 58=(330:ℤ) from rfl,
    show gridGroupRate 58=(2:ℚ) from rfl,
    show gridGroupDerivative 58=(26:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_59 : GridGroupGeometry 59 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 59=(23:Fin 32) from rfl,
    show gridGroupIndex 59=(132:Fin 780) from rfl,
    show gridGroupPartner 59=(335:ℤ) from rfl,
    show gridGroupRate 59=((72/25):ℚ) from rfl,
    show gridGroupDerivative 59=((156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_60 : GridGroupGeometry 60 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 60=(23:Fin 32) from rfl,
    show gridGroupIndex 60=(150:Fin 780) from rfl,
    show gridGroupPartner 60=(340:ℤ) from rfl,
    show gridGroupRate 60=((9/2):ℚ) from rfl,
    show gridGroupDerivative 60=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_61 : GridGroupGeometry 61 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 61=(23:Fin 32) from rfl,
    show gridGroupIndex 61=(160:Fin 780) from rfl,
    show gridGroupPartner 61=(342:ℤ) from rfl,
    show gridGroupRate 61=((50/9):ℚ) from rfl,
    show gridGroupDerivative 61=((130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_62 : GridGroupGeometry 62 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 62=(23:Fin 32) from rfl,
    show gridGroupIndex 62=(180:Fin 780) from rfl,
    show gridGroupPartner 62=(345:ℤ) from rfl,
    show gridGroupRate 62=(8:ℚ) from rfl,
    show gridGroupDerivative 62=(52:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_63 : GridGroupGeometry 63 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 63=(23:Fin 32) from rfl,
    show gridGroupIndex 63=(210:Fin 780) from rfl,
    show gridGroupPartner 63=(348:ℤ) from rfl,
    show gridGroupRate 63=((25/2):ℚ) from rfl,
    show gridGroupDerivative 63=(65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_64 : GridGroupGeometry 64 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 64=(23:Fin 32) from rfl,
    show gridGroupIndex 64=(240:Fin 780) from rfl,
    show gridGroupPartner 64=(350:ℤ) from rfl,
    show gridGroupRate 64=(18:ℚ) from rfl,
    show gridGroupDerivative 64=(78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_65 : GridGroupGeometry 65 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 65=(23:Fin 32) from rfl,
    show gridGroupIndex 65=(260:Fin 780) from rfl,
    show gridGroupPartner 65=(351:ℤ) from rfl,
    show gridGroupRate 65=((200/9):ℚ) from rfl,
    show gridGroupDerivative 65=((260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_66 : GridGroupGeometry 66 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 66=(23:Fin 32) from rfl,
    show gridGroupIndex 66=(285:Fin 780) from rfl,
    show gridGroupPartner 66=(352:ℤ) from rfl,
    show gridGroupRate 66=((225/8):ℚ) from rfl,
    show gridGroupDerivative 66=((195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_67 : GridGroupGeometry 67 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 67=(23:Fin 32) from rfl,
    show gridGroupIndex 67=(360:Fin 780) from rfl,
    show gridGroupPartner 67=(354:ℤ) from rfl,
    show gridGroupRate 67=(50:ℚ) from rfl,
    show gridGroupDerivative 67=(130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_68 : GridGroupGeometry 68 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 68=(23:Fin 32) from rfl,
    show gridGroupIndex 68=(420:Fin 780) from rfl,
    show gridGroupPartner 68=(355:ℤ) from rfl,
    show gridGroupRate 68=(72:ℚ) from rfl,
    show gridGroupDerivative 68=(156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_69 : GridGroupGeometry 69 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 69=(23:Fin 32) from rfl,
    show gridGroupIndex 69=(510:Fin 780) from rfl,
    show gridGroupPartner 69=(356:ℤ) from rfl,
    show gridGroupRate 69=((225/2):ℚ) from rfl,
    show gridGroupDerivative 69=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_70 : GridGroupGeometry 70 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 70=(23:Fin 32) from rfl,
    show gridGroupIndex 70=(660:Fin 780) from rfl,
    show gridGroupPartner 70=(357:ℤ) from rfl,
    show gridGroupRate 70=(200:ℚ) from rfl,
    show gridGroupDerivative 70=(260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_71 : GridGroupGeometry 71 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 71=(27:Fin 32) from rfl,
    show gridGroupIndex 71=(260:Fin 780) from rfl,
    show gridGroupPartner 71=(-32:ℤ) from rfl,
    show gridGroupRate 71=(325:ℚ) from rfl,
    show gridGroupDerivative 71=(-1560:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 27=!![13,-7;-312,169] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_72 : GridGroupGeometry 72 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 72=(27:Fin 32) from rfl,
    show gridGroupIndex 72=(435:Fin 780) from rfl,
    show gridGroupPartner 72=(-39:ℤ) from rfl,
    show gridGroupRate 72=((25/13):ℚ) from rfl,
    show gridGroupDerivative 72=(120:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 27=!![13,-7;-312,169] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_73 : GridGroupGeometry 73 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 73=(27:Fin 32) from rfl,
    show gridGroupIndex 73=(585:Fin 780) from rfl,
    show gridGroupPartner 73=(-33:ℤ) from rfl,
    show gridGroupRate 73=(325:ℚ) from rfl,
    show gridGroupDerivative 73=(1560:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 27=!![13,-7;-312,169] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_74 : GridGroupGeometry 74 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 74=(10:Fin 32) from rfl,
    show gridGroupIndex 74=(0:Fin 780) from rfl,
    show gridGroupPartner 74=(-360:ℤ) from rfl,
    show gridGroupRate 74=(13:ℚ) from rfl,
    show gridGroupDerivative 74=(-26:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_75 : GridGroupGeometry 75 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 75=(10:Fin 32) from rfl,
    show gridGroupIndex 75=(65:Fin 780) from rfl,
    show gridGroupPartner 75=(-354:ℤ) from rfl,
    show gridGroupRate 75=((325/36):ℚ) from rfl,
    show gridGroupDerivative 75=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_76 : GridGroupGeometry 76 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 76=(10:Fin 32) from rfl,
    show gridGroupIndex 76=(90:Fin 780) from rfl,
    show gridGroupPartner 76=(-351:ℤ) from rfl,
    show gridGroupRate 76=((100/13):ℚ) from rfl,
    show gridGroupDerivative 76=(-20:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_77 : GridGroupGeometry 77 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 77=(10:Fin 32) from rfl,
    show gridGroupIndex 77=(130:Fin 780) from rfl,
    show gridGroupPartner 77=(-345:ℤ) from rfl,
    show gridGroupRate 77=((52/9):ℚ) from rfl,
    show gridGroupDerivative 77=((-52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_78 : GridGroupGeometry 78 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 78=(10:Fin 32) from rfl,
    show gridGroupIndex 78=(156:Fin 780) from rfl,
    show gridGroupPartner 78=(-340:ℤ) from rfl,
    show gridGroupRate 78=((117/25):ℚ) from rfl,
    show gridGroupDerivative 78=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_79 : GridGroupGeometry 79 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 79=(10:Fin 32) from rfl,
    show gridGroupIndex 79=(165:Fin 780) from rfl,
    show gridGroupPartner 79=(-338:ℤ) from rfl,
    show gridGroupRate 79=((225/52):ℚ) from rfl,
    show gridGroupDerivative 79=(-15:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_80 : GridGroupGeometry 80 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 80=(10:Fin 32) from rfl,
    show gridGroupIndex 80=(195:Fin 780) from rfl,
    show gridGroupPartner 80=(-330:ℤ) from rfl,
    show gridGroupRate 80=((13/4):ℚ) from rfl,
    show gridGroupDerivative 80=(-13:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_81 : GridGroupGeometry 81 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 81=(10:Fin 32) from rfl,
    show gridGroupIndex 81=(210:Fin 780) from rfl,
    show gridGroupPartner 81=(-325:ℤ) from rfl,
    show gridGroupRate 81=((36/13):ℚ) from rfl,
    show gridGroupDerivative 81=(-12:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_82 : GridGroupGeometry 82 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 82=(10:Fin 32) from rfl,
    show gridGroupIndex 82=(234:Fin 780) from rfl,
    show gridGroupPartner 82=(-315:ℤ) from rfl,
    show gridGroupRate 82=((52/25):ℚ) from rfl,
    show gridGroupDerivative 82=((-52/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_83 : GridGroupGeometry 83 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 83=(10:Fin 32) from rfl,
    show gridGroupIndex 83=(240:Fin 780) from rfl,
    show gridGroupPartner 83=(-312:ℤ) from rfl,
    show gridGroupRate 83=((25/13):ℚ) from rfl,
    show gridGroupDerivative 83=(-10:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_84 : GridGroupGeometry 84 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 84=(10:Fin 32) from rfl,
    show gridGroupIndex 84=(260:Fin 780) from rfl,
    show gridGroupPartner 84=(-300:ℤ) from rfl,
    show gridGroupRate 84=((13/9):ℚ) from rfl,
    show gridGroupDerivative 84=((-26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_85 : GridGroupGeometry 85 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 85=(10:Fin 32) from rfl,
    show gridGroupIndex 85=(273:Fin 780) from rfl,
    show gridGroupPartner 85=(-290:ℤ) from rfl,
    show gridGroupRate 85=((117/100):ℚ) from rfl,
    show gridGroupDerivative 85=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_86 : GridGroupGeometry 86 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 86=(10:Fin 32) from rfl,
    show gridGroupIndex 86=(290:Fin 780) from rfl,
    show gridGroupPartner 86=(-273:ℤ) from rfl,
    show gridGroupRate 86=((100/117):ℚ) from rfl,
    show gridGroupDerivative 86=((-20/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_87 : GridGroupGeometry 87 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 87=(10:Fin 32) from rfl,
    show gridGroupIndex 87=(300:Fin 780) from rfl,
    show gridGroupPartner 87=(-260:ℤ) from rfl,
    show gridGroupRate 87=((9/13):ℚ) from rfl,
    show gridGroupDerivative 87=(-6:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_88 : GridGroupGeometry 88 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 88=(10:Fin 32) from rfl,
    show gridGroupIndex 88=(312:Fin 780) from rfl,
    show gridGroupPartner 88=(-240:ℤ) from rfl,
    show gridGroupRate 88=((13/25):ℚ) from rfl,
    show gridGroupDerivative 88=((-26/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_89 : GridGroupGeometry 89 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 89=(10:Fin 32) from rfl,
    show gridGroupIndex 89=(315:Fin 780) from rfl,
    show gridGroupPartner 89=(-234:ℤ) from rfl,
    show gridGroupRate 89=((25/52):ℚ) from rfl,
    show gridGroupDerivative 89=(-5:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_90 : GridGroupGeometry 90 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 90=(10:Fin 32) from rfl,
    show gridGroupIndex 90=(325:Fin 780) from rfl,
    show gridGroupPartner 90=(-210:ℤ) from rfl,
    show gridGroupRate 90=((13/36):ℚ) from rfl,
    show gridGroupDerivative 90=((-13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_91 : GridGroupGeometry 91 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 91=(10:Fin 32) from rfl,
    show gridGroupIndex 91=(330:Fin 780) from rfl,
    show gridGroupPartner 91=(-195:ℤ) from rfl,
    show gridGroupRate 91=((4/13):ℚ) from rfl,
    show gridGroupDerivative 91=(-4:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_92 : GridGroupGeometry 92 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 92=(10:Fin 32) from rfl,
    show gridGroupIndex 92=(338:Fin 780) from rfl,
    show gridGroupPartner 92=(-165:ℤ) from rfl,
    show gridGroupRate 92=((52/225):ℚ) from rfl,
    show gridGroupDerivative 92=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_93 : GridGroupGeometry 93 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 93=(10:Fin 32) from rfl,
    show gridGroupIndex 93=(340:Fin 780) from rfl,
    show gridGroupPartner 93=(-156:ℤ) from rfl,
    show gridGroupRate 93=((25/117):ℚ) from rfl,
    show gridGroupDerivative 93=((-10/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_94 : GridGroupGeometry 94 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 94=(10:Fin 32) from rfl,
    show gridGroupIndex 94=(345:Fin 780) from rfl,
    show gridGroupPartner 94=(-130:ℤ) from rfl,
    show gridGroupRate 94=((9/52):ℚ) from rfl,
    show gridGroupDerivative 94=(-3:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_95 : GridGroupGeometry 95 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 95=(10:Fin 32) from rfl,
    show gridGroupIndex 95=(354:Fin 780) from rfl,
    show gridGroupPartner 95=(-65:ℤ) from rfl,
    show gridGroupRate 95=((36/325):ℚ) from rfl,
    show gridGroupDerivative 95=((-12/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_96 : GridGroupGeometry 96 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 96=(10:Fin 32) from rfl,
    show gridGroupIndex 96=(364:Fin 780) from rfl,
    show gridGroupPartner 96=(60:ℤ) from rfl,
    show gridGroupRate 96=((13/225):ℚ) from rfl,
    show gridGroupDerivative 96=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_97 : GridGroupGeometry 97 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 97=(10:Fin 32) from rfl,
    show gridGroupIndex 97=(365:Fin 780) from rfl,
    show gridGroupPartner 97=(78:ℤ) from rfl,
    show gridGroupRate 97=((25/468):ℚ) from rfl,
    show gridGroupDerivative 97=((-5/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_98 : GridGroupGeometry 98 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 98=(10:Fin 32) from rfl,
    show gridGroupIndex 98=(370:Fin 780) from rfl,
    show gridGroupPartner 98=(195:ℤ) from rfl,
    show gridGroupRate 98=((4/117):ℚ) from rfl,
    show gridGroupDerivative 98=((-4/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_99 : GridGroupGeometry 99 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 99=(10:Fin 32) from rfl,
    show gridGroupIndex 99=(372:Fin 780) from rfl,
    show gridGroupPartner 99=(260:ℤ) from rfl,
    show gridGroupRate 99=((9/325):ℚ) from rfl,
    show gridGroupDerivative 99=((-6/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_100 : GridGroupGeometry 100 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 100=(10:Fin 32) from rfl,
    show gridGroupIndex 100=(375:Fin 780) from rfl,
    show gridGroupPartner 100=(390:ℤ) from rfl,
    show gridGroupRate 100=((1/52):ℚ) from rfl,
    show gridGroupDerivative 100=(-1:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_101 : GridGroupGeometry 101 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 101=(10:Fin 32) from rfl,
    show gridGroupIndex 101=(377:Fin 780) from rfl,
    show gridGroupPartner 101=(510:ℤ) from rfl,
    show gridGroupRate 101=((13/900):ℚ) from rfl,
    show gridGroupDerivative 101=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_102 : GridGroupGeometry 102 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 102=(10:Fin 32) from rfl,
    show gridGroupIndex 102=(378:Fin 780) from rfl,
    show gridGroupPartner 102=(585:ℤ) from rfl,
    show gridGroupRate 102=((4/325):ℚ) from rfl,
    show gridGroupDerivative 102=((-4/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_103 : GridGroupGeometry 103 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 103=(10:Fin 32) from rfl,
    show gridGroupIndex 103=(380:Fin 780) from rfl,
    show gridGroupPartner 103=(780:ℤ) from rfl,
    show gridGroupRate 103=((1/117):ℚ) from rfl,
    show gridGroupDerivative 103=((-2/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_104 : GridGroupGeometry 104 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 104=(10:Fin 32) from rfl,
    show gridGroupIndex 104=(381:Fin 780) from rfl,
    show gridGroupPartner 104=(910:ℤ) from rfl,
    show gridGroupRate 104=((9/1300):ℚ) from rfl,
    show gridGroupDerivative 104=((-3/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_105 : GridGroupGeometry 105 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 105=(10:Fin 32) from rfl,
    show gridGroupIndex 105=(384:Fin 780) from rfl,
    show gridGroupPartner 105=(1560:ℤ) from rfl,
    show gridGroupRate 105=((1/325):ℚ) from rfl,
    show gridGroupDerivative 105=((-2/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_106 : GridGroupGeometry 106 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 106=(10:Fin 32) from rfl,
    show gridGroupIndex 106=(385:Fin 780) from rfl,
    show gridGroupPartner 106=(1950:ℤ) from rfl,
    show gridGroupRate 106=((1/468):ℚ) from rfl,
    show gridGroupDerivative 106=((-1/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_107 : GridGroupGeometry 107 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 107=(10:Fin 32) from rfl,
    show gridGroupIndex 107=(386:Fin 780) from rfl,
    show gridGroupPartner 107=(2535:ℤ) from rfl,
    show gridGroupRate 107=((4/2925):ℚ) from rfl,
    show gridGroupDerivative 107=((-4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_108 : GridGroupGeometry 108 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 108=(10:Fin 32) from rfl,
    show gridGroupIndex 108=(387:Fin 780) from rfl,
    show gridGroupPartner 108=(3510:ℤ) from rfl,
    show gridGroupRate 108=((1/1300):ℚ) from rfl,
    show gridGroupDerivative 108=((-1/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_109 : GridGroupGeometry 109 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 109=(10:Fin 32) from rfl,
    show gridGroupIndex 109=(388:Fin 780) from rfl,
    show gridGroupPartner 109=(5460:ℤ) from rfl,
    show gridGroupRate 109=((1/2925):ℚ) from rfl,
    show gridGroupDerivative 109=((-2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_110 : GridGroupGeometry 110 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 110=(10:Fin 32) from rfl,
    show gridGroupIndex 110=(389:Fin 780) from rfl,
    show gridGroupPartner 110=(11310:ℤ) from rfl,
    show gridGroupRate 110=((1/11700):ℚ) from rfl,
    show gridGroupDerivative 110=((-1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_111 : GridGroupGeometry 111 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 111=(10:Fin 32) from rfl,
    show gridGroupIndex 111=(391:Fin 780) from rfl,
    show gridGroupPartner 111=(-12090:ℤ) from rfl,
    show gridGroupRate 111=((1/11700):ℚ) from rfl,
    show gridGroupDerivative 111=((1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_112 : GridGroupGeometry 112 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 112=(10:Fin 32) from rfl,
    show gridGroupIndex 112=(392:Fin 780) from rfl,
    show gridGroupPartner 112=(-6240:ℤ) from rfl,
    show gridGroupRate 112=((1/2925):ℚ) from rfl,
    show gridGroupDerivative 112=((2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_113 : GridGroupGeometry 113 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 113=(10:Fin 32) from rfl,
    show gridGroupIndex 113=(393:Fin 780) from rfl,
    show gridGroupPartner 113=(-4290:ℤ) from rfl,
    show gridGroupRate 113=((1/1300):ℚ) from rfl,
    show gridGroupDerivative 113=((1/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_114 : GridGroupGeometry 114 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 114=(10:Fin 32) from rfl,
    show gridGroupIndex 114=(394:Fin 780) from rfl,
    show gridGroupPartner 114=(-3315:ℤ) from rfl,
    show gridGroupRate 114=((4/2925):ℚ) from rfl,
    show gridGroupDerivative 114=((4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_115 : GridGroupGeometry 115 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 115=(10:Fin 32) from rfl,
    show gridGroupIndex 115=(395:Fin 780) from rfl,
    show gridGroupPartner 115=(-2730:ℤ) from rfl,
    show gridGroupRate 115=((1/468):ℚ) from rfl,
    show gridGroupDerivative 115=((1/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_116 : GridGroupGeometry 116 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 116=(10:Fin 32) from rfl,
    show gridGroupIndex 116=(399:Fin 780) from rfl,
    show gridGroupPartner 116=(-1690:ℤ) from rfl,
    show gridGroupRate 116=((9/1300):ℚ) from rfl,
    show gridGroupDerivative 116=((3/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_117 : GridGroupGeometry 117 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 117=(10:Fin 32) from rfl,
    show gridGroupIndex 117=(402:Fin 780) from rfl,
    show gridGroupPartner 117=(-1365:ℤ) from rfl,
    show gridGroupRate 117=((4/325):ℚ) from rfl,
    show gridGroupDerivative 117=((4/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_118 : GridGroupGeometry 118 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 118=(10:Fin 32) from rfl,
    show gridGroupIndex 118=(403:Fin 780) from rfl,
    show gridGroupPartner 118=(-1290:ℤ) from rfl,
    show gridGroupRate 118=((13/900):ℚ) from rfl,
    show gridGroupDerivative 118=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_119 : GridGroupGeometry 119 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 119=(10:Fin 32) from rfl,
    show gridGroupIndex 119=(408:Fin 780) from rfl,
    show gridGroupPartner 119=(-1040:ℤ) from rfl,
    show gridGroupRate 119=((9/325):ℚ) from rfl,
    show gridGroupDerivative 119=((6/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_120 : GridGroupGeometry 120 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 120=(10:Fin 32) from rfl,
    show gridGroupIndex 120=(410:Fin 780) from rfl,
    show gridGroupPartner 120=(-975:ℤ) from rfl,
    show gridGroupRate 120=((4/117):ℚ) from rfl,
    show gridGroupDerivative 120=((4/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_121 : GridGroupGeometry 121 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 121=(10:Fin 32) from rfl,
    show gridGroupIndex 121=(415:Fin 780) from rfl,
    show gridGroupPartner 121=(-858:ℤ) from rfl,
    show gridGroupRate 121=((25/468):ℚ) from rfl,
    show gridGroupDerivative 121=((5/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![13,-6;-26,13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_122 : GridGroupGeometry 122 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 122=(21:Fin 32) from rfl,
    show gridGroupIndex 122=(600:Fin 780) from rfl,
    show gridGroupPartner 122=(422:ℤ) from rfl,
    show gridGroupRate 122=(450:ℚ) from rfl,
    show gridGroupDerivative 122=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![14,-27;26,-50] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_123 : GridGroupGeometry 123 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 123=(20:Fin 32) from rfl,
    show gridGroupIndex 123=(719:Fin 780) from rfl,
    show gridGroupPartner 123=(2220:ℤ) from rfl,
    show gridGroupRate 123=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 123=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 20=!![14,-13;26,-24] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_124 : GridGroupGeometry 124 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 124=(13:Fin 32) from rfl,
    show gridGroupIndex 124=(414:Fin 780) from rfl,
    show gridGroupPartner 124=(75:ℤ) from rfl,
    show gridGroupRate 124=((4/25):ℚ) from rfl,
    show gridGroupDerivative 124=((-364/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![15,-8;182,-97] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_125 : GridGroupGeometry 125 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 125=(13:Fin 32) from rfl,
    show gridGroupIndex 125=(417:Fin 780) from rfl,
    show gridGroupPartner 125=(50:ℤ) from rfl,
    show gridGroupRate 125=((9/100):ℚ) from rfl,
    show gridGroupDerivative 125=((273/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![15,-8;182,-97] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_126 : GridGroupGeometry 126 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 126=(5:Fin 32) from rfl,
    show gridGroupIndex 126=(195:Fin 780) from rfl,
    show gridGroupPartner 126=(728:ℤ) from rfl,
    show gridGroupRate 126=((225/8):ℚ) from rfl,
    show gridGroupDerivative 126=((-195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_127 : GridGroupGeometry 127 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 127=(5:Fin 32) from rfl,
    show gridGroupIndex 127=(220:Fin 780) from rfl,
    show gridGroupPartner 127=(729:ℤ) from rfl,
    show gridGroupRate 127=((200/9):ℚ) from rfl,
    show gridGroupDerivative 127=((-260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_128 : GridGroupGeometry 128 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 128=(5:Fin 32) from rfl,
    show gridGroupIndex 128=(270:Fin 780) from rfl,
    show gridGroupPartner 128=(732:ℤ) from rfl,
    show gridGroupRate 128=((25/2):ℚ) from rfl,
    show gridGroupDerivative 128=(-65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_129 : GridGroupGeometry 129 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 129=(5:Fin 32) from rfl,
    show gridGroupIndex 129=(320:Fin 780) from rfl,
    show gridGroupPartner 129=(738:ℤ) from rfl,
    show gridGroupRate 129=((50/9):ℚ) from rfl,
    show gridGroupDerivative 129=((-130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_130 : GridGroupGeometry 130 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 130=(5:Fin 32) from rfl,
    show gridGroupIndex 130=(345:Fin 780) from rfl,
    show gridGroupPartner 130=(744:ℤ) from rfl,
    show gridGroupRate 130=((25/8):ℚ) from rfl,
    show gridGroupDerivative 130=((-65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_131 : GridGroupGeometry 131 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 131=(5:Fin 32) from rfl,
    show gridGroupIndex 131=(411:Fin 780) from rfl,
    show gridGroupPartner 131=(920:ℤ) from rfl,
    show gridGroupRate 131=((9/200):ℚ) from rfl,
    show gridGroupDerivative 131=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_132 : GridGroupGeometry 132 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 132=(5:Fin 32) from rfl,
    show gridGroupIndex 132=(412:Fin 780) from rfl,
    show gridGroupPartner 132=(945:ℤ) from rfl,
    show gridGroupRate 132=((8/225):ℚ) from rfl,
    show gridGroupDerivative 132=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_133 : GridGroupGeometry 133 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 133=(5:Fin 32) from rfl,
    show gridGroupIndex 133=(419:Fin 780) from rfl,
    show gridGroupPartner 133=(2520:ℤ) from rfl,
    show gridGroupRate 133=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 133=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_134 : GridGroupGeometry 134 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 134=(5:Fin 32) from rfl,
    show gridGroupIndex 134=(421:Fin 780) from rfl,
    show gridGroupPartner 134=(-1080:ℤ) from rfl,
    show gridGroupRate 134=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 134=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_135 : GridGroupGeometry 135 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 135=(5:Fin 32) from rfl,
    show gridGroupIndex 135=(424:Fin 780) from rfl,
    show gridGroupPartner 135=(270:ℤ) from rfl,
    show gridGroupRate 135=((2/225):ℚ) from rfl,
    show gridGroupDerivative 135=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_136 : GridGroupGeometry 136 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 136=(5:Fin 32) from rfl,
    show gridGroupIndex 136=(425:Fin 780) from rfl,
    show gridGroupPartner 136=(360:ℤ) from rfl,
    show gridGroupRate 136=((1/72):ℚ) from rfl,
    show gridGroupDerivative 136=((13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_137 : GridGroupGeometry 137 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 137=(5:Fin 32) from rfl,
    show gridGroupIndex 137=(428:Fin 780) from rfl,
    show gridGroupPartner 137=(495:ℤ) from rfl,
    show gridGroupRate 137=((8/225):ℚ) from rfl,
    show gridGroupDerivative 137=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_138 : GridGroupGeometry 138 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 138=(5:Fin 32) from rfl,
    show gridGroupIndex 138=(432:Fin 780) from rfl,
    show gridGroupPartner 138=(570:ℤ) from rfl,
    show gridGroupRate 138=((2/25):ℚ) from rfl,
    show gridGroupDerivative 138=((26/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_139 : GridGroupGeometry 139 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 139=(5:Fin 32) from rfl,
    show gridGroupIndex 139=(438:Fin 780) from rfl,
    show gridGroupPartner 139=(620:ℤ) from rfl,
    show gridGroupRate 139=((9/50):ℚ) from rfl,
    show gridGroupDerivative 139=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_140 : GridGroupGeometry 140 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 140=(5:Fin 32) from rfl,
    show gridGroupIndex 140=(440:Fin 780) from rfl,
    show gridGroupPartner 140=(630:ℤ) from rfl,
    show gridGroupRate 140=((2/9):ℚ) from rfl,
    show gridGroupDerivative 140=((26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_141 : GridGroupGeometry 141 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 141=(5:Fin 32) from rfl,
    show gridGroupIndex 141=(445:Fin 780) from rfl,
    show gridGroupPartner 141=(648:ℤ) from rfl,
    show gridGroupRate 141=((25/72):ℚ) from rfl,
    show gridGroupDerivative 141=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_142 : GridGroupGeometry 142 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 142=(5:Fin 32) from rfl,
    show gridGroupIndex 142=(456:Fin 780) from rfl,
    show gridGroupPartner 142=(670:ℤ) from rfl,
    show gridGroupRate 142=((18/25):ℚ) from rfl,
    show gridGroupDerivative 142=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_143 : GridGroupGeometry 143 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 143=(5:Fin 32) from rfl,
    show gridGroupIndex 143=(460:Fin 780) from rfl,
    show gridGroupPartner 143=(675:ℤ) from rfl,
    show gridGroupRate 143=((8/9):ℚ) from rfl,
    show gridGroupDerivative 143=((52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_144 : GridGroupGeometry 144 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 144=(5:Fin 32) from rfl,
    show gridGroupIndex 144=(465:Fin 780) from rfl,
    show gridGroupPartner 144=(680:ℤ) from rfl,
    show gridGroupRate 144=((9/8):ℚ) from rfl,
    show gridGroupDerivative 144=((39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_145 : GridGroupGeometry 145 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 145=(5:Fin 32) from rfl,
    show gridGroupIndex 145=(470:Fin 780) from rfl,
    show gridGroupPartner 145=(684:ℤ) from rfl,
    show gridGroupRate 145=((25/18):ℚ) from rfl,
    show gridGroupDerivative 145=((65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_146 : GridGroupGeometry 146 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 146=(5:Fin 32) from rfl,
    show gridGroupIndex 146=(495:Fin 780) from rfl,
    show gridGroupPartner 146=(696:ℤ) from rfl,
    show gridGroupRate 146=((25/8):ℚ) from rfl,
    show gridGroupDerivative 146=((65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_147 : GridGroupGeometry 147 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 147=(5:Fin 32) from rfl,
    show gridGroupIndex 147=(510:Fin 780) from rfl,
    show gridGroupPartner 147=(700:ℤ) from rfl,
    show gridGroupRate 147=((9/2):ℚ) from rfl,
    show gridGroupDerivative 147=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_148 : GridGroupGeometry 148 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 148=(5:Fin 32) from rfl,
    show gridGroupIndex 148=(570:Fin 780) from rfl,
    show gridGroupPartner 148=(708:ℤ) from rfl,
    show gridGroupRate 148=((25/2):ℚ) from rfl,
    show gridGroupDerivative 148=(65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_149 : GridGroupGeometry 149 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 149=(5:Fin 32) from rfl,
    show gridGroupIndex 149=(600:Fin 780) from rfl,
    show gridGroupPartner 149=(710:ℤ) from rfl,
    show gridGroupRate 149=(18:ℚ) from rfl,
    show gridGroupDerivative 149=(78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_150 : GridGroupGeometry 150 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 150=(5:Fin 32) from rfl,
    show gridGroupIndex 150=(620:Fin 780) from rfl,
    show gridGroupPartner 150=(711:ℤ) from rfl,
    show gridGroupRate 150=((200/9):ℚ) from rfl,
    show gridGroupDerivative 150=((260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_151 : GridGroupGeometry 151 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 151=(5:Fin 32) from rfl,
    show gridGroupIndex 151=(720:Fin 780) from rfl,
    show gridGroupPartner 151=(714:ℤ) from rfl,
    show gridGroupRate 151=(50:ℚ) from rfl,
    show gridGroupDerivative 151=(130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![24,-13;26,-14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_152 : GridGroupGeometry 152 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 152=(6:Fin 32) from rfl,
    show gridGroupIndex 152=(90:Fin 780) from rfl,
    show gridGroupPartner 152=(716:ℤ) from rfl,
    show gridGroupRate 152=((225/2):ℚ) from rfl,
    show gridGroupDerivative 152=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![24,11;26,12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_153 : GridGroupGeometry 153 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 153=(6:Fin 32) from rfl,
    show gridGroupIndex 153=(240:Fin 780) from rfl,
    show gridGroupPartner 153=(717:ℤ) from rfl,
    show gridGroupRate 153=(200:ℚ) from rfl,
    show gridGroupDerivative 153=(260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![24,11;26,12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_154 : GridGroupGeometry 154 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 154=(6:Fin 32) from rfl,
    show gridGroupIndex 154=(540:Fin 780) from rfl,
    show gridGroupPartner 154=(718:ℤ) from rfl,
    show gridGroupRate 154=(450:ℚ) from rfl,
    show gridGroupDerivative 154=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![24,11;26,12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_155 : GridGroupGeometry 155 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 155=(3:Fin 32) from rfl,
    show gridGroupIndex 155=(510:Fin 780) from rfl,
    show gridGroupPartner 155=(753:ℤ) from rfl,
    show gridGroupRate 155=(100:ℚ) from rfl,
    show gridGroupDerivative 155=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![25,-26;26,-27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_156 : GridGroupGeometry 156 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 156=(3:Fin 32) from rfl,
    show gridGroupIndex 156=(774:Fin 780) from rfl,
    show gridGroupPartner 156=(775:ℤ) from rfl,
    show gridGroupRate 156=((36/25):ℚ) from rfl,
    show gridGroupDerivative 156=((-156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![25,-26;26,-27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_157 : GridGroupGeometry 157 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 157=(14:Fin 32) from rfl,
    show gridGroupIndex 157=(25:Fin 780) from rfl,
    show gridGroupPartner 157=(-31:ℤ) from rfl,
    show gridGroupRate 157=(25:ℚ) from rfl,
    show gridGroupDerivative 157=(-3120:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![25,-1;-624,25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_158 : GridGroupGeometry 158 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 158=(8:Fin 32) from rfl,
    show gridGroupIndex 158=(771:Fin 780) from rfl,
    show gridGroupPartner 158=(1820:ℤ) from rfl,
    show gridGroupRate 158=((9/2600):ℚ) from rfl,
    show gridGroupDerivative 158=((-3/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_159 : GridGroupGeometry 159 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 159=(8:Fin 32) from rfl,
    show gridGroupIndex 159=(772:Fin 780) from rfl,
    show gridGroupPartner 159=(2145:ℤ) from rfl,
    show gridGroupRate 159=((8/2925):ℚ) from rfl,
    show gridGroupDerivative 159=((-4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_160 : GridGroupGeometry 160 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 160=(8:Fin 32) from rfl,
    show gridGroupIndex 160=(774:Fin 780) from rfl,
    show gridGroupPartner 160=(3120:ℤ) from rfl,
    show gridGroupRate 160=((1/650):ℚ) from rfl,
    show gridGroupDerivative 160=((-1/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_161 : GridGroupGeometry 161 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 161=(8:Fin 32) from rfl,
    show gridGroupIndex 161=(776:Fin 780) from rfl,
    show gridGroupPartner 161=(5070:ℤ) from rfl,
    show gridGroupRate 161=((2/2925):ℚ) from rfl,
    show gridGroupDerivative 161=((-2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_162 : GridGroupGeometry 162 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 162=(8:Fin 32) from rfl,
    show gridGroupIndex 162=(777:Fin 780) from rfl,
    show gridGroupPartner 162=(7020:ℤ) from rfl,
    show gridGroupRate 162=((1/2600):ℚ) from rfl,
    show gridGroupDerivative 162=((-1/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_163 : GridGroupGeometry 163 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 163=(8:Fin 32) from rfl,
    show gridGroupIndex 163=(778:Fin 780) from rfl,
    show gridGroupPartner 163=(10920:ℤ) from rfl,
    show gridGroupRate 163=((1/5850):ℚ) from rfl,
    show gridGroupDerivative 163=((-1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_164 : GridGroupGeometry 164 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 164=(8:Fin 32) from rfl,
    show gridGroupIndex 164=(779:Fin 780) from rfl,
    show gridGroupPartner 164=(22620:ℤ) from rfl,
    show gridGroupRate 164=((1/23400):ℚ) from rfl,
    show gridGroupDerivative 164=((-1/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![26,-25;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_165 : GridGroupGeometry 165 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 165=(26:Fin 32) from rfl,
    show gridGroupIndex 165=(0:Fin 780) from rfl,
    show gridGroupPartner 165=(-30:ℤ) from rfl,
    show gridGroupRate 165=(26:ℚ) from rfl,
    show gridGroupDerivative 165=(702:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 26=!![26,1;-702,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_166 : GridGroupGeometry 166 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 166=(26:Fin 32) from rfl,
    show gridGroupIndex 166=(260:Fin 780) from rfl,
    show gridGroupPartner 166=(-29:ℤ) from rfl,
    show gridGroupRate 166=(2600:ℚ) from rfl,
    show gridGroupDerivative 166=(7020:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 26=!![26,1;-702,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_167 : GridGroupGeometry 167 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 167=(29:Fin 32) from rfl,
    show gridGroupIndex 167=(1:Fin 780) from rfl,
    show gridGroupPartner 167=(-24180:ℤ) from rfl,
    show gridGroupRate 167=((1/23400):ℚ) from rfl,
    show gridGroupDerivative 167=((1/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_168 : GridGroupGeometry 168 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 168=(29:Fin 32) from rfl,
    show gridGroupIndex 168=(2:Fin 780) from rfl,
    show gridGroupPartner 168=(-12480:ℤ) from rfl,
    show gridGroupRate 168=((1/5850):ℚ) from rfl,
    show gridGroupDerivative 168=((1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_169 : GridGroupGeometry 169 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 169=(29:Fin 32) from rfl,
    show gridGroupIndex 169=(3:Fin 780) from rfl,
    show gridGroupPartner 169=(-8580:ℤ) from rfl,
    show gridGroupRate 169=((1/2600):ℚ) from rfl,
    show gridGroupDerivative 169=((1/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_170 : GridGroupGeometry 170 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 170=(29:Fin 32) from rfl,
    show gridGroupIndex 170=(4:Fin 780) from rfl,
    show gridGroupPartner 170=(-6630:ℤ) from rfl,
    show gridGroupRate 170=((2/2925):ℚ) from rfl,
    show gridGroupDerivative 170=((2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_171 : GridGroupGeometry 171 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 171=(29:Fin 32) from rfl,
    show gridGroupIndex 171=(13:Fin 780) from rfl,
    show gridGroupPartner 171=(-2580:ℤ) from rfl,
    show gridGroupRate 171=((13/1800):ℚ) from rfl,
    show gridGroupDerivative 171=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_172 : GridGroupGeometry 172 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 172=(29:Fin 32) from rfl,
    show gridGroupIndex 172=(104:Fin 780) from rfl,
    show gridGroupPartner 172=(-1005:ℤ) from rfl,
    show gridGroupRate 172=((104/225):ℚ) from rfl,
    show gridGroupDerivative 172=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_173 : GridGroupGeometry 173 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 173=(29:Fin 32) from rfl,
    show gridGroupIndex 173=(117:Fin 780) from rfl,
    show gridGroupPartner 173=(-980:ℤ) from rfl,
    show gridGroupRate 173=((117/200):ℚ) from rfl,
    show gridGroupDerivative 173=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_174 : GridGroupGeometry 174 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 174=(29:Fin 32) from rfl,
    show gridGroupIndex 174=(200:Fin 780) from rfl,
    show gridGroupPartner 174=(-897:ℤ) from rfl,
    show gridGroupRate 174=((200/117):ℚ) from rfl,
    show gridGroupDerivative 174=((20/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_175 : GridGroupGeometry 175 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 175=(29:Fin 32) from rfl,
    show gridGroupIndex 175=(225:Fin 780) from rfl,
    show gridGroupPartner 175=(-884:ℤ) from rfl,
    show gridGroupRate 175=((225/104):ℚ) from rfl,
    show gridGroupDerivative 175=((15/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 29=!![26,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_176 : GridGroupGeometry 176 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 176=(28:Fin 32) from rfl,
    show gridGroupIndex 176=(156:Fin 780) from rfl,
    show gridGroupPartner 176=(31:ℤ) from rfl,
    show gridGroupRate 176=(936:ℚ) from rfl,
    show gridGroupDerivative 176=(3900:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 28=!![26,1;650,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_177 : GridGroupGeometry 177 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 177=(30:Fin 32) from rfl,
    show gridGroupIndex 177=(120:Fin 780) from rfl,
    show gridGroupPartner 177=(-806:ℤ) from rfl,
    show gridGroupRate 177=((450/13):ℚ) from rfl,
    show gridGroupDerivative 177=(30:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 30=!![26,27;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_178 : GridGroupGeometry 178 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 178=(22:Fin 32) from rfl,
    show gridGroupIndex 178=(150:Fin 780) from rfl,
    show gridGroupPartner 178=(406:ℤ) from rfl,
    show gridGroupRate 178=(225:ℚ) from rfl,
    show gridGroupDerivative 178=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![27,-13;52,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_179 : GridGroupGeometry 179 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 179=(22:Fin 32) from rfl,
    show gridGroupIndex 179=(374:Fin 780) from rfl,
    show gridGroupPartner 179=(630:ℤ) from rfl,
    show gridGroupRate 179=((1/225):ℚ) from rfl,
    show gridGroupDerivative 179=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![27,-13;52,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_180 : GridGroupGeometry 180 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 180=(0:Fin 32) from rfl,
    show gridGroupIndex 180=(90:Fin 780) from rfl,
    show gridGroupPartner 180=(809:ℤ) from rfl,
    show gridGroupRate 180=(900:ℚ) from rfl,
    show gridGroupDerivative 180=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![27,28;26,27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_181 : GridGroupGeometry 181 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 181=(2:Fin 32) from rfl,
    show gridGroupIndex 181=(358:Fin 780) from rfl,
    show gridGroupPartner 181=(1740:ℤ) from rfl,
    show gridGroupRate 181=((1/450):ℚ) from rfl,
    show gridGroupDerivative 181=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_182 : GridGroupGeometry 182 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 182=(2:Fin 32) from rfl,
    show gridGroupIndex 182=(359:Fin 780) from rfl,
    show gridGroupPartner 182=(2640:ℤ) from rfl,
    show gridGroupRate 182=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 182=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_183 : GridGroupGeometry 183 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 183=(2:Fin 32) from rfl,
    show gridGroupIndex 183=(361:Fin 780) from rfl,
    show gridGroupPartner 183=(-960:ℤ) from rfl,
    show gridGroupRate 183=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 183=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_184 : GridGroupGeometry 184 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 184=(2:Fin 32) from rfl,
    show gridGroupIndex 184=(362:Fin 780) from rfl,
    show gridGroupPartner 184=(-60:ℤ) from rfl,
    show gridGroupRate 184=((1/450):ℚ) from rfl,
    show gridGroupDerivative 184=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_185 : GridGroupGeometry 185 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 185=(2:Fin 32) from rfl,
    show gridGroupIndex 185=(363:Fin 780) from rfl,
    show gridGroupPartner 185=(240:ℤ) from rfl,
    show gridGroupRate 185=((1/200):ℚ) from rfl,
    show gridGroupDerivative 185=((13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_186 : GridGroupGeometry 186 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 186=(2:Fin 32) from rfl,
    show gridGroupIndex 186=(366:Fin 780) from rfl,
    show gridGroupPartner 186=(540:ℤ) from rfl,
    show gridGroupRate 186=((1/50):ℚ) from rfl,
    show gridGroupDerivative 186=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_187 : GridGroupGeometry 187 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 187=(2:Fin 32) from rfl,
    show gridGroupIndex 187=(368:Fin 780) from rfl,
    show gridGroupPartner 187=(615:ℤ) from rfl,
    show gridGroupRate 187=((8/225):ℚ) from rfl,
    show gridGroupDerivative 187=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_188 : GridGroupGeometry 188 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 188=(2:Fin 32) from rfl,
    show gridGroupIndex 188=(369:Fin 780) from rfl,
    show gridGroupPartner 188=(640:ℤ) from rfl,
    show gridGroupRate 188=((9/200):ℚ) from rfl,
    show gridGroupDerivative 188=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![28,-13;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_189 : GridGroupGeometry 189 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 189=(12:Fin 32) from rfl,
    show gridGroupIndex 189=(20:Fin 780) from rfl,
    show gridGroupPartner 189=(66:ℤ) from rfl,
    show gridGroupRate 189=((50/9):ℚ) from rfl,
    show gridGroupDerivative 189=((-1690/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![28,-1;338,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_190 : GridGroupGeometry 190 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 190=(12:Fin 32) from rfl,
    show gridGroupIndex 190=(27:Fin 780) from rfl,
    show gridGroupPartner 190=(80:ℤ) from rfl,
    show gridGroupRate 190=((9/200):ℚ) from rfl,
    show gridGroupDerivative 190=((-507/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![28,-1;338,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_191 : GridGroupGeometry 191 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 191=(12:Fin 32) from rfl,
    show gridGroupIndex 191=(28:Fin 780) from rfl,
    show gridGroupPartner 191=(30:ℤ) from rfl,
    show gridGroupRate 191=((2/225):ℚ) from rfl,
    show gridGroupDerivative 191=((338/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![28,-1;338,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_192 : GridGroupGeometry 192 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 192=(12:Fin 32) from rfl,
    show gridGroupIndex 192=(30:Fin 780) from rfl,
    show gridGroupPartner 192=(60:ℤ) from rfl,
    show gridGroupRate 192=((1/2):ℚ) from rfl,
    show gridGroupDerivative 192=(169:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![28,-1;338,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_193 : GridGroupGeometry 193 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 193=(12:Fin 32) from rfl,
    show gridGroupIndex 193=(45:Fin 780) from rfl,
    show gridGroupPartner 193=(64:ℤ) from rfl,
    show gridGroupRate 193=((225/8):ℚ) from rfl,
    show gridGroupDerivative 193=((2535/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![28,-1;338,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_194 : GridGroupGeometry 194 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 194=(24:Fin 32) from rfl,
    show gridGroupIndex 194=(16:Fin 780) from rfl,
    show gridGroupPartner 194=(430:ℤ) from rfl,
    show gridGroupRate 194=((2/25):ℚ) from rfl,
    show gridGroupDerivative 194=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_195 : GridGroupGeometry 195 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 195=(24:Fin 32) from rfl,
    show gridGroupIndex 195=(18:Fin 780) from rfl,
    show gridGroupPartner 195=(480:ℤ) from rfl,
    show gridGroupRate 195=((1/50):ℚ) from rfl,
    show gridGroupDerivative 195=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_196 : GridGroupGeometry 196 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 196=(24:Fin 32) from rfl,
    show gridGroupIndex 196=(19:Fin 780) from rfl,
    show gridGroupPartner 196=(580:ℤ) from rfl,
    show gridGroupRate 196=((1/200):ℚ) from rfl,
    show gridGroupDerivative 196=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_197 : GridGroupGeometry 197 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 197=(24:Fin 32) from rfl,
    show gridGroupIndex 197=(21:Fin 780) from rfl,
    show gridGroupPartner 197=(180:ℤ) from rfl,
    show gridGroupRate 197=((1/200):ℚ) from rfl,
    show gridGroupDerivative 197=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_198 : GridGroupGeometry 198 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 198=(24:Fin 32) from rfl,
    show gridGroupIndex 198=(22:Fin 780) from rfl,
    show gridGroupPartner 198=(280:ℤ) from rfl,
    show gridGroupRate 198=((1/50):ℚ) from rfl,
    show gridGroupDerivative 198=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_199 : GridGroupGeometry 199 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 199=(24:Fin 32) from rfl,
    show gridGroupIndex 199=(25:Fin 780) from rfl,
    show gridGroupPartner 199=(340:ℤ) from rfl,
    show gridGroupRate 199=((1/8):ℚ) from rfl,
    show gridGroupDerivative 199=((39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_200 : GridGroupGeometry 200 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 200=(24:Fin 32) from rfl,
    show gridGroupIndex 200=(70:Fin 780) from rfl,
    show gridGroupPartner 200=(376:ℤ) from rfl,
    show gridGroupRate 200=((25/2):ℚ) from rfl,
    show gridGroupDerivative 200=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_201 : GridGroupGeometry 201 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 201=(24:Fin 32) from rfl,
    show gridGroupIndex 201=(220:Fin 780) from rfl,
    show gridGroupPartner 201=(379:ℤ) from rfl,
    show gridGroupRate 201=(200:ℚ) from rfl,
    show gridGroupDerivative 201=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![38,-1;78,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_202 : GridGroupGeometry 202 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 202=(7:Fin 32) from rfl,
    show gridGroupIndex 202=(32:Fin 780) from rfl,
    show gridGroupPartner 202=(-2040:ℤ) from rfl,
    show gridGroupRate 202=((1/225):ℚ) from rfl,
    show gridGroupDerivative 202=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![53,-2;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_203 : GridGroupGeometry 203 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 203=(7:Fin 32) from rfl,
    show gridGroupIndex 203=(33:Fin 780) from rfl,
    show gridGroupPartner 203=(-1890:ℤ) from rfl,
    show gridGroupRate 203=((1/100):ℚ) from rfl,
    show gridGroupDerivative 203=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![53,-2;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_204 : GridGroupGeometry 204 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 204=(7:Fin 32) from rfl,
    show gridGroupIndex 204=(39:Fin 780) from rfl,
    show gridGroupPartner 204=(-1690:ℤ) from rfl,
    show gridGroupRate 204=((9/100):ℚ) from rfl,
    show gridGroupDerivative 204=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![53,-2;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_205 : GridGroupGeometry 205 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 205=(1:Fin 32) from rfl,
    show gridGroupIndex 205=(210:Fin 780) from rfl,
    show gridGroupPartner 205=(794:ℤ) from rfl,
    show gridGroupRate 205=(225:ℚ) from rfl,
    show gridGroupDerivative 205=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 1=!![53,1;52,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_206 : GridGroupGeometry 206 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 206=(4:Fin 32) from rfl,
    show gridGroupIndex 206=(200:Fin 780) from rfl,
    show gridGroupPartner 206=(761:ℤ) from rfl,
    show gridGroupRate 206=(200:ℚ) from rfl,
    show gridGroupDerivative 206=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_207 : GridGroupGeometry 207 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 207=(4:Fin 32) from rfl,
    show gridGroupIndex 207=(300:Fin 780) from rfl,
    show gridGroupPartner 207=(762:ℤ) from rfl,
    show gridGroupRate 207=(50:ℚ) from rfl,
    show gridGroupDerivative 207=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_208 : GridGroupGeometry 208 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 208=(4:Fin 32) from rfl,
    show gridGroupIndex 208=(350:Fin 780) from rfl,
    show gridGroupPartner 208=(764:ℤ) from rfl,
    show gridGroupRate 208=((25/2):ℚ) from rfl,
    show gridGroupDerivative 208=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_209 : GridGroupGeometry 209 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 209=(4:Fin 32) from rfl,
    show gridGroupIndex 209=(380:Fin 780) from rfl,
    show gridGroupPartner 209=(770:ℤ) from rfl,
    show gridGroupRate 209=(2:ℚ) from rfl,
    show gridGroupDerivative 209=(-78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_210 : GridGroupGeometry 210 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 210=(4:Fin 32) from rfl,
    show gridGroupIndex 210=(398:Fin 780) from rfl,
    show gridGroupPartner 210=(860:ℤ) from rfl,
    show gridGroupRate 210=((1/50):ℚ) from rfl,
    show gridGroupDerivative 210=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_211 : GridGroupGeometry 211 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 211=(4:Fin 32) from rfl,
    show gridGroupIndex 211=(401:Fin 780) from rfl,
    show gridGroupPartner 211=(560:ℤ) from rfl,
    show gridGroupRate 211=((1/200):ℚ) from rfl,
    show gridGroupDerivative 211=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_212 : GridGroupGeometry 212 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 212=(4:Fin 32) from rfl,
    show gridGroupIndex 212=(402:Fin 780) from rfl,
    show gridGroupPartner 212=(660:ℤ) from rfl,
    show gridGroupRate 212=((1/50):ℚ) from rfl,
    show gridGroupDerivative 212=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_213 : GridGroupGeometry 213 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 213=(4:Fin 32) from rfl,
    show gridGroupIndex 213=(404:Fin 780) from rfl,
    show gridGroupPartner 213=(710:ℤ) from rfl,
    show gridGroupRate 213=((2/25):ℚ) from rfl,
    show gridGroupDerivative 213=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_214 : GridGroupGeometry 214 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 214=(4:Fin 32) from rfl,
    show gridGroupIndex 214=(408:Fin 780) from rfl,
    show gridGroupPartner 214=(735:ℤ) from rfl,
    show gridGroupRate 214=((8/25):ℚ) from rfl,
    show gridGroupDerivative 214=((156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_215 : GridGroupGeometry 215 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 215=(4:Fin 32) from rfl,
    show gridGroupIndex 215=(410:Fin 780) from rfl,
    show gridGroupPartner 215=(740:ℤ) from rfl,
    show gridGroupRate 215=((1/2):ℚ) from rfl,
    show gridGroupDerivative 215=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_216 : GridGroupGeometry 216 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 216=(4:Fin 32) from rfl,
    show gridGroupIndex 216=(425:Fin 780) from rfl,
    show gridGroupPartner 216=(752:ℤ) from rfl,
    show gridGroupRate 216=((25/8):ℚ) from rfl,
    show gridGroupDerivative 216=((195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_217 : GridGroupGeometry 217 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 217=(4:Fin 32) from rfl,
    show gridGroupIndex 217=(440:Fin 780) from rfl,
    show gridGroupPartner 217=(755:ℤ) from rfl,
    show gridGroupRate 217=(8:ℚ) from rfl,
    show gridGroupDerivative 217=(156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_218 : GridGroupGeometry 218 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 218=(4:Fin 32) from rfl,
    show gridGroupIndex 218=(450:Fin 780) from rfl,
    show gridGroupPartner 218=(756:ℤ) from rfl,
    show gridGroupRate 218=((25/2):ℚ) from rfl,
    show gridGroupDerivative 218=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_219 : GridGroupGeometry 219 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 219=(4:Fin 32) from rfl,
    show gridGroupIndex 219=(500:Fin 780) from rfl,
    show gridGroupPartner 219=(758:ℤ) from rfl,
    show gridGroupRate 219=(50:ℚ) from rfl,
    show gridGroupDerivative 219=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_220 : GridGroupGeometry 220 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 220=(4:Fin 32) from rfl,
    show gridGroupIndex 220=(600:Fin 780) from rfl,
    show gridGroupPartner 220=(759:ℤ) from rfl,
    show gridGroupRate 220=(200:ℚ) from rfl,
    show gridGroupDerivative 220=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![76,-39;78,-40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_221 : GridGroupGeometry 221 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 221=(19:Fin 32) from rfl,
    show gridGroupIndex 221=(405:Fin 780) from rfl,
    show gridGroupPartner 221=(418:ℤ) from rfl,
    show gridGroupRate 221=((225/4):ℚ) from rfl,
    show gridGroupDerivative 221=(-2535:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![181,-98;338,-183] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_222 : GridGroupGeometry 222 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 222=(19:Fin 32) from rfl,
    show gridGroupIndex 222=(422:Fin 780) from rfl,
    show gridGroupPartner 222=(435:ℤ) from rfl,
    show gridGroupRate 222=((4/225):ℚ) from rfl,
    show gridGroupDerivative 222=((-676/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![181,-98;338,-183] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_223 : GridGroupGeometry 223 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 223=(19:Fin 32) from rfl,
    show gridGroupIndex 223=(423:Fin 780) from rfl,
    show gridGroupPartner 223=(410:ℤ) from rfl,
    show gridGroupRate 223=((9/100):ℚ) from rfl,
    show gridGroupDerivative 223=((507/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![181,-98;338,-183] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_224 : GridGroupGeometry 224 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 224=(19:Fin 32) from rfl,
    show gridGroupIndex 224=(430:Fin 780) from rfl,
    show gridGroupPartner 224=(417:ℤ) from rfl,
    show gridGroupRate 224=((100/9):ℚ) from rfl,
    show gridGroupDerivative 224=((3380/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![181,-98;338,-183] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_225 : GridGroupGeometry 225 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 225=(31:Fin 32) from rfl,
    show gridGroupIndex 225=(26:Fin 780) from rfl,
    show gridGroupPartner 225=(450:ℤ) from rfl,
    show gridGroupRate 225=((13/225):ℚ) from rfl,
    show gridGroupDerivative 225=((-364/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 31=!![195,-7;364,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_226 : GridGroupGeometry 226 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 226=(9:Fin 32) from rfl,
    show gridGroupIndex 226=(360:Fin 780) from rfl,
    show gridGroupPartner 226=(-836:ℤ) from rfl,
    show gridGroupRate 226=(225:ℚ) from rfl,
    show gridGroupDerivative 226=(-3120:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_227 : GridGroupGeometry 227 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 227=(9:Fin 32) from rfl,
    show gridGroupIndex 227=(405:Fin 780) from rfl,
    show gridGroupPartner 227=(-835:ℤ) from rfl,
    show gridGroupRate 227=(9:ℚ) from rfl,
    show gridGroupDerivative 227=(-624:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_228 : GridGroupGeometry 228 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 228=(9:Fin 32) from rfl,
    show gridGroupIndex 228=(410:Fin 780) from rfl,
    show gridGroupPartner 228=(-834:ℤ) from rfl,
    show gridGroupRate 228=((25/9):ℚ) from rfl,
    show gridGroupDerivative 228=((-1040/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_229 : GridGroupGeometry 229 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 229=(9:Fin 32) from rfl,
    show gridGroupIndex 229=(414:Fin 780) from rfl,
    show gridGroupPartner 229=(-830:ℤ) from rfl,
    show gridGroupRate 229=((9/25):ℚ) from rfl,
    show gridGroupDerivative 229=((-624/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_230 : GridGroupGeometry 230 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 230=(9:Fin 32) from rfl,
    show gridGroupIndex 230=(415:Fin 780) from rfl,
    show gridGroupPartner 230=(-825:ℤ) from rfl,
    show gridGroupRate 230=((1/9):ℚ) from rfl,
    show gridGroupDerivative 230=((-208/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_231 : GridGroupGeometry 231 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 231=(9:Fin 32) from rfl,
    show gridGroupIndex 231=(416:Fin 780) from rfl,
    show gridGroupPartner 231=(-780:ℤ) from rfl,
    show gridGroupRate 231=((1/225):ℚ) from rfl,
    show gridGroupDerivative 231=((-208/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_232 : GridGroupGeometry 232 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 232=(9:Fin 32) from rfl,
    show gridGroupIndex 232=(417:Fin 780) from rfl,
    show gridGroupPartner 232=(-855:ℤ) from rfl,
    show gridGroupRate 232=((1/25):ℚ) from rfl,
    show gridGroupDerivative 232=((208/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_233 : GridGroupGeometry 233 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 233=(9:Fin 32) from rfl,
    show gridGroupIndex 233=(420:Fin 780) from rfl,
    show gridGroupPartner 233=(-840:ℤ) from rfl,
    show gridGroupRate 233=(1:ℚ) from rfl,
    show gridGroupDerivative 233=(208:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_234 : GridGroupGeometry 234 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 234=(9:Fin 32) from rfl,
    show gridGroupIndex 234=(435:Fin 780) from rfl,
    show gridGroupPartner 234=(-837:ℤ) from rfl,
    show gridGroupRate 234=(25:ℚ) from rfl,
    show gridGroupDerivative 234=(1040:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![223,-119;-208,111] from rfl]
  norm_num [Matrix.det_fin_two]

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermGeometryV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open Matrix SmallLevelAdditive

theorem gridGroup_geometry (i : Fin 235) : GridGroupGeometry i := by
  fin_cases i
  · exact gridGroup_geometry_0
  · exact gridGroup_geometry_1
  · exact gridGroup_geometry_2
  · exact gridGroup_geometry_3
  · exact gridGroup_geometry_4
  · exact gridGroup_geometry_5
  · exact gridGroup_geometry_6
  · exact gridGroup_geometry_7
  · exact gridGroup_geometry_8
  · exact gridGroup_geometry_9
  · exact gridGroup_geometry_10
  · exact gridGroup_geometry_11
  · exact gridGroup_geometry_12
  · exact gridGroup_geometry_13
  · exact gridGroup_geometry_14
  · exact gridGroup_geometry_15
  · exact gridGroup_geometry_16
  · exact gridGroup_geometry_17
  · exact gridGroup_geometry_18
  · exact gridGroup_geometry_19
  · exact gridGroup_geometry_20
  · exact gridGroup_geometry_21
  · exact gridGroup_geometry_22
  · exact gridGroup_geometry_23
  · exact gridGroup_geometry_24
  · exact gridGroup_geometry_25
  · exact gridGroup_geometry_26
  · exact gridGroup_geometry_27
  · exact gridGroup_geometry_28
  · exact gridGroup_geometry_29
  · exact gridGroup_geometry_30
  · exact gridGroup_geometry_31
  · exact gridGroup_geometry_32
  · exact gridGroup_geometry_33
  · exact gridGroup_geometry_34
  · exact gridGroup_geometry_35
  · exact gridGroup_geometry_36
  · exact gridGroup_geometry_37
  · exact gridGroup_geometry_38
  · exact gridGroup_geometry_39
  · exact gridGroup_geometry_40
  · exact gridGroup_geometry_41
  · exact gridGroup_geometry_42
  · exact gridGroup_geometry_43
  · exact gridGroup_geometry_44
  · exact gridGroup_geometry_45
  · exact gridGroup_geometry_46
  · exact gridGroup_geometry_47
  · exact gridGroup_geometry_48
  · exact gridGroup_geometry_49
  · exact gridGroup_geometry_50
  · exact gridGroup_geometry_51
  · exact gridGroup_geometry_52
  · exact gridGroup_geometry_53
  · exact gridGroup_geometry_54
  · exact gridGroup_geometry_55
  · exact gridGroup_geometry_56
  · exact gridGroup_geometry_57
  · exact gridGroup_geometry_58
  · exact gridGroup_geometry_59
  · exact gridGroup_geometry_60
  · exact gridGroup_geometry_61
  · exact gridGroup_geometry_62
  · exact gridGroup_geometry_63
  · exact gridGroup_geometry_64
  · exact gridGroup_geometry_65
  · exact gridGroup_geometry_66
  · exact gridGroup_geometry_67
  · exact gridGroup_geometry_68
  · exact gridGroup_geometry_69
  · exact gridGroup_geometry_70
  · exact gridGroup_geometry_71
  · exact gridGroup_geometry_72
  · exact gridGroup_geometry_73
  · exact gridGroup_geometry_74
  · exact gridGroup_geometry_75
  · exact gridGroup_geometry_76
  · exact gridGroup_geometry_77
  · exact gridGroup_geometry_78
  · exact gridGroup_geometry_79
  · exact gridGroup_geometry_80
  · exact gridGroup_geometry_81
  · exact gridGroup_geometry_82
  · exact gridGroup_geometry_83
  · exact gridGroup_geometry_84
  · exact gridGroup_geometry_85
  · exact gridGroup_geometry_86
  · exact gridGroup_geometry_87
  · exact gridGroup_geometry_88
  · exact gridGroup_geometry_89
  · exact gridGroup_geometry_90
  · exact gridGroup_geometry_91
  · exact gridGroup_geometry_92
  · exact gridGroup_geometry_93
  · exact gridGroup_geometry_94
  · exact gridGroup_geometry_95
  · exact gridGroup_geometry_96
  · exact gridGroup_geometry_97
  · exact gridGroup_geometry_98
  · exact gridGroup_geometry_99
  · exact gridGroup_geometry_100
  · exact gridGroup_geometry_101
  · exact gridGroup_geometry_102
  · exact gridGroup_geometry_103
  · exact gridGroup_geometry_104
  · exact gridGroup_geometry_105
  · exact gridGroup_geometry_106
  · exact gridGroup_geometry_107
  · exact gridGroup_geometry_108
  · exact gridGroup_geometry_109
  · exact gridGroup_geometry_110
  · exact gridGroup_geometry_111
  · exact gridGroup_geometry_112
  · exact gridGroup_geometry_113
  · exact gridGroup_geometry_114
  · exact gridGroup_geometry_115
  · exact gridGroup_geometry_116
  · exact gridGroup_geometry_117
  · exact gridGroup_geometry_118
  · exact gridGroup_geometry_119
  · exact gridGroup_geometry_120
  · exact gridGroup_geometry_121
  · exact gridGroup_geometry_122
  · exact gridGroup_geometry_123
  · exact gridGroup_geometry_124
  · exact gridGroup_geometry_125
  · exact gridGroup_geometry_126
  · exact gridGroup_geometry_127
  · exact gridGroup_geometry_128
  · exact gridGroup_geometry_129
  · exact gridGroup_geometry_130
  · exact gridGroup_geometry_131
  · exact gridGroup_geometry_132
  · exact gridGroup_geometry_133
  · exact gridGroup_geometry_134
  · exact gridGroup_geometry_135
  · exact gridGroup_geometry_136
  · exact gridGroup_geometry_137
  · exact gridGroup_geometry_138
  · exact gridGroup_geometry_139
  · exact gridGroup_geometry_140
  · exact gridGroup_geometry_141
  · exact gridGroup_geometry_142
  · exact gridGroup_geometry_143
  · exact gridGroup_geometry_144
  · exact gridGroup_geometry_145
  · exact gridGroup_geometry_146
  · exact gridGroup_geometry_147
  · exact gridGroup_geometry_148
  · exact gridGroup_geometry_149
  · exact gridGroup_geometry_150
  · exact gridGroup_geometry_151
  · exact gridGroup_geometry_152
  · exact gridGroup_geometry_153
  · exact gridGroup_geometry_154
  · exact gridGroup_geometry_155
  · exact gridGroup_geometry_156
  · exact gridGroup_geometry_157
  · exact gridGroup_geometry_158
  · exact gridGroup_geometry_159
  · exact gridGroup_geometry_160
  · exact gridGroup_geometry_161
  · exact gridGroup_geometry_162
  · exact gridGroup_geometry_163
  · exact gridGroup_geometry_164
  · exact gridGroup_geometry_165
  · exact gridGroup_geometry_166
  · exact gridGroup_geometry_167
  · exact gridGroup_geometry_168
  · exact gridGroup_geometry_169
  · exact gridGroup_geometry_170
  · exact gridGroup_geometry_171
  · exact gridGroup_geometry_172
  · exact gridGroup_geometry_173
  · exact gridGroup_geometry_174
  · exact gridGroup_geometry_175
  · exact gridGroup_geometry_176
  · exact gridGroup_geometry_177
  · exact gridGroup_geometry_178
  · exact gridGroup_geometry_179
  · exact gridGroup_geometry_180
  · exact gridGroup_geometry_181
  · exact gridGroup_geometry_182
  · exact gridGroup_geometry_183
  · exact gridGroup_geometry_184
  · exact gridGroup_geometry_185
  · exact gridGroup_geometry_186
  · exact gridGroup_geometry_187
  · exact gridGroup_geometry_188
  · exact gridGroup_geometry_189
  · exact gridGroup_geometry_190
  · exact gridGroup_geometry_191
  · exact gridGroup_geometry_192
  · exact gridGroup_geometry_193
  · exact gridGroup_geometry_194
  · exact gridGroup_geometry_195
  · exact gridGroup_geometry_196
  · exact gridGroup_geometry_197
  · exact gridGroup_geometry_198
  · exact gridGroup_geometry_199
  · exact gridGroup_geometry_200
  · exact gridGroup_geometry_201
  · exact gridGroup_geometry_202
  · exact gridGroup_geometry_203
  · exact gridGroup_geometry_204
  · exact gridGroup_geometry_205
  · exact gridGroup_geometry_206
  · exact gridGroup_geometry_207
  · exact gridGroup_geometry_208
  · exact gridGroup_geometry_209
  · exact gridGroup_geometry_210
  · exact gridGroup_geometry_211
  · exact gridGroup_geometry_212
  · exact gridGroup_geometry_213
  · exact gridGroup_geometry_214
  · exact gridGroup_geometry_215
  · exact gridGroup_geometry_216
  · exact gridGroup_geometry_217
  · exact gridGroup_geometry_218
  · exact gridGroup_geometry_219
  · exact gridGroup_geometry_220
  · exact gridGroup_geometry_221
  · exact gridGroup_geometry_222
  · exact gridGroup_geometry_223
  · exact gridGroup_geometry_224
  · exact gridGroup_geometry_225
  · exact gridGroup_geometry_226
  · exact gridGroup_geometry_227
  · exact gridGroup_geometry_228
  · exact gridGroup_geometry_229
  · exact gridGroup_geometry_230
  · exact gridGroup_geometry_231
  · exact gridGroup_geometry_232
  · exact gridGroup_geometry_233
  · exact gridGroup_geometry_234

theorem gridGroup_target_mod (i : Fin 235) :
    gridGroupPartner i%780=((gridGroupTarget i:ℕ):ℤ) := by
  fin_cases i <;> decide

theorem gridGroup_rate_pos (i : Fin 235) : 0<gridGroupRate i := by
  have hn : (sourceRaw (gridGroupSource i) 1 0:ℝ)*(((gridGroupIndex i:ℕ):ℝ)/780)+
      (sourceRaw (gridGroupSource i) 1 1:ℝ)≠0 := by
    simpa only [mul_div_assoc] using (gridGroup_geometry i).1
  have hp : 0<sourceRate (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780) :=
    div_pos (sq_pos_of_ne_zero hn) (by exact_mod_cast source_det_pos (gridGroupSource i))
  rw [(gridGroup_geometry i).2.2.1] at hp
  exact_mod_cast hp

theorem gridGroup_partner_transform (k : ℕ) (f : ℕ→ℂ) (i : Fin 235) (s : ℂ) :
    original k f (sourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780)) s=
      grid k f 780 ((gridGroupTarget i:ℕ):ℤ) s := by
  rw [(gridGroup_geometry i).2.1]
  change grid k f 780 (gridGroupPartner i) s=_
  rw [← grid_mod k f (by decide : 0<780)]
  norm_num only [Nat.cast_ofNat]
  rw [gridGroup_target_mod]

#print axioms gridGroup_geometry
#print axioms gridGroup_partner_transform

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermMatrixRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessNormalizedTwistProduct
open SmallLevelAdditive Complex Set
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

def gridMatrixScalar (m : ℕ) (f : ℕ→ℂ) (η : ℂ) (i : Fin 235) (n : ℕ) (s : ℂ) : ℂ :=
  gridWordSign (root 26 f 2) η (sourceWord (gridGroupSource i))*(gridGroupRate i:ℂ)^(s-(m:ℂ))*
    (Complex.I*(gridGroupDerivative i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- The 235 selected matrix rows of the actual closed 780-grid system.
The leading term and every positive shift use the same grid coordinate. -/
theorem grid_matrix_rows_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 26 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 235) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 780 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m f η i 0 s*
            grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m f η i (n+1) s*
          grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  obtain ⟨B,error,hrows⟩:=source_taylor_of_fricke m hf hη hW
    (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780) (by
      simpa only [mul_div_assoc] using (gridGroup_geometry i).1)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrows (M+1)).1
  intro s hs
  have hh:=(hrows (M+1)).2 s hs
  simp_rw [gridGroup_partner_transform] at hh
  rw [(gridGroup_geometry i).2.2.1,(gridGroup_geometry i).2.2.2,
    Finset.sum_range_succ'] at hh
  simp only [Complex.ofReal_ratCast,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,one_mul,Nat.cast_add,Nat.cast_one] at hh
  simp only [gridMatrixScalar,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
  rw [mul_add,Finset.mul_sum] at hh
  simp only [← mul_assoc] at hh
  simp only [grid,Int.cast_natCast,Nat.cast_ofNat] at hh ⊢
  linear_combination hh

#print axioms grid_matrix_rows_of_fricke
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermRamanujanV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct

def gridTaylorL (i : Fin 53) : ℕ := Nat.lcm 26 ((gridTaylorQ i)^2)
def gridTaylorD (i : Fin 53) : ℤ := (780:ℤ)^2/(gridTaylorL i:ℤ)
def gridTaylorPartner (i : Fin 53) : ℤ := -(gridTaylorD i/gridTaylorT i)

theorem gridTaylorSpecs_valid : ∀ i : Fin 53,
    0<gridTaylorQ i ∧ gridTaylorQ i∣780 ∧ gridTaylorT i≠0 ∧
      (gridTaylorL i:ℤ)*gridTaylorD i=(780:ℤ)^2 ∧ gridTaylorT i∣gridTaylorD i := by decide

def gridTaylorCoefficient (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 53) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar (2*m) (gridTaylorL i) ((gridTaylorT i:ℝ)/780)
    (root 26 f (gridTaylorQ i)*ε*I^(2*m)) n s

def gridTaylorError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 53) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError (2*m) (fullCoefficients (twisted f (gridTaylorQ i)) (2*m))
    (gridTaylorL i) ((gridTaylorT i:ℝ)/780) (root 26 f (gridTaylorQ i)*ε*I^(2*m)) (M+1)) s

theorem grid_ramanujan_rows_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (i : Fin 53) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/780≠0:=div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : 0<gridTaylorL i:=Nat.lcm_pos (by decide) (pow_pos hv.1 _)
  obtain ⟨B,hB⟩:=grid_ramanujan_taylor_of_laws m hf hlaw (gridTaylorQ i) hv.1 _ hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · intro s hs
    unfold gridTaylorError gridTaylorL
    apply (hB (M+1)).1 s
    change B-((M+1:ℕ):ℝ)<s.re
    change B-((M:ℝ)+1)<s.re at hs
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  · intro s hs
    have hm:=(hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at hm
    rw [show Nat.lcm 26 ((gridTaylorQ i)^2)=gridTaylorL i from rfl] at hm
    have htrans:=ramanujanAdditive_grid (2*m) f (by decide : 0<780) hv.1 hv.2.1 (gridTaylorT i) s
    norm_num only [Nat.cast_ofNat] at htrans
    rw [htrans] at hm
    have hp:=fricke_grid_partner (by decide : 0<780) hL hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    norm_num only [Nat.cast_ofNat] at hp
    rw [hp] at hm
    have hgrid (t : ℤ) (w : ℂ) :
        ramanujanAdditive (2*m) f (gridTaylorQ i) ((t:ℝ)/780) w=
          ∑ j∈FinitenessRamanujanSum.residues (gridTaylorQ i),
            grid (2*m) f 780 (t+(j:ℤ)*(780/gridTaylorQ i:ℕ)) w := by
      simpa only [Nat.cast_ofNat] using
        ramanujanAdditive_grid (2*m) f (by decide : 0<780) hv.1 hv.2.1 t w
    simp_rw [hgrid] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    unfold gridTaylorCoefficient gridTaylorError gridTaylorPartner gridSum
    linear_combination hm

/-- All selected Ramanujan rows share a half-plane and the specified sign. -/
theorem grid_ramanujan_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∀ i : Fin 53, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  choose b hb using grid_ramanujan_rows_of_laws m hf hlaw
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 53) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridTaylorSpecs_valid
#print axioms grid_ramanujan_rows_of_laws
#print axioms grid_ramanujan_system_of_laws
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermMatrixSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive SmallLevelTaylor
open scoped ModularForm

/-- Every coefficient of every positive shift is entire. -/
theorem gridMatrixScalar_analytic (m : ℕ) (f : ℕ→ℂ) (η : ℂ)
    (i : Fin 235) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridMatrixScalar m f η i n) s := by
  have hn : (gridGroupRate i:ℂ)≠0 := by exact_mod_cast (gridGroup_rate_pos i).ne'
  have hp : AnalyticAt ℂ (fun z : ℂ => (gridGroupRate i:ℂ)^(z-(m:ℂ))) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (binomial_shift_analytic (2*m) n s)

theorem gridTaylorCoefficient_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (i : Fin 53) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridTaylorCoefficient m f ε i n) s := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/780≠0 := div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : (0:ℝ)<gridTaylorL i := by
    exact_mod_cast (Nat.lcm_pos (by decide : 0<26) (pow_pos hv.1 2))
  exact taylorRowScalar_analytic (2*m) hL hr _ n s

/-- All235 word rows share one half-plane and the original coherent sign. -/
theorem grid_matrix_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (error : Fin 235→ℕ→ℂ→ℂ), ∀ i : Fin 235, ∀ M : ℕ,
      AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        grid (2*m) f 780 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m f (ε*I^(2*m)) i 0 s*
            grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) s=
        error i M s+∑ n∈Finset.range M,gridMatrixScalar m f (ε*I^(2*m)) i (n+1) s*
          grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  choose b error hb using grid_matrix_rows_of_fricke m hf (grid_physical_sign m hε)
    (grid_fricke_of_laws m hε hlaw)
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 235) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,error,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridMatrixScalar_analytic
#print axioms gridTaylorCoefficient_analytic
#print axioms grid_matrix_system_of_laws
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermEntireRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Matrix Complex Set SmallLevelAdditive SmallLevelTaylor
open SmallLevelOriginal SmallLevelNormalized FinitenessOriginalInput
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

def gridEntireQ : Fin 11→ℕ := ![3,4,5,6,10,13,15,20,30,39,78]

theorem gridEntireQ_valid (i : Fin 11) : 0<gridEntireQ i ∧ gridEntireQ i∣780 := by
  fin_cases i <;> decide

/-- The11 unshifted Ramanujan sources are entire and agree with the grid sums. -/
theorem grid_ramanujan_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 26 (2*m) f) (i : Fin 11) :
    (∀ s : ℂ,AnalyticAt ℂ (ramanujanEntire 26 (2*m) f (gridEntireQ i)) s) ∧
    ∃ B : ℝ,∀ s : ℂ,B<s.re →
      ramanujanEntire 26 (2*m) f (gridEntireQ i) s=gridSum (2*m) f 780 (gridEntireQ i) 0 s := by
  obtain ⟨ha,B,hB⟩:=original_ramanujan_entire (by decide : 0<26) (by omega : 0<2*m)
    hf (gridEntireQ_valid i).1
  refine ⟨ha,B,?_⟩
  intro s hs
  rw [hB s hs]
  simpa only [gridSum,Int.cast_zero,zero_div] using
    ramanujanAdditive_grid (2*m) f (by decide : 0<780)
      (gridEntireQ_valid i).1 (gridEntireQ_valid i).2 (0:ℤ) s

theorem source_scale_ne_zero (i : Fin 32) :
    wordScale (sourceWord i)*(sourceMultiple i:ℝ)≠0 := by
  intro h
  have hd:=gridWord_det (sourceWord i)
  change (gridWord (sourceWord i)).val.det=1 at hd
  rw [source_coordinates,h,zero_smul] at hd
  norm_num at hd

theorem source_word_nonaffine (i : Fin 32) :
    (gridWord (sourceWord i)).val 1 0≠0 := by
  rw [source_coordinates]
  change (wordScale (sourceWord i)*(sourceMultiple i:ℝ))*(sourceRaw i 1 0:ℝ)≠0
  exact mul_ne_zero (source_scale_ne_zero i) (by exact_mod_cast source_nonaffine i)

def gridInfinitySource : Fin 2→Fin 32 := ![15,23]
def gridInfinityIndex : Fin 2→Fin 780 := ![10,60]

theorem gridInfinity_geometry (i : Fin 2) :
    (sourceRaw (gridInfinitySource i) 1 0:ℝ)*((gridInfinityIndex i:ℕ):ℝ)/780+
      (sourceRaw (gridInfinitySource i) 1 1:ℝ)=0 := by
  fin_cases i <;> norm_num [gridInfinitySource,gridInfinityIndex,sourceRaw]

/-- Both source-to-infinity rows come from original Fourier laws. -/
theorem grid_infinity_entire_of_fricke (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 26 (2*m) f) {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (i : Fin 2) :
    Differentiable ℂ (sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/780)) := by
  apply word_source_entire_of_fricke m hm hf hη hW (sourceWord (gridInfinitySource i))
    _ (source_word_nonaffine _)
  rw [source_coordinates]
  change (wordScale _*(sourceMultiple _:ℝ))*(sourceRaw _ 1 0:ℝ)*
    (((gridInfinityIndex i:ℕ):ℝ)/780)+(wordScale _*(sourceMultiple _:ℝ))*(sourceRaw _ 1 1:ℝ)=0
  have hh:=gridInfinity_geometry i
  rw [mul_div_assoc] at hh
  linear_combination (wordScale (sourceWord (gridInfinitySource i))*(sourceMultiple (gridInfinitySource i):ℝ))*hh

#print axioms grid_ramanujan_entire
#print axioms grid_infinity_entire_of_fricke
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermHeckeSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open Complex Set SmallLevelAdditive SmallLevelPrimeRates

def gridHeckeSpecs : Fin 96→ℕ×ℤ :=
  ![(2,7),(2,8),(2,9),(2,11),(2,16),(2,22),(2,24),(2,25),(2,42),(2,48),(2,50),(2,52),(2,55),(2,66),(2,75),(2,80),(2,95),(2,100),(2,104),(2,105),(2,120),(2,143),(2,150),(2,156),(2,160),(2,162),(2,165),(2,170),(2,185),(2,205),(2,228),(2,230),(2,234),(2,235),(2,247),(2,250),(2,280),(2,286),(2,295),(2,312),(2,315),(2,340),(2,342),(2,350),(2,359),(2,363),(2,368),(2,377),(2,382),(3,13),(3,25),(3,26),(3,30),(3,35),(3,40),(3,50),(3,52),(3,55),(3,65),(3,70),(3,75),(3,78),(3,90),(3,95),(3,100),(3,104),(3,105),(3,110),(3,117),(3,143),(3,150),(3,155),(3,160),(3,165),(3,170),(3,180),(3,182),(3,185),(3,190),(3,195),(3,200),(3,205),(3,208),(3,210),(3,220),(3,225),(3,230),(3,234),(3,235),(3,247),(5,26),(5,39),(5,52),(5,104),(5,117),(5,130)]
def gridHeckeP (i : Fin 96) : ℕ := (gridHeckeSpecs i).1
def gridHeckeT (i : Fin 96) : ℤ := (gridHeckeSpecs i).2

theorem gridHeckeSpecs_valid (i : Fin 96) :
    (gridHeckeP i).Prime ∧ gridHeckeP i∣780 := by
  fin_cases i <;> decide

def gridHeckeRow (m : ℕ) (f : ℕ→ℂ) (i : Fin 96) (s : ℂ) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),grid (2*m) f 780
    (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ)) s)-
    ((Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i))*(parameter (gridHeckeP i) m s)⁻¹*
      grid (2*m) f 780 ((gridHeckeP i:ℤ)*gridHeckeT i) s+
    (if gridHeckeP i∣26 then 0 else ((parameter (gridHeckeP i) m s)⁻¹)^2*
      grid (2*m) f 780 ((gridHeckeP i:ℤ)^2*gridHeckeT i) s)

/-- All96 prime equations, including both ramified and both good primes. -/
theorem original_grid_hecke_row (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (i : Fin 96) :
    ∃ B : ℝ,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  have hv:=gridHeckeSpecs_valid i
  by_cases hb : gridHeckeP i∣26
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_ramified_rows hf hm hv.1 hb
      (by decide : 0<780) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_left hb,add_zero] using hB (gridHeckeT i) s hs⟩
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_good_rows hf hv.1 hb
      (by decide : 0<780) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_right hb] using hB (gridHeckeT i) s hs⟩

theorem original_grid_hecke_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ,∀ i : Fin 96,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  choose b hb using original_grid_hecke_row m hm hf
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 96) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  exact ⟨B,fun i s hs => hb i s (lt_of_le_of_lt (hbB i) hs)⟩

#print axioms original_grid_hecke_system
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermAssemblyV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive SmallLevelTaylor FinitenessRamanujanSum SmallLevelPrimeRates

def gridSample (q : ℕ) (t : ℤ) (w : Fin 780→ℂ) : ℂ :=
  ∑ j∈residues q,w (gridIndex (t+(j:ℤ)*(780/q:ℕ)))

def gridVector (k : ℕ) (f : ℕ→ℂ) (s : ℂ) : Fin 780→ℂ :=
  fun j => grid k f 780 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ→ℂ) (s : ℂ) (t : ℤ) :
    gridVector k f s (gridIndex t)=grid k f 780 t s := by
  unfold gridVector
  have he : ((gridIndex t).val:ℤ)=t%780:=Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<780) t s

theorem gridSample_grid (k : ℕ) (f : ℕ→ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    gridSample q t (gridVector k f s)=gridSum k f 780 q t s := by
  unfold gridSample gridSum
  simp_rw [gridVector_index]

theorem gridSample_add (q : ℕ) (t : ℤ) (w v : Fin 780→ℂ) :
    gridSample q t (w+v)=gridSample q t w+gridSample q t v := by
  simp [gridSample,Finset.sum_add_distrib]

theorem gridSample_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 780→ℂ) :
    gridSample q t (c • w)=c*gridSample q t w := by
  simp [gridSample,Finset.mul_sum]


def gridGroupLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) (i : Fin 235) : ℂ :=
  v (gridGroupIndex i)-gridMatrixScalar m f (ε*I^(2*m)) i 0 s*v (gridGroupTarget i)

def gridRamanujanLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) (i : Fin 53) : ℂ :=
  gridSample (gridTaylorQ i) (gridTaylorT i) v-
    gridTaylorCoefficient m f ε i 0 s*gridSample (gridTaylorQ i) (gridTaylorPartner i) v

def gridHeckeLeading (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) (i : Fin 96) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),v (gridIndex (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ))))-
    ((Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i))*(parameter (gridHeckeP i) m s)⁻¹*
      v (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i))+
    (if gridHeckeP i∣26 then 0 else ((parameter (gridHeckeP i) m s)⁻¹)^2*
      v (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i)))

def gridLeadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) : GridSource→ℂ
  | .word i => gridGroupLeading m f ε s v i
  | .taylor i => gridRamanujanLeading m f ε s v i
  | .entire i => gridSample (gridEntireQ i) 0 v
  | .hecke i => gridHeckeLeading m f s v i
  | .infinity i => v (gridInfinityIndex i)

def gridShiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 780→ℂ) : GridSource→ℂ
  | .word i => gridMatrixScalar m f (ε*I^(2*m)) i (n+1) s*v (gridGroupTarget i)
  | .taylor i => gridTaylorCoefficient m f ε i (n+1) s*gridSample (gridTaylorQ i) (gridTaylorPartner i) v
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem gridHeckeLeading_grid (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 96) :
    gridHeckeLeading m f s (gridVector (2*m) f s) i=gridHeckeRow m f i s := by
  simp only [gridHeckeLeading,gridHeckeRow,gridVector_index]

#print axioms gridVector_index
#print axioms gridSample_grid
#print axioms gridHeckeLeading_grid
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermShiftSupportDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

def groupTargetSupport : Fin 235→Fin 320 :=
  ![308,10,15,35,63,252,272,289,293,302,306,307,309,310,273,274,276,259,260,160,166,170,175,178,187,197,198,203,207,211,218,222,228,233,250,272,28,84,211,237,71,99,222,258,0,49,80,84,92,99,102,103,106,110,111,113,114,115,118,119,121,122,123,124,125,126,127,128,129,130,131,291,287,290,187,193,195,198,200,201,203,205,208,209,211,213,217,219,222,224,229,233,239,242,248,267,49,60,88,102,160,218,233,0,73,0,160,88,160,0,160,160,0,160,233,160,248,88,103,219,233,261,189,250,59,40,279,280,282,285,288,75,82,84,211,103,134,215,229,241,244,247,252,253,255,256,259,260,263,264,265,266,268,269,270,296,315,292,102,233,0,160,0,0,0,293,294,0,0,0,160,222,227,232,251,254,29,297,176,244,27,84,110,237,272,99,222,239,246,55,61,28,49,53,196,211,232,84,105,121,147,150,110,203,248,14,303,304,305,311,61,228,250,264,283,286,295,298,299,300,301,185,198,178,184,203,276,277,278,281,283,0,262,272,275]

theorem groupTargetSupport_spec (i : Fin 235) :
    support (groupTargetSupport i)=gridGroupTarget i := by
  fin_cases i <;> rfl

theorem groupTarget_restrict (v : Fin 780→ℂ) (i : Fin 235) :
    extension support (fun j => v (support j)) (gridGroupTarget i)=v (gridGroupTarget i) := by
  rw [←groupTargetSupport_spec]
  exact extend_at support support_injective (fun t => v (support t)) (groupTargetSupport i)

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermShiftSupportBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorTarget_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 0) (gridTaylorPartner 0) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 0) (gridTaylorPartner 0) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 0=3 from rfl,show gridTaylorPartner 0=(-260:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 1) (gridTaylorPartner 1) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 1) (gridTaylorPartner 1) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 1=3 from rfl,show gridTaylorPartner 1=(260:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 2) (gridTaylorPartner 2) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 2) (gridTaylorPartner 2) v := by
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  simp only [show gridTaylorQ 2=3 from rfl,show gridTaylorPartner 2=(-200:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h60,h320]

theorem taylorTarget_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 3) (gridTaylorPartner 3) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 3) (gridTaylorPartner 3) v := by
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 3=3 from rfl,show gridTaylorPartner 3=(200:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h460,h720]

theorem taylorTarget_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 4) (gridTaylorPartner 4) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 4) (gridTaylorPartner 4) v := by
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 4=3 from rfl,show gridTaylorPartner 4=(-130:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h130,h390]

theorem taylorTarget_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 5) (gridTaylorPartner 5) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 5) (gridTaylorPartner 5) v := by
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 5=3 from rfl,show gridTaylorPartner 5=(130:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h390,h650]

theorem taylorTarget_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 6) (gridTaylorPartner 6) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 6) (gridTaylorPartner 6) v := by
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h416 : extension support (fun t => v (support t)) 416=v 416 :=
    extend_at support support_injective (fun t => v (support t)) 183
  simp only [show gridTaylorQ 6=3 from rfl,show gridTaylorPartner 6=(-104:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h156,h416]

theorem taylorTarget_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 7) (gridTaylorPartner 7) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 7) (gridTaylorPartner 7) v := by
  have h364 : extension support (fun t => v (support t)) 364=v 364 :=
    extend_at support support_injective (fun t => v (support t)) 138
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 7=3 from rfl,show gridTaylorPartner 7=(104:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h364,h624]

theorem taylorTarget_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 8) (gridTaylorPartner 8) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 8) (gridTaylorPartner 8) v := by
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  simp only [show gridTaylorQ 8=3 from rfl,show gridTaylorPartner 8=(-100:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h160,h420]

theorem taylorTarget_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 9) (gridTaylorPartner 9) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 9) (gridTaylorPartner 9) v := by
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  simp only [show gridTaylorQ 9=3 from rfl,show gridTaylorPartner 9=(100:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h360,h620]

theorem taylorTarget_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 10) (gridTaylorPartner 10) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 10) (gridTaylorPartner 10) v := by
  have h195 : extension support (fun t => v (support t)) 195=v 195 :=
    extend_at support support_injective (fun t => v (support t)) 88
  have h455 : extension support (fun t => v (support t)) 455=v 455 :=
    extend_at support support_injective (fun t => v (support t)) 205
  simp only [show gridTaylorQ 10=3 from rfl,show gridTaylorPartner 10=(-65:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h195,h455]

theorem taylorTarget_restrict_11 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 11) (gridTaylorPartner 11) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 11) (gridTaylorPartner 11) v := by
  have h325 : extension support (fun t => v (support t)) 325=v 325 :=
    extend_at support support_injective (fun t => v (support t)) 116
  have h585 : extension support (fun t => v (support t)) 585=v 585 :=
    extend_at support support_injective (fun t => v (support t)) 233
  simp only [show gridTaylorQ 11=3 from rfl,show gridTaylorPartner 11=(65:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h325,h585]

theorem taylorTarget_restrict_12 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 12) (gridTaylorPartner 12) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 12) (gridTaylorPartner 12) v := by
  have h208 : extension support (fun t => v (support t)) 208=v 208 :=
    extend_at support support_injective (fun t => v (support t)) 91
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  simp only [show gridTaylorQ 12=3 from rfl,show gridTaylorPartner 12=(-52:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h208,h468]

theorem taylorTarget_restrict_13 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 13) (gridTaylorPartner 13) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 13) (gridTaylorPartner 13) v := by
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h572 : extension support (fun t => v (support t)) 572=v 572 :=
    extend_at support support_injective (fun t => v (support t)) 230
  simp only [show gridTaylorQ 13=3 from rfl,show gridTaylorPartner 13=(52:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h312,h572]

theorem taylorTarget_restrict_14 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 14) (gridTaylorPartner 14) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 14) (gridTaylorPartner 14) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 14=4 from rfl,show gridTaylorPartner 14=(-585:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_15 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 15) (gridTaylorPartner 15) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 15) (gridTaylorPartner 15) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 15=4 from rfl,show gridTaylorPartner 15=(585:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_16 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 16) (gridTaylorPartner 16) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 16) (gridTaylorPartner 16) v := by
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 16=4 from rfl,show gridTaylorPartner 16=(-225:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h360,h750]

theorem taylorTarget_restrict_17 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 17) (gridTaylorPartner 17) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 17) (gridTaylorPartner 17) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  simp only [show gridTaylorQ 17=4 from rfl,show gridTaylorPartner 17=(225:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h420]

theorem taylorTarget_restrict_18 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 18) (gridTaylorPartner 18) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 18) (gridTaylorPartner 18) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 18=4 from rfl,show gridTaylorPartner 18=(-195:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_19 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 19) (gridTaylorPartner 19) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 19) (gridTaylorPartner 19) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 19=4 from rfl,show gridTaylorPartner 19=(195:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_20 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 20) (gridTaylorPartner 20) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 20) (gridTaylorPartner 20) v := by
  have h78 : extension support (fun t => v (support t)) 78=v 78 :=
    extend_at support support_injective (fun t => v (support t)) 60
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  simp only [show gridTaylorQ 20=4 from rfl,show gridTaylorPartner 20=(-117:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h78,h468]

theorem taylorTarget_restrict_21 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 21) (gridTaylorPartner 21) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 21) (gridTaylorPartner 21) v := by
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h702 : extension support (fun t => v (support t)) 702=v 702 :=
    extend_at support support_injective (fun t => v (support t)) 261
  simp only [show gridTaylorQ 21=4 from rfl,show gridTaylorPartner 21=(117:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h312,h702]

theorem taylorTarget_restrict_22 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 22) (gridTaylorPartner 22) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 22) (gridTaylorPartner 22) v := by
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  simp only [show gridTaylorQ 22=4 from rfl,show gridTaylorPartner 22=(-75:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h120,h510]

theorem taylorTarget_restrict_23 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 23) (gridTaylorPartner 23) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 23) (gridTaylorPartner 23) v := by
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  simp only [show gridTaylorQ 23=4 from rfl,show gridTaylorPartner 23=(75:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h270,h660]

theorem taylorTarget_restrict_24 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 24) (gridTaylorPartner 24) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 24) (gridTaylorPartner 24) v := by
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 24=4 from rfl,show gridTaylorPartner 24=(-65:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h130,h520]

theorem taylorTarget_restrict_25 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 25) (gridTaylorPartner 25) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 25) (gridTaylorPartner 25) v := by
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 25=4 from rfl,show gridTaylorPartner 25=(65:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h260,h650]

theorem taylorTarget_restrict_26 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 26) (gridTaylorPartner 26) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 26) (gridTaylorPartner 26) v := by
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  simp only [show gridTaylorQ 26=4 from rfl,show gridTaylorPartner 26=(-45:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h150,h540]

theorem taylorTarget_restrict_27 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 27) (gridTaylorPartner 27) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 27) (gridTaylorPartner 27) v := by
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h546 : extension support (fun t => v (support t)) 546=v 546 :=
    extend_at support support_injective (fun t => v (support t)) 224
  simp only [show gridTaylorQ 27=4 from rfl,show gridTaylorPartner 27=(-39:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h156,h546]

theorem taylorTarget_restrict_28 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 28) (gridTaylorPartner 28) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 28) (gridTaylorPartner 28) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 28=6 from rfl,show gridTaylorPartner 28=(-650:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_29 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 29) (gridTaylorPartner 29) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 29) (gridTaylorPartner 29) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 29=6 from rfl,show gridTaylorPartner 29=(650:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_30 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 30) (gridTaylorPartner 30) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 30) (gridTaylorPartner 30) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 30=6 from rfl,show gridTaylorPartner 30=(-130:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_31 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 31) (gridTaylorPartner 31) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 31) (gridTaylorPartner 31) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 31=6 from rfl,show gridTaylorPartner 31=(130:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_32 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 32) (gridTaylorPartner 32) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 32) (gridTaylorPartner 32) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  simp only [show gridTaylorQ 32=6 from rfl,show gridTaylorPartner 32=(-100:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h550]

theorem taylorTarget_restrict_33 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 33) (gridTaylorPartner 33) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 33) (gridTaylorPartner 33) v := by
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 33=6 from rfl,show gridTaylorPartner 33=(100:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h230,h750]

theorem taylorTarget_restrict_34 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 34) (gridTaylorPartner 34) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 34) (gridTaylorPartner 34) v := by
  have h65 : extension support (fun t => v (support t)) 65=v 65 :=
    extend_at support support_injective (fun t => v (support t)) 54
  have h585 : extension support (fun t => v (support t)) 585=v 585 :=
    extend_at support support_injective (fun t => v (support t)) 233
  simp only [show gridTaylorQ 34=6 from rfl,show gridTaylorPartner 34=(-65:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h65,h585]

theorem taylorTarget_restrict_35 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 35) (gridTaylorPartner 35) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 35) (gridTaylorPartner 35) v := by
  have h195 : extension support (fun t => v (support t)) 195=v 195 :=
    extend_at support support_injective (fun t => v (support t)) 88
  have h715 : extension support (fun t => v (support t)) 715=v 715 :=
    extend_at support support_injective (fun t => v (support t)) 267
  simp only [show gridTaylorQ 35=6 from rfl,show gridTaylorPartner 35=(65:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h195,h715]

theorem taylorTarget_restrict_36 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 36) (gridTaylorPartner 36) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 36) (gridTaylorPartner 36) v := by
  have h78 : extension support (fun t => v (support t)) 78=v 78 :=
    extend_at support support_injective (fun t => v (support t)) 60
  have h598 : extension support (fun t => v (support t)) 598=v 598 :=
    extend_at support support_injective (fun t => v (support t)) 236
  simp only [show gridTaylorQ 36=6 from rfl,show gridTaylorPartner 36=(-52:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h78,h598]

theorem taylorTarget_restrict_37 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 37) (gridTaylorPartner 37) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 37) (gridTaylorPartner 37) v := by
  have h182 : extension support (fun t => v (support t)) 182=v 182 :=
    extend_at support support_injective (fun t => v (support t)) 85
  have h702 : extension support (fun t => v (support t)) 702=v 702 :=
    extend_at support support_injective (fun t => v (support t)) 261
  simp only [show gridTaylorQ 37=6 from rfl,show gridTaylorPartner 37=(52:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h182,h702]

theorem taylorTarget_restrict_38 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 38) (gridTaylorPartner 38) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 38) (gridTaylorPartner 38) v := by
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  simp only [show gridTaylorQ 38=6 from rfl,show gridTaylorPartner 38=(-50:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h80,h600]

theorem taylorTarget_restrict_39 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 39) (gridTaylorPartner 39) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 39) (gridTaylorPartner 39) v := by
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  simp only [show gridTaylorQ 39=6 from rfl,show gridTaylorPartner 39=(50:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h180,h700]

theorem taylorTarget_restrict_40 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 40) (gridTaylorPartner 40) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 40) (gridTaylorPartner 40) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 40=10 from rfl,show gridTaylorPartner 40=(-78:ℤ) from rfl,
    gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h156,h468,h624]

theorem taylorTarget_restrict_41 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 41) (gridTaylorPartner 41) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 41) (gridTaylorPartner 41) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 41=10 from rfl,show gridTaylorPartner 41=(78:ℤ) from rfl,
    gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h156,h312,h624]

theorem taylorTarget_restrict_42 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 42) (gridTaylorPartner 42) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 42) (gridTaylorPartner 42) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 42=12 from rfl,show gridTaylorPartner 42=(-325:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h130,h390,h520]

theorem taylorTarget_restrict_43 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 43) (gridTaylorPartner 43) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 43) (gridTaylorPartner 43) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 43=12 from rfl,show gridTaylorPartner 43=(325:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260,h390,h650]

theorem taylorTarget_restrict_44 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 44) (gridTaylorPartner 44) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 44) (gridTaylorPartner 44) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 44=12 from rfl,show gridTaylorPartner 44=(-65:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260,h390,h650]

theorem taylorTarget_restrict_45 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 45) (gridTaylorPartner 45) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 45) (gridTaylorPartner 45) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 45=12 from rfl,show gridTaylorPartner 45=(65:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h130,h390,h520]

theorem taylorTarget_restrict_46 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 46) (gridTaylorPartner 46) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 46) (gridTaylorPartner 46) v := by
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h430 : extension support (fun t => v (support t)) 430=v 430 :=
    extend_at support support_injective (fun t => v (support t)) 196
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  simp only [show gridTaylorQ 46=12 from rfl,show gridTaylorPartner 46=(-25:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h40,h300,h430,h690]

theorem taylorTarget_restrict_47 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 47) (gridTaylorPartner 47) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 47) (gridTaylorPartner 47) v := by
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  simp only [show gridTaylorQ 47=12 from rfl,show gridTaylorPartner 47=(25:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h90,h350,h480,h740]

theorem taylorTarget_restrict_48 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 48) (gridTaylorPartner 48) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 48) (gridTaylorPartner 48) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 48=13 from rfl,show gridTaylorPartner 48=(-180:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h300,h360,h420,h480,h540,h660,h720]

theorem taylorTarget_restrict_49 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 49) (gridTaylorPartner 49) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 49) (gridTaylorPartner 49) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 49=13 from rfl,show gridTaylorPartner 49=(-90:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h90,h150,h210,h270,h330,h390,h450,h510,h570,h630,h750]

theorem taylorTarget_restrict_50 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 50) (gridTaylorPartner 50) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 50) (gridTaylorPartner 50) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  simp only [show gridTaylorQ 50=13 from rfl,show gridTaylorPartner 50=(-60:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h300,h360,h420,h480,h540,h600,h660]

theorem taylorTarget_restrict_51 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 51) (gridTaylorPartner 51) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 51) (gridTaylorPartner 51) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 51=52 from rfl,show gridTaylorPartner 51=(-45:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h30,h60,h90,h120,h180,h210,h240,h270,h300,h330,h360,h390,h420,h450,h480,h510,h570,h600,h630,h660,h690,h720,h750]

theorem taylorTarget_restrict_52 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 52) (gridTaylorPartner 52) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 52) (gridTaylorPartner 52) v := by
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h50 : extension support (fun t => v (support t)) 50=v 50 :=
    extend_at support support_injective (fun t => v (support t)) 40
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h110 : extension support (fun t => v (support t)) 110=v 110 :=
    extend_at support support_injective (fun t => v (support t)) 69
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h170 : extension support (fun t => v (support t)) 170=v 170 :=
    extend_at support support_injective (fun t => v (support t)) 83
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h290 : extension support (fun t => v (support t)) 290=v 290 :=
    extend_at support support_injective (fun t => v (support t)) 108
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h410 : extension support (fun t => v (support t)) 410=v 410 :=
    extend_at support support_injective (fun t => v (support t)) 178
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h470 : extension support (fun t => v (support t)) 470=v 470 :=
    extend_at support support_injective (fun t => v (support t)) 210
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h530 : extension support (fun t => v (support t)) 530=v 530 :=
    extend_at support support_injective (fun t => v (support t)) 220
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h710 : extension support (fun t => v (support t)) 710=v 710 :=
    extend_at support support_injective (fun t => v (support t)) 264
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  have h770 : extension support (fun t => v (support t)) 770=v 770 :=
    extend_at support support_injective (fun t => v (support t)) 311
  simp only [show gridTaylorQ 52=52 from rfl,show gridTaylorPartner 52=(5:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h20,h50,h80,h110,h140,h170,h230,h260,h290,h320,h350,h380,h410,h440,h470,h500,h530,h560,h620,h650,h680,h710,h740,h770]

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermShiftSupportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorTarget_restrict (v : Fin 780→ℂ) (i : Fin 53) :
    gridSample (gridTaylorQ i) (gridTaylorPartner i) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ i) (gridTaylorPartner i) v := by
  fin_cases i
  · exact taylorTarget_restrict_0 v
  · exact taylorTarget_restrict_1 v
  · exact taylorTarget_restrict_2 v
  · exact taylorTarget_restrict_3 v
  · exact taylorTarget_restrict_4 v
  · exact taylorTarget_restrict_5 v
  · exact taylorTarget_restrict_6 v
  · exact taylorTarget_restrict_7 v
  · exact taylorTarget_restrict_8 v
  · exact taylorTarget_restrict_9 v
  · exact taylorTarget_restrict_10 v
  · exact taylorTarget_restrict_11 v
  · exact taylorTarget_restrict_12 v
  · exact taylorTarget_restrict_13 v
  · exact taylorTarget_restrict_14 v
  · exact taylorTarget_restrict_15 v
  · exact taylorTarget_restrict_16 v
  · exact taylorTarget_restrict_17 v
  · exact taylorTarget_restrict_18 v
  · exact taylorTarget_restrict_19 v
  · exact taylorTarget_restrict_20 v
  · exact taylorTarget_restrict_21 v
  · exact taylorTarget_restrict_22 v
  · exact taylorTarget_restrict_23 v
  · exact taylorTarget_restrict_24 v
  · exact taylorTarget_restrict_25 v
  · exact taylorTarget_restrict_26 v
  · exact taylorTarget_restrict_27 v
  · exact taylorTarget_restrict_28 v
  · exact taylorTarget_restrict_29 v
  · exact taylorTarget_restrict_30 v
  · exact taylorTarget_restrict_31 v
  · exact taylorTarget_restrict_32 v
  · exact taylorTarget_restrict_33 v
  · exact taylorTarget_restrict_34 v
  · exact taylorTarget_restrict_35 v
  · exact taylorTarget_restrict_36 v
  · exact taylorTarget_restrict_37 v
  · exact taylorTarget_restrict_38 v
  · exact taylorTarget_restrict_39 v
  · exact taylorTarget_restrict_40 v
  · exact taylorTarget_restrict_41 v
  · exact taylorTarget_restrict_42 v
  · exact taylorTarget_restrict_43 v
  · exact taylorTarget_restrict_44 v
  · exact taylorTarget_restrict_45 v
  · exact taylorTarget_restrict_46 v
  · exact taylorTarget_restrict_47 v
  · exact taylorTarget_restrict_48 v
  · exact taylorTarget_restrict_49 v
  · exact taylorTarget_restrict_50 v
  · exact taylorTarget_restrict_51 v
  · exact taylorTarget_restrict_52 v

theorem shiftRows_restrict (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s (extension support (fun j => v (support j))) i=
      gridShiftRows m f ε n s v i := by
  cases i <;> simp only [gridShiftRows,groupTarget_restrict,taylorTarget_restrict]

#print axioms groupTargetSupport_spec
#print axioms taylorTarget_restrict
#print axioms shiftRows_restrict

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLeadingSupportDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

def groupIndexSupport : Fin 235→Fin 320 :=
 ![99,5,6,8,9,11,12,14,15,19,28,32,49,69,84,110,293,167,153,0,10,15,19,22,28,32,33,35,36,38,39,40,41,42,43,44,45,46,47,48,50,51,52,53,54,55,56,57,58,59,60,61,62,63,65,66,68,69,71,74,77,80,84,92,99,102,106,134,187,218,250,102,198,233,0,54,63,73,79,82,88,92,97,99,102,104,108,110,112,113,116,118,120,121,123,128,138,139,143,144,146,148,149,151,152,154,155,156,157,158,159,161,162,163,164,165,169,172,173,177,178,182,237,271,181,184,88,93,103,114,123,179,180,186,188,191,192,194,197,199,200,202,206,207,208,210,215,218,229,237,241,272,63,99,222,218,314,23,312,313,314,316,317,318,319,0,102,1,2,3,4,13,67,70,89,94,79,71,77,145,63,132,133,135,136,137,140,141,142,19,25,26,28,38,16,17,18,20,21,23,57,93,30,31,34,92,89,110,125,151,168,171,172,174,177,178,192,200,203,216,237,175,189,190,196,24,134,175,178,181,182,183,184,187,198]
theorem groupIndexSupport_spec (i : Fin 235) : support (groupIndexSupport i)=gridGroupIndex i := by
  fin_cases i <;> rfl

theorem groupIndex_restrict (v : Fin 780→ℂ) (i : Fin 235) :
    extension support (fun j => v (support j)) (gridGroupIndex i)=v (gridGroupIndex i) := by
  rw [←groupIndexSupport_spec]
  exact extend_at support support_injective (fun j => v (support j)) (groupIndexSupport i)
theorem infinity_restrict_0 (v : Fin 780→ℂ) :
    extension support (fun j => v (support j)) (gridInfinityIndex 0)=v (gridInfinityIndex 0) :=
  extend_at support support_injective (fun j => v (support j)) 10
theorem infinity_restrict_1 (v : Fin 780→ℂ) :
    extension support (fun j => v (support j)) (gridInfinityIndex 1)=v (gridInfinityIndex 1) :=
  extend_at support support_injective (fun j => v (support j)) 49

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLeadingSupportBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorSource_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 0) (gridTaylorT 0) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 0) (gridTaylorT 0) v := by
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  simp only [show gridTaylorQ 0=3 from rfl,show gridTaylorT 0=(10:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h270,h530]

theorem taylorSource_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 1) (gridTaylorT 1) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 1) (gridTaylorT 1) v := by
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  simp only [show gridTaylorQ 1=3 from rfl,show gridTaylorT 1=(-10:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h250,h510]

theorem taylorSource_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 2) (gridTaylorT 2) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 2) (gridTaylorT 2) v := by
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [show gridTaylorQ 2=3 from rfl,show gridTaylorT 2=(13:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h273,h533]

theorem taylorSource_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 3) (gridTaylorT 3) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 3) (gridTaylorT 3) v := by
  have h247 : extension support (fun a => v (support a)) 247=v 247 :=
    extend_at support support_injective (fun a => v (support a)) 100
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  simp only [show gridTaylorQ 3=3 from rfl,show gridTaylorT 3=(-13:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h247,h507]

theorem taylorSource_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 4) (gridTaylorT 4) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 4) (gridTaylorT 4) v := by
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  simp only [show gridTaylorQ 4=3 from rfl,show gridTaylorT 4=(20:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h280,h540]

theorem taylorSource_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 5) (gridTaylorT 5) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 5) (gridTaylorT 5) v := by
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  simp only [show gridTaylorQ 5=3 from rfl,show gridTaylorT 5=(-20:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h240,h500]

theorem taylorSource_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 6) (gridTaylorT 6) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 6) (gridTaylorT 6) v := by
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h545 : extension support (fun a => v (support a)) 545=v 545 :=
    extend_at support support_injective (fun a => v (support a)) 223
  simp only [show gridTaylorQ 6=3 from rfl,show gridTaylorT 6=(25:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h285,h545]

theorem taylorSource_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 7) (gridTaylorT 7) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 7) (gridTaylorT 7) v := by
  have h235 : extension support (fun a => v (support a)) 235=v 235 :=
    extend_at support support_injective (fun a => v (support a)) 98
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  simp only [show gridTaylorQ 7=3 from rfl,show gridTaylorT 7=(-25:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h235,h495]

theorem taylorSource_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 8) (gridTaylorT 8) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 8) (gridTaylorT 8) v := by
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [show gridTaylorQ 8=3 from rfl,show gridTaylorT 8=(26:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h286,h546]

theorem taylorSource_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 9) (gridTaylorT 9) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 9) (gridTaylorT 9) v := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  simp only [show gridTaylorQ 9=3 from rfl,show gridTaylorT 9=(-26:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h494]

theorem taylorSource_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 10) (gridTaylorT 10) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 10) (gridTaylorT 10) v := by
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [show gridTaylorQ 10=3 from rfl,show gridTaylorT 10=(40:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h300,h560]

theorem taylorSource_restrict_11 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 11) (gridTaylorT 11) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 11) (gridTaylorT 11) v := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  simp only [show gridTaylorQ 11=3 from rfl,show gridTaylorT 11=(-40:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h480]

theorem taylorSource_restrict_12 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 12) (gridTaylorT 12) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 12) (gridTaylorT 12) v := by
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  simp only [show gridTaylorQ 12=3 from rfl,show gridTaylorT 12=(50:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h310,h570]

theorem taylorSource_restrict_13 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 13) (gridTaylorT 13) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 13) (gridTaylorT 13) v := by
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  simp only [show gridTaylorQ 13=3 from rfl,show gridTaylorT 13=(-50:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h210,h470]

theorem taylorSource_restrict_14 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 14) (gridTaylorT 14) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 14) (gridTaylorT 14) v := by
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  simp only [show gridTaylorQ 14=4 from rfl,show gridTaylorT 14=(5:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h200,h590]

theorem taylorSource_restrict_15 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 15) (gridTaylorT 15) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 15) (gridTaylorT 15) v := by
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  simp only [show gridTaylorQ 15=4 from rfl,show gridTaylorT 15=(-5:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h190,h580]

theorem taylorSource_restrict_16 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 16) (gridTaylorT 16) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 16) (gridTaylorT 16) v := by
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  simp only [show gridTaylorQ 16=4 from rfl,show gridTaylorT 16=(13:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h208,h598]

theorem taylorSource_restrict_17 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 17) (gridTaylorT 17) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 17) (gridTaylorT 17) v := by
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  simp only [show gridTaylorQ 17=4 from rfl,show gridTaylorT 17=(-13:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h182,h572]

theorem taylorSource_restrict_18 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 18) (gridTaylorT 18) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 18) (gridTaylorT 18) v := by
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  simp only [show gridTaylorQ 18=4 from rfl,show gridTaylorT 18=(15:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h210,h600]

theorem taylorSource_restrict_19 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 19) (gridTaylorT 19) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 19) (gridTaylorT 19) v := by
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  simp only [show gridTaylorQ 19=4 from rfl,show gridTaylorT 19=(-15:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h180,h570]

theorem taylorSource_restrict_20 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 20) (gridTaylorT 20) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 20) (gridTaylorT 20) v := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  simp only [show gridTaylorQ 20=4 from rfl,show gridTaylorT 20=(25:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h610]

theorem taylorSource_restrict_21 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 21) (gridTaylorT 21) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 21) (gridTaylorT 21) v := by
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [show gridTaylorQ 21=4 from rfl,show gridTaylorT 21=(-25:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h170,h560]

theorem taylorSource_restrict_22 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 22) (gridTaylorT 22) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 22) (gridTaylorT 22) v := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridTaylorQ 22=4 from rfl,show gridTaylorT 22=(39:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h624]

theorem taylorSource_restrict_23 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 23) (gridTaylorT 23) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 23) (gridTaylorT 23) v := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [show gridTaylorQ 23=4 from rfl,show gridTaylorT 23=(-39:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h546]

theorem taylorSource_restrict_24 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 24) (gridTaylorT 24) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 24) (gridTaylorT 24) v := by
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [show gridTaylorQ 24=4 from rfl,show gridTaylorT 24=(45:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h240,h630]

theorem taylorSource_restrict_25 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 25) (gridTaylorT 25) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 25) (gridTaylorT 25) v := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  simp only [show gridTaylorQ 25=4 from rfl,show gridTaylorT 25=(-45:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h540]

theorem taylorSource_restrict_26 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 26) (gridTaylorT 26) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 26) (gridTaylorT 26) v := by
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [show gridTaylorQ 26=4 from rfl,show gridTaylorT 26=(65:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h260,h650]

theorem taylorSource_restrict_27 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 27) (gridTaylorT 27) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 27) (gridTaylorT 27) v := by
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  simp only [show gridTaylorQ 27=4 from rfl,show gridTaylorT 27=(75:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h270,h660]

theorem taylorSource_restrict_28 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 28) (gridTaylorT 28) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 28) (gridTaylorT 28) v := by
  have h132 : extension support (fun a => v (support a)) 132=v 132 :=
    extend_at support support_injective (fun a => v (support a)) 74
  have h652 : extension support (fun a => v (support a)) 652=v 652 :=
    extend_at support support_injective (fun a => v (support a)) 249
  simp only [show gridTaylorQ 28=6 from rfl,show gridTaylorT 28=(2:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h132,h652]

theorem taylorSource_restrict_29 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 29) (gridTaylorT 29) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 29) (gridTaylorT 29) v := by
  have h128 : extension support (fun a => v (support a)) 128=v 128 :=
    extend_at support support_injective (fun a => v (support a)) 72
  have h648 : extension support (fun a => v (support a)) 648=v 648 :=
    extend_at support support_injective (fun a => v (support a)) 247
  simp only [show gridTaylorQ 29=6 from rfl,show gridTaylorT 29=(-2:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h128,h648]

theorem taylorSource_restrict_30 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 30) (gridTaylorT 30) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 30) (gridTaylorT 30) v := by
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  simp only [show gridTaylorQ 30=6 from rfl,show gridTaylorT 30=(10:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h140,h660]

theorem taylorSource_restrict_31 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 31) (gridTaylorT 31) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 31) (gridTaylorT 31) v := by
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  simp only [show gridTaylorQ 31=6 from rfl,show gridTaylorT 31=(-10:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h120,h640]

theorem taylorSource_restrict_32 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 32) (gridTaylorT 32) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 32) (gridTaylorT 32) v := by
  have h143 : extension support (fun a => v (support a)) 143=v 143 :=
    extend_at support support_injective (fun a => v (support a)) 76
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  simp only [show gridTaylorQ 32=6 from rfl,show gridTaylorT 32=(13:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h143,h663]

theorem taylorSource_restrict_33 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 33) (gridTaylorT 33) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 33) (gridTaylorT 33) v := by
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h637 : extension support (fun a => v (support a)) 637=v 637 :=
    extend_at support support_injective (fun a => v (support a)) 245
  simp only [show gridTaylorQ 33=6 from rfl,show gridTaylorT 33=(-13:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h117,h637]

theorem taylorSource_restrict_34 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 34) (gridTaylorT 34) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 34) (gridTaylorT 34) v := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  simp only [show gridTaylorQ 34=6 from rfl,show gridTaylorT 34=(20:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h670]

theorem taylorSource_restrict_35 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 35) (gridTaylorT 35) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 35) (gridTaylorT 35) v := by
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [show gridTaylorQ 35=6 from rfl,show gridTaylorT 35=(-20:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h110,h630]

theorem taylorSource_restrict_36 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 36) (gridTaylorT 36) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 36) (gridTaylorT 36) v := by
  have h155 : extension support (fun a => v (support a)) 155=v 155 :=
    extend_at support support_injective (fun a => v (support a)) 78
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  simp only [show gridTaylorQ 36=6 from rfl,show gridTaylorT 36=(25:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h155,h675]

theorem taylorSource_restrict_37 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 37) (gridTaylorT 37) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 37) (gridTaylorT 37) v := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h625 : extension support (fun a => v (support a)) 625=v 625 :=
    extend_at support support_injective (fun a => v (support a)) 243
  simp only [show gridTaylorQ 37=6 from rfl,show gridTaylorT 37=(-25:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h625]

theorem taylorSource_restrict_38 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 38) (gridTaylorT 38) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 38) (gridTaylorT 38) v := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  simp only [show gridTaylorQ 38=6 from rfl,show gridTaylorT 38=(26:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h676]

theorem taylorSource_restrict_39 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 39) (gridTaylorT 39) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 39) (gridTaylorT 39) v := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridTaylorQ 39=6 from rfl,show gridTaylorT 39=(-26:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h624]

theorem taylorSource_restrict_40 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 40) (gridTaylorT 40) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 40) (gridTaylorT 40) v := by
  have h84 : extension support (fun a => v (support a)) 84=v 84 :=
    extend_at support support_injective (fun a => v (support a)) 62
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h552 : extension support (fun a => v (support a)) 552=v 552 :=
    extend_at support support_injective (fun a => v (support a)) 226
  have h708 : extension support (fun a => v (support a)) 708=v 708 :=
    extend_at support support_injective (fun a => v (support a)) 263
  simp only [show gridTaylorQ 40=10 from rfl,show gridTaylorT 40=(6:ℤ) from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h84,h240,h552,h708]

theorem taylorSource_restrict_41 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 41) (gridTaylorT 41) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 41) (gridTaylorT 41) v := by
  have h72 : extension support (fun a => v (support a)) 72=v 72 :=
    extend_at support support_injective (fun a => v (support a)) 58
  have h228 : extension support (fun a => v (support a)) 228=v 228 :=
    extend_at support support_injective (fun a => v (support a)) 95
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h696 : extension support (fun a => v (support a)) 696=v 696 :=
    extend_at support support_injective (fun a => v (support a)) 259
  simp only [show gridTaylorQ 41=10 from rfl,show gridTaylorT 41=(-6:ℤ) from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h72,h228,h540,h696]

theorem taylorSource_restrict_42 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 42) (gridTaylorT 42) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 42) (gridTaylorT 42) v := by
  have h66 : extension support (fun a => v (support a)) 66=v 66 :=
    extend_at support support_injective (fun a => v (support a)) 55
  have h326 : extension support (fun a => v (support a)) 326=v 326 :=
    extend_at support support_injective (fun a => v (support a)) 117
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  have h716 : extension support (fun a => v (support a)) 716=v 716 :=
    extend_at support support_injective (fun a => v (support a)) 268
  simp only [show gridTaylorQ 42=12 from rfl,show gridTaylorT 42=(1:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h66,h326,h456,h716]

theorem taylorSource_restrict_43 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 43) (gridTaylorT 43) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 43) (gridTaylorT 43) v := by
  have h64 : extension support (fun a => v (support a)) 64=v 64 :=
    extend_at support support_injective (fun a => v (support a)) 53
  have h324 : extension support (fun a => v (support a)) 324=v 324 :=
    extend_at support support_injective (fun a => v (support a)) 115
  have h454 : extension support (fun a => v (support a)) 454=v 454 :=
    extend_at support support_injective (fun a => v (support a)) 204
  have h714 : extension support (fun a => v (support a)) 714=v 714 :=
    extend_at support support_injective (fun a => v (support a)) 266
  simp only [show gridTaylorQ 43=12 from rfl,show gridTaylorT 43=(-1:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h64,h324,h454,h714]

theorem taylorSource_restrict_44 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 44) (gridTaylorT 44) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 44) (gridTaylorT 44) v := by
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 44=12 from rfl,show gridTaylorT 44=(5:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h70,h330,h460,h720]

theorem taylorSource_restrict_45 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 45) (gridTaylorT 45) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 45) (gridTaylorT 45) v := by
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  simp only [show gridTaylorQ 45=12 from rfl,show gridTaylorT 45=(-5:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h60,h320,h450,h710]

theorem taylorSource_restrict_46 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 46) (gridTaylorT 46) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 46) (gridTaylorT 46) v := by
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [show gridTaylorQ 46=12 from rfl,show gridTaylorT 46=(13:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h78,h338,h468,h728]

theorem taylorSource_restrict_47 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 47) (gridTaylorT 47) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 47) (gridTaylorT 47) v := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [show gridTaylorQ 47=12 from rfl,show gridTaylorT 47=(-13:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h312,h442,h702]

theorem taylorSource_restrict_48 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 48) (gridTaylorT 48) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 48) (gridTaylorT 48) v := by
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  simp only [show gridTaylorQ 48=13 from rfl,show gridTaylorT 48=(10:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h70,h130,h190,h250,h310,h370,h430,h490,h550,h610,h670,h730]

theorem taylorSource_restrict_49 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 49) (gridTaylorT 49) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 49) (gridTaylorT 49) v := by
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [show gridTaylorQ 49=13 from rfl,show gridTaylorT 49=(20:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h80,h140,h200,h260,h320,h380,h440,h500,h560,h620,h680,h740]

theorem taylorSource_restrict_50 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 50) (gridTaylorT 50) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 50) (gridTaylorT 50) v := by
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 50=13 from rfl,show gridTaylorT 50=(30:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h90,h150,h210,h270,h330,h390,h450,h510,h570,h630,h690,h750]

theorem taylorSource_restrict_51 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 51) (gridTaylorT 51) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 51) (gridTaylorT 51) v := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridTaylorQ 51=52 from rfl,show gridTaylorT 51=(5:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h50,h80,h110,h140,h170,h230,h260,h290,h320,h350,h380,h410,h440,h470,h500,h530,h560,h620,h650,h680,h710,h740,h770]

theorem taylorSource_restrict_52 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 52) (gridTaylorT 52) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 52) (gridTaylorT 52) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 52=52 from rfl,show gridTaylorT 52=(-45:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h30,h60,h90,h120,h180,h210,h240,h270,h300,h330,h360,h390,h420,h450,h480,h510,h570,h600,h630,h660,h690,h720,h750]

theorem entireSource_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 0) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 0) 0 v := by
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  simp only [show gridEntireQ 0=3 from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h260,h520]

theorem entireSource_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 1) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 1) 0 v := by
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  simp only [show gridEntireQ 1=4 from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h195,h585]

theorem entireSource_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 2) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 2) 0 v := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridEntireQ 2=5 from rfl,gridSample,show residues 5=({1,2,3,4}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h312,h468,h624]

theorem entireSource_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 3) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 3) 0 v := by
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [show gridEntireQ 3=6 from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h130,h650]

theorem entireSource_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 4) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 4) 0 v := by
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [show gridEntireQ 4=10 from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h78,h234,h546,h702]

theorem entireSource_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 5) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 5) 0 v := by
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridEntireQ 5=13 from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h60,h120,h180,h240,h300,h360,h420,h480,h540,h600,h660,h720]

theorem entireSource_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 6) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 6) 0 v := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h364 : extension support (fun a => v (support a)) 364=v 364 :=
    extend_at support support_injective (fun a => v (support a)) 138
  have h416 : extension support (fun a => v (support a)) 416=v 416 :=
    extend_at support support_injective (fun a => v (support a)) 183
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [show gridEntireQ 6=15 from rfl,gridSample,show residues 15=({1,2,4,7,8,11,13,14}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h104,h208,h364,h416,h572,h676,h728]

theorem entireSource_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 7) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 7) 0 v := by
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h351 : extension support (fun a => v (support a)) 351=v 351 :=
    extend_at support support_injective (fun a => v (support a)) 126
  have h429 : extension support (fun a => v (support a)) 429=v 429 :=
    extend_at support support_injective (fun a => v (support a)) 195
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  have h741 : extension support (fun a => v (support a)) 741=v 741 :=
    extend_at support support_injective (fun a => v (support a)) 287
  simp only [show gridEntireQ 7=20 from rfl,gridSample,show residues 20=({1,3,7,9,11,13,17,19}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h39,h117,h273,h351,h429,h507,h663,h741]

theorem entireSource_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 8) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 8) 0 v := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  simp only [show gridEntireQ 8=30 from rfl,gridSample,show residues 30=({1,7,11,13,17,19,23,29}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h182,h286,h338,h442,h494,h598,h754]

theorem entireSource_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 9) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 9) 0 v := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridEntireQ 9=39 from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h40,h80,h100,h140,h160,h200,h220,h280,h320,h340,h380,h400,h440,h460,h500,h560,h580,h620,h640,h680,h700,h740,h760]

theorem entireSource_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 10) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 10) 0 v := by
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridEntireQ 10=78 from rfl,gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h10,h50,h70,h110,h170,h190,h230,h250,h290,h310,h350,h370,h410,h430,h470,h490,h530,h550,h590,h610,h670,h710,h730,h770]

theorem heckeSource_restrict_0 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 0=
      gridHeckeLeading m f s v 0 := by
  have h7 : extension support (fun a => v (support a)) 7=v 7 :=
    extend_at support support_injective (fun a => v (support a)) 7
  have h14 : extension support (fun a => v (support a)) 14=v 14 :=
    extend_at support support_injective (fun a => v (support a)) 14
  have h397 : extension support (fun a => v (support a)) 397=v 397 :=
    extend_at support support_injective (fun a => v (support a)) 167
  simp only [gridHeckeLeading,show gridHeckeP 0=2 from rfl,show gridHeckeT 0=(7:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h7,h14,h397]

theorem heckeSource_restrict_1 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 1=
      gridHeckeLeading m f s v 1 := by
  have h8 : extension support (fun a => v (support a)) 8=v 8 :=
    extend_at support support_injective (fun a => v (support a)) 8
  have h16 : extension support (fun a => v (support a)) 16=v 16 :=
    extend_at support support_injective (fun a => v (support a)) 16
  have h398 : extension support (fun a => v (support a)) 398=v 398 :=
    extend_at support support_injective (fun a => v (support a)) 168
  simp only [gridHeckeLeading,show gridHeckeP 1=2 from rfl,show gridHeckeT 1=(8:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h8,h16,h398]

theorem heckeSource_restrict_2 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 2=
      gridHeckeLeading m f s v 2 := by
  have h9 : extension support (fun a => v (support a)) 9=v 9 :=
    extend_at support support_injective (fun a => v (support a)) 9
  have h18 : extension support (fun a => v (support a)) 18=v 18 :=
    extend_at support support_injective (fun a => v (support a)) 17
  have h399 : extension support (fun a => v (support a)) 399=v 399 :=
    extend_at support support_injective (fun a => v (support a)) 169
  simp only [gridHeckeLeading,show gridHeckeP 2=2 from rfl,show gridHeckeT 2=(9:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h9,h18,h399]

theorem heckeSource_restrict_3 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 3=
      gridHeckeLeading m f s v 3 := by
  have h11 : extension support (fun a => v (support a)) 11=v 11 :=
    extend_at support support_injective (fun a => v (support a)) 11
  have h22 : extension support (fun a => v (support a)) 22=v 22 :=
    extend_at support support_injective (fun a => v (support a)) 21
  have h401 : extension support (fun a => v (support a)) 401=v 401 :=
    extend_at support support_injective (fun a => v (support a)) 171
  simp only [gridHeckeLeading,show gridHeckeP 3=2 from rfl,show gridHeckeT 3=(11:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h11,h22,h401]

theorem heckeSource_restrict_4 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 4=
      gridHeckeLeading m f s v 4 := by
  have h16 : extension support (fun a => v (support a)) 16=v 16 :=
    extend_at support support_injective (fun a => v (support a)) 16
  have h32 : extension support (fun a => v (support a)) 32=v 32 :=
    extend_at support support_injective (fun a => v (support a)) 30
  have h406 : extension support (fun a => v (support a)) 406=v 406 :=
    extend_at support support_injective (fun a => v (support a)) 176
  simp only [gridHeckeLeading,show gridHeckeP 4=2 from rfl,show gridHeckeT 4=(16:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h16,h32,h406]

theorem heckeSource_restrict_5 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 5=
      gridHeckeLeading m f s v 5 := by
  have h22 : extension support (fun a => v (support a)) 22=v 22 :=
    extend_at support support_injective (fun a => v (support a)) 21
  have h44 : extension support (fun a => v (support a)) 44=v 44 :=
    extend_at support support_injective (fun a => v (support a)) 37
  have h412 : extension support (fun a => v (support a)) 412=v 412 :=
    extend_at support support_injective (fun a => v (support a)) 180
  simp only [gridHeckeLeading,show gridHeckeP 5=2 from rfl,show gridHeckeT 5=(22:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h22,h44,h412]

theorem heckeSource_restrict_6 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 6=
      gridHeckeLeading m f s v 6 := by
  have h24 : extension support (fun a => v (support a)) 24=v 24 :=
    extend_at support support_injective (fun a => v (support a)) 22
  have h48 : extension support (fun a => v (support a)) 48=v 48 :=
    extend_at support support_injective (fun a => v (support a)) 39
  have h414 : extension support (fun a => v (support a)) 414=v 414 :=
    extend_at support support_injective (fun a => v (support a)) 181
  simp only [gridHeckeLeading,show gridHeckeP 6=2 from rfl,show gridHeckeT 6=(24:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h24,h48,h414]

theorem heckeSource_restrict_7 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 7=
      gridHeckeLeading m f s v 7 := by
  have h25 : extension support (fun a => v (support a)) 25=v 25 :=
    extend_at support support_injective (fun a => v (support a)) 23
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h415 : extension support (fun a => v (support a)) 415=v 415 :=
    extend_at support support_injective (fun a => v (support a)) 182
  simp only [gridHeckeLeading,show gridHeckeP 7=2 from rfl,show gridHeckeT 7=(25:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h25,h50,h415]

theorem heckeSource_restrict_8 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 8=
      gridHeckeLeading m f s v 8 := by
  have h42 : extension support (fun a => v (support a)) 42=v 42 :=
    extend_at support support_injective (fun a => v (support a)) 36
  have h84 : extension support (fun a => v (support a)) 84=v 84 :=
    extend_at support support_injective (fun a => v (support a)) 62
  have h432 : extension support (fun a => v (support a)) 432=v 432 :=
    extend_at support support_injective (fun a => v (support a)) 197
  simp only [gridHeckeLeading,show gridHeckeP 8=2 from rfl,show gridHeckeT 8=(42:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h42,h84,h432]

theorem heckeSource_restrict_9 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 9=
      gridHeckeLeading m f s v 9 := by
  have h48 : extension support (fun a => v (support a)) 48=v 48 :=
    extend_at support support_injective (fun a => v (support a)) 39
  have h96 : extension support (fun a => v (support a)) 96=v 96 :=
    extend_at support support_injective (fun a => v (support a)) 65
  have h438 : extension support (fun a => v (support a)) 438=v 438 :=
    extend_at support support_injective (fun a => v (support a)) 199
  simp only [gridHeckeLeading,show gridHeckeP 9=2 from rfl,show gridHeckeT 9=(48:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h48,h96,h438]

theorem heckeSource_restrict_10 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 10=
      gridHeckeLeading m f s v 10 := by
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  simp only [gridHeckeLeading,show gridHeckeP 10=2 from rfl,show gridHeckeT 10=(50:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h50,h100,h440]

theorem heckeSource_restrict_11 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 11=
      gridHeckeLeading m f s v 11 := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  simp only [gridHeckeLeading,show gridHeckeP 11=2 from rfl,show gridHeckeT 11=(52:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h104,h442]

theorem heckeSource_restrict_12 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 12=
      gridHeckeLeading m f s v 12 := by
  have h55 : extension support (fun a => v (support a)) 55=v 55 :=
    extend_at support support_injective (fun a => v (support a)) 44
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h445 : extension support (fun a => v (support a)) 445=v 445 :=
    extend_at support support_injective (fun a => v (support a)) 202
  simp only [gridHeckeLeading,show gridHeckeP 12=2 from rfl,show gridHeckeT 12=(55:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h55,h110,h445]

theorem heckeSource_restrict_13 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 13=
      gridHeckeLeading m f s v 13 := by
  have h66 : extension support (fun a => v (support a)) 66=v 66 :=
    extend_at support support_injective (fun a => v (support a)) 55
  have h132 : extension support (fun a => v (support a)) 132=v 132 :=
    extend_at support support_injective (fun a => v (support a)) 74
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  simp only [gridHeckeLeading,show gridHeckeP 13=2 from rfl,show gridHeckeT 13=(66:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h66,h132,h456]

theorem heckeSource_restrict_14 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 14=
      gridHeckeLeading m f s v 14 := by
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h465 : extension support (fun a => v (support a)) 465=v 465 :=
    extend_at support support_injective (fun a => v (support a)) 208
  simp only [gridHeckeLeading,show gridHeckeP 14=2 from rfl,show gridHeckeT 14=(75:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h75,h150,h465]

theorem heckeSource_restrict_15 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 15=
      gridHeckeLeading m f s v 15 := by
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  simp only [gridHeckeLeading,show gridHeckeP 15=2 from rfl,show gridHeckeT 15=(80:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h80,h160,h470]

theorem heckeSource_restrict_16 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 16=
      gridHeckeLeading m f s v 16 := by
  have h95 : extension support (fun a => v (support a)) 95=v 95 :=
    extend_at support support_injective (fun a => v (support a)) 64
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h485 : extension support (fun a => v (support a)) 485=v 485 :=
    extend_at support support_injective (fun a => v (support a)) 212
  simp only [gridHeckeLeading,show gridHeckeP 16=2 from rfl,show gridHeckeT 16=(95:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h95,h190,h485]

theorem heckeSource_restrict_17 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 17=
      gridHeckeLeading m f s v 17 := by
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  simp only [gridHeckeLeading,show gridHeckeP 17=2 from rfl,show gridHeckeT 17=(100:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h100,h200,h490]

theorem heckeSource_restrict_18 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 18=
      gridHeckeLeading m f s v 18 := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  simp only [gridHeckeLeading,show gridHeckeP 18=2 from rfl,show gridHeckeT 18=(104:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h208,h494]

theorem heckeSource_restrict_19 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 19=
      gridHeckeLeading m f s v 19 := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  simp only [gridHeckeLeading,show gridHeckeP 19=2 from rfl,show gridHeckeT 19=(105:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h210,h495]

theorem heckeSource_restrict_20 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 20=
      gridHeckeLeading m f s v 20 := by
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  simp only [gridHeckeLeading,show gridHeckeP 20=2 from rfl,show gridHeckeT 20=(120:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h120,h240,h510]

theorem heckeSource_restrict_21 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 21=
      gridHeckeLeading m f s v 21 := by
  have h143 : extension support (fun a => v (support a)) 143=v 143 :=
    extend_at support support_injective (fun a => v (support a)) 76
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [gridHeckeLeading,show gridHeckeP 21=2 from rfl,show gridHeckeT 21=(143:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h143,h286,h533]

theorem heckeSource_restrict_22 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 22=
      gridHeckeLeading m f s v 22 := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  simp only [gridHeckeLeading,show gridHeckeP 22=2 from rfl,show gridHeckeT 22=(150:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h300,h540]

theorem heckeSource_restrict_23 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 23=
      gridHeckeLeading m f s v 23 := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [gridHeckeLeading,show gridHeckeP 23=2 from rfl,show gridHeckeT 23=(156:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h312,h546]

theorem heckeSource_restrict_24 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 24=
      gridHeckeLeading m f s v 24 := by
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  simp only [gridHeckeLeading,show gridHeckeP 24=2 from rfl,show gridHeckeT 24=(160:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h160,h320,h550]

theorem heckeSource_restrict_25 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 25=
      gridHeckeLeading m f s v 25 := by
  have h162 : extension support (fun a => v (support a)) 162=v 162 :=
    extend_at support support_injective (fun a => v (support a)) 81
  have h324 : extension support (fun a => v (support a)) 324=v 324 :=
    extend_at support support_injective (fun a => v (support a)) 115
  have h552 : extension support (fun a => v (support a)) 552=v 552 :=
    extend_at support support_injective (fun a => v (support a)) 226
  simp only [gridHeckeLeading,show gridHeckeP 25=2 from rfl,show gridHeckeT 25=(162:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h162,h324,h552]

theorem heckeSource_restrict_26 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 26=
      gridHeckeLeading m f s v 26 := by
  have h165 : extension support (fun a => v (support a)) 165=v 165 :=
    extend_at support support_injective (fun a => v (support a)) 82
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  simp only [gridHeckeLeading,show gridHeckeP 26=2 from rfl,show gridHeckeT 26=(165:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h165,h330,h555]

theorem heckeSource_restrict_27 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 27=
      gridHeckeLeading m f s v 27 := by
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [gridHeckeLeading,show gridHeckeP 27=2 from rfl,show gridHeckeT 27=(170:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h170,h340,h560]

theorem heckeSource_restrict_28 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 28=
      gridHeckeLeading m f s v 28 := by
  have h185 : extension support (fun a => v (support a)) 185=v 185 :=
    extend_at support support_injective (fun a => v (support a)) 86
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h575 : extension support (fun a => v (support a)) 575=v 575 :=
    extend_at support support_injective (fun a => v (support a)) 231
  simp only [gridHeckeLeading,show gridHeckeP 28=2 from rfl,show gridHeckeT 28=(185:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h185,h370,h575]

theorem heckeSource_restrict_29 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 29=
      gridHeckeLeading m f s v 29 := by
  have h205 : extension support (fun a => v (support a)) 205=v 205 :=
    extend_at support support_injective (fun a => v (support a)) 90
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h595 : extension support (fun a => v (support a)) 595=v 595 :=
    extend_at support support_injective (fun a => v (support a)) 235
  simp only [gridHeckeLeading,show gridHeckeP 29=2 from rfl,show gridHeckeT 29=(205:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h205,h410,h595]

theorem heckeSource_restrict_30 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 30=
      gridHeckeLeading m f s v 30 := by
  have h228 : extension support (fun a => v (support a)) 228=v 228 :=
    extend_at support support_injective (fun a => v (support a)) 95
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  have h618 : extension support (fun a => v (support a)) 618=v 618 :=
    extend_at support support_injective (fun a => v (support a)) 240
  simp only [gridHeckeLeading,show gridHeckeP 30=2 from rfl,show gridHeckeT 30=(228:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h228,h456,h618]

theorem heckeSource_restrict_31 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 31=
      gridHeckeLeading m f s v 31 := by
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  simp only [gridHeckeLeading,show gridHeckeP 31=2 from rfl,show gridHeckeT 31=(230:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h230,h460,h620]

theorem heckeSource_restrict_32 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 32=
      gridHeckeLeading m f s v 32 := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [gridHeckeLeading,show gridHeckeP 32=2 from rfl,show gridHeckeT 32=(234:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h468,h624]

theorem heckeSource_restrict_33 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 33=
      gridHeckeLeading m f s v 33 := by
  have h235 : extension support (fun a => v (support a)) 235=v 235 :=
    extend_at support support_injective (fun a => v (support a)) 98
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h625 : extension support (fun a => v (support a)) 625=v 625 :=
    extend_at support support_injective (fun a => v (support a)) 243
  simp only [gridHeckeLeading,show gridHeckeP 33=2 from rfl,show gridHeckeT 33=(235:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h235,h470,h625]

theorem heckeSource_restrict_34 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 34=
      gridHeckeLeading m f s v 34 := by
  have h247 : extension support (fun a => v (support a)) 247=v 247 :=
    extend_at support support_injective (fun a => v (support a)) 100
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h637 : extension support (fun a => v (support a)) 637=v 637 :=
    extend_at support support_injective (fun a => v (support a)) 245
  simp only [gridHeckeLeading,show gridHeckeP 34=2 from rfl,show gridHeckeT 34=(247:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h247,h494,h637]

theorem heckeSource_restrict_35 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 35=
      gridHeckeLeading m f s v 35 := by
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  simp only [gridHeckeLeading,show gridHeckeP 35=2 from rfl,show gridHeckeT 35=(250:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h250,h500,h640]

theorem heckeSource_restrict_36 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 36=
      gridHeckeLeading m f s v 36 := by
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  simp only [gridHeckeLeading,show gridHeckeP 36=2 from rfl,show gridHeckeT 36=(280:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h280,h560,h670]

theorem heckeSource_restrict_37 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 37=
      gridHeckeLeading m f s v 37 := by
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  simp only [gridHeckeLeading,show gridHeckeP 37=2 from rfl,show gridHeckeT 37=(286:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h286,h572,h676]

theorem heckeSource_restrict_38 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 38=
      gridHeckeLeading m f s v 38 := by
  have h295 : extension support (fun a => v (support a)) 295=v 295 :=
    extend_at support support_injective (fun a => v (support a)) 109
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h685 : extension support (fun a => v (support a)) 685=v 685 :=
    extend_at support support_injective (fun a => v (support a)) 257
  simp only [gridHeckeLeading,show gridHeckeP 38=2 from rfl,show gridHeckeT 38=(295:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h295,h590,h685]

theorem heckeSource_restrict_39 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 39=
      gridHeckeLeading m f s v 39 := by
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [gridHeckeLeading,show gridHeckeP 39=2 from rfl,show gridHeckeT 39=(312:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h312,h624,h702]

theorem heckeSource_restrict_40 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 40=
      gridHeckeLeading m f s v 40 := by
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h705 : extension support (fun a => v (support a)) 705=v 705 :=
    extend_at support support_injective (fun a => v (support a)) 262
  simp only [gridHeckeLeading,show gridHeckeP 40=2 from rfl,show gridHeckeT 40=(315:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h315,h630,h705]

theorem heckeSource_restrict_41 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 41=
      gridHeckeLeading m f s v 41 := by
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  simp only [gridHeckeLeading,show gridHeckeP 41=2 from rfl,show gridHeckeT 41=(340:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h340,h680,h730]

theorem heckeSource_restrict_42 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 42=
      gridHeckeLeading m f s v 42 := by
  have h342 : extension support (fun a => v (support a)) 342=v 342 :=
    extend_at support support_injective (fun a => v (support a)) 122
  have h684 : extension support (fun a => v (support a)) 684=v 684 :=
    extend_at support support_injective (fun a => v (support a)) 256
  have h732 : extension support (fun a => v (support a)) 732=v 732 :=
    extend_at support support_injective (fun a => v (support a)) 282
  simp only [gridHeckeLeading,show gridHeckeP 42=2 from rfl,show gridHeckeT 42=(342:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h342,h684,h732]

theorem heckeSource_restrict_43 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 43=
      gridHeckeLeading m f s v 43 := by
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [gridHeckeLeading,show gridHeckeP 43=2 from rfl,show gridHeckeT 43=(350:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h350,h700,h740]

theorem heckeSource_restrict_44 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 44=
      gridHeckeLeading m f s v 44 := by
  have h359 : extension support (fun a => v (support a)) 359=v 359 :=
    extend_at support support_injective (fun a => v (support a)) 133
  have h718 : extension support (fun a => v (support a)) 718=v 718 :=
    extend_at support support_injective (fun a => v (support a)) 270
  have h749 : extension support (fun a => v (support a)) 749=v 749 :=
    extend_at support support_injective (fun a => v (support a)) 292
  simp only [gridHeckeLeading,show gridHeckeP 44=2 from rfl,show gridHeckeT 44=(359:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h359,h718,h749]

theorem heckeSource_restrict_45 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 45=
      gridHeckeLeading m f s v 45 := by
  have h363 : extension support (fun a => v (support a)) 363=v 363 :=
    extend_at support support_injective (fun a => v (support a)) 137
  have h726 : extension support (fun a => v (support a)) 726=v 726 :=
    extend_at support support_injective (fun a => v (support a)) 278
  have h753 : extension support (fun a => v (support a)) 753=v 753 :=
    extend_at support support_injective (fun a => v (support a)) 296
  simp only [gridHeckeLeading,show gridHeckeP 45=2 from rfl,show gridHeckeT 45=(363:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h363,h726,h753]

theorem heckeSource_restrict_46 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 46=
      gridHeckeLeading m f s v 46 := by
  have h368 : extension support (fun a => v (support a)) 368=v 368 :=
    extend_at support support_injective (fun a => v (support a)) 141
  have h736 : extension support (fun a => v (support a)) 736=v 736 :=
    extend_at support support_injective (fun a => v (support a)) 284
  have h758 : extension support (fun a => v (support a)) 758=v 758 :=
    extend_at support support_injective (fun a => v (support a)) 300
  simp only [gridHeckeLeading,show gridHeckeP 46=2 from rfl,show gridHeckeT 46=(368:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h368,h736,h758]

theorem heckeSource_restrict_47 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 47=
      gridHeckeLeading m f s v 47 := by
  have h377 : extension support (fun a => v (support a)) 377=v 377 :=
    extend_at support support_injective (fun a => v (support a)) 148
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  have h767 : extension support (fun a => v (support a)) 767=v 767 :=
    extend_at support support_injective (fun a => v (support a)) 308
  simp only [gridHeckeLeading,show gridHeckeP 47=2 from rfl,show gridHeckeT 47=(377:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h377,h754,h767]

theorem heckeSource_restrict_48 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 48=
      gridHeckeLeading m f s v 48 := by
  have h382 : extension support (fun a => v (support a)) 382=v 382 :=
    extend_at support support_injective (fun a => v (support a)) 153
  have h764 : extension support (fun a => v (support a)) 764=v 764 :=
    extend_at support support_injective (fun a => v (support a)) 305
  have h772 : extension support (fun a => v (support a)) 772=v 772 :=
    extend_at support support_injective (fun a => v (support a)) 313
  simp only [gridHeckeLeading,show gridHeckeP 48=2 from rfl,show gridHeckeT 48=(382:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h382,h764,h772]

theorem heckeSource_restrict_49 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 49=
      gridHeckeLeading m f s v 49 := by
  have h13 : extension support (fun a => v (support a)) 13=v 13 :=
    extend_at support support_injective (fun a => v (support a)) 13
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [gridHeckeLeading,show gridHeckeP 49=3 from rfl,show gridHeckeT 49=(13:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h13,h39,h117,h273,h533]

theorem heckeSource_restrict_50 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 50=
      gridHeckeLeading m f s v 50 := by
  have h25 : extension support (fun a => v (support a)) 25=v 25 :=
    extend_at support support_injective (fun a => v (support a)) 23
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h545 : extension support (fun a => v (support a)) 545=v 545 :=
    extend_at support support_injective (fun a => v (support a)) 223
  simp only [gridHeckeLeading,show gridHeckeP 50=3 from rfl,show gridHeckeT 50=(25:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h25,h75,h225,h285,h545]

theorem heckeSource_restrict_51 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 51=
      gridHeckeLeading m f s v 51 := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [gridHeckeLeading,show gridHeckeP 51=3 from rfl,show gridHeckeT 51=(26:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h78,h234,h286,h546]

theorem heckeSource_restrict_52 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 52=
      gridHeckeLeading m f s v 52 := by
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  simp only [gridHeckeLeading,show gridHeckeP 52=3 from rfl,show gridHeckeT 52=(30:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h30,h90,h270,h290,h550]

theorem heckeSource_restrict_53 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 53=
      gridHeckeLeading m f s v 53 := by
  have h35 : extension support (fun a => v (support a)) 35=v 35 :=
    extend_at support support_injective (fun a => v (support a)) 32
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h295 : extension support (fun a => v (support a)) 295=v 295 :=
    extend_at support support_injective (fun a => v (support a)) 109
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  simp only [gridHeckeLeading,show gridHeckeP 53=3 from rfl,show gridHeckeT 53=(35:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h35,h105,h295,h315,h555]

theorem heckeSource_restrict_54 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 54=
      gridHeckeLeading m f s v 54 := by
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [gridHeckeLeading,show gridHeckeP 54=3 from rfl,show gridHeckeT 54=(40:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h40,h120,h300,h360,h560]

theorem heckeSource_restrict_55 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 55=
      gridHeckeLeading m f s v 55 := by
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  simp only [gridHeckeLeading,show gridHeckeP 55=3 from rfl,show gridHeckeT 55=(50:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h50,h150,h310,h450,h570]

theorem heckeSource_restrict_56 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 56=
      gridHeckeLeading m f s v 56 := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  simp only [gridHeckeLeading,show gridHeckeP 56=3 from rfl,show gridHeckeT 56=(52:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h156,h312,h468,h572]

theorem heckeSource_restrict_57 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 57=
      gridHeckeLeading m f s v 57 := by
  have h55 : extension support (fun a => v (support a)) 55=v 55 :=
    extend_at support support_injective (fun a => v (support a)) 44
  have h165 : extension support (fun a => v (support a)) 165=v 165 :=
    extend_at support support_injective (fun a => v (support a)) 82
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  have h575 : extension support (fun a => v (support a)) 575=v 575 :=
    extend_at support support_injective (fun a => v (support a)) 231
  simp only [gridHeckeLeading,show gridHeckeP 57=3 from rfl,show gridHeckeT 57=(55:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h55,h165,h315,h495,h575]

theorem heckeSource_restrict_58 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 58=
      gridHeckeLeading m f s v 58 := by
  have h65 : extension support (fun a => v (support a)) 65=v 65 :=
    extend_at support support_injective (fun a => v (support a)) 54
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h325 : extension support (fun a => v (support a)) 325=v 325 :=
    extend_at support support_injective (fun a => v (support a)) 116
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  simp only [gridHeckeLeading,show gridHeckeP 58=3 from rfl,show gridHeckeT 58=(65:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h65,h195,h325,h585]

theorem heckeSource_restrict_59 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 59=
      gridHeckeLeading m f s v 59 := by
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [gridHeckeLeading,show gridHeckeP 59=3 from rfl,show gridHeckeT 59=(70:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h70,h210,h330,h590,h630]

theorem heckeSource_restrict_60 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 60=
      gridHeckeLeading m f s v 60 := by
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h335 : extension support (fun a => v (support a)) 335=v 335 :=
    extend_at support support_injective (fun a => v (support a)) 119
  have h595 : extension support (fun a => v (support a)) 595=v 595 :=
    extend_at support support_injective (fun a => v (support a)) 235
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  simp only [gridHeckeLeading,show gridHeckeP 60=3 from rfl,show gridHeckeT 60=(75:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h75,h225,h335,h595,h675]

theorem heckeSource_restrict_61 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 61=
      gridHeckeLeading m f s v 61 := by
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [gridHeckeLeading,show gridHeckeP 61=3 from rfl,show gridHeckeT 61=(78:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h78,h234,h338,h598,h702]

theorem heckeSource_restrict_62 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 62=
      gridHeckeLeading m f s v 62 := by
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  simp only [gridHeckeLeading,show gridHeckeP 62=3 from rfl,show gridHeckeT 62=(90:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h30,h90,h270,h350,h610]

theorem heckeSource_restrict_63 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 63=
      gridHeckeLeading m f s v 63 := by
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h95 : extension support (fun a => v (support a)) 95=v 95 :=
    extend_at support support_injective (fun a => v (support a)) 64
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h355 : extension support (fun a => v (support a)) 355=v 355 :=
    extend_at support support_injective (fun a => v (support a)) 129
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  simp only [gridHeckeLeading,show gridHeckeP 63=3 from rfl,show gridHeckeT 63=(95:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h75,h95,h285,h355,h615]

theorem heckeSource_restrict_64 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 64=
      gridHeckeLeading m f s v 64 := by
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  simp only [gridHeckeLeading,show gridHeckeP 64=3 from rfl,show gridHeckeT 64=(100:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h100,h120,h300,h360,h620]

theorem heckeSource_restrict_65 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 65=
      gridHeckeLeading m f s v 65 := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h364 : extension support (fun a => v (support a)) 364=v 364 :=
    extend_at support support_injective (fun a => v (support a)) 138
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [gridHeckeLeading,show gridHeckeP 65=3 from rfl,show gridHeckeT 65=(104:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h156,h312,h364,h624]

theorem heckeSource_restrict_66 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 66=
      gridHeckeLeading m f s v 66 := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h165 : extension support (fun a => v (support a)) 165=v 165 :=
    extend_at support support_injective (fun a => v (support a)) 82
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h365 : extension support (fun a => v (support a)) 365=v 365 :=
    extend_at support support_injective (fun a => v (support a)) 139
  have h625 : extension support (fun a => v (support a)) 625=v 625 :=
    extend_at support support_injective (fun a => v (support a)) 243
  simp only [gridHeckeLeading,show gridHeckeP 66=3 from rfl,show gridHeckeT 66=(105:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h165,h315,h365,h625]

theorem heckeSource_restrict_67 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 67=
      gridHeckeLeading m f s v 67 := by
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [gridHeckeLeading,show gridHeckeP 67=3 from rfl,show gridHeckeT 67=(110:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h110,h210,h330,h370,h630]

theorem heckeSource_restrict_68 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 68=
      gridHeckeLeading m f s v 68 := by
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h351 : extension support (fun a => v (support a)) 351=v 351 :=
    extend_at support support_injective (fun a => v (support a)) 126
  have h377 : extension support (fun a => v (support a)) 377=v 377 :=
    extend_at support support_injective (fun a => v (support a)) 148
  have h637 : extension support (fun a => v (support a)) 637=v 637 :=
    extend_at support support_injective (fun a => v (support a)) 245
  simp only [gridHeckeLeading,show gridHeckeP 68=3 from rfl,show gridHeckeT 68=(117:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h117,h273,h351,h377,h637]

theorem heckeSource_restrict_69 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 69=
      gridHeckeLeading m f s v 69 := by
  have h143 : extension support (fun a => v (support a)) 143=v 143 :=
    extend_at support support_injective (fun a => v (support a)) 76
  have h403 : extension support (fun a => v (support a)) 403=v 403 :=
    extend_at support support_injective (fun a => v (support a)) 173
  have h429 : extension support (fun a => v (support a)) 429=v 429 :=
    extend_at support support_injective (fun a => v (support a)) 195
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  simp only [gridHeckeLeading,show gridHeckeP 69=3 from rfl,show gridHeckeT 69=(143:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h143,h403,h429,h507,h663]

theorem heckeSource_restrict_70 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 70=
      gridHeckeLeading m f s v 70 := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  simp only [gridHeckeLeading,show gridHeckeP 70=3 from rfl,show gridHeckeT 70=(150:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h410,h450,h570,h670]

theorem heckeSource_restrict_71 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 71=
      gridHeckeLeading m f s v 71 := by
  have h155 : extension support (fun a => v (support a)) 155=v 155 :=
    extend_at support support_injective (fun a => v (support a)) 78
  have h415 : extension support (fun a => v (support a)) 415=v 415 :=
    extend_at support support_injective (fun a => v (support a)) 182
  have h465 : extension support (fun a => v (support a)) 465=v 465 :=
    extend_at support support_injective (fun a => v (support a)) 208
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  simp only [gridHeckeLeading,show gridHeckeP 71=3 from rfl,show gridHeckeT 71=(155:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h155,h415,h465,h615,h675]

theorem heckeSource_restrict_72 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 72=
      gridHeckeLeading m f s v 72 := by
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  simp only [gridHeckeLeading,show gridHeckeP 72=3 from rfl,show gridHeckeT 72=(160:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h160,h420,h480,h660,h680]

theorem heckeSource_restrict_73 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 73=
      gridHeckeLeading m f s v 73 := by
  have h165 : extension support (fun a => v (support a)) 165=v 165 :=
    extend_at support support_injective (fun a => v (support a)) 82
  have h425 : extension support (fun a => v (support a)) 425=v 425 :=
    extend_at support support_injective (fun a => v (support a)) 192
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  have h685 : extension support (fun a => v (support a)) 685=v 685 :=
    extend_at support support_injective (fun a => v (support a)) 257
  have h705 : extension support (fun a => v (support a)) 705=v 705 :=
    extend_at support support_injective (fun a => v (support a)) 262
  simp only [gridHeckeLeading,show gridHeckeP 73=3 from rfl,show gridHeckeT 73=(165:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h165,h425,h495,h685,h705]

theorem heckeSource_restrict_74 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 74=
      gridHeckeLeading m f s v 74 := by
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [gridHeckeLeading,show gridHeckeP 74=3 from rfl,show gridHeckeT 74=(170:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h170,h430,h510,h690,h750]

theorem heckeSource_restrict_75 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 75=
      gridHeckeLeading m f s v 75 := by
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  simp only [gridHeckeLeading,show gridHeckeP 75=3 from rfl,show gridHeckeT 75=(180:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h60,h180,h440,h540,h700]

theorem heckeSource_restrict_76 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 76=
      gridHeckeLeading m f s v 76 := by
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [gridHeckeLeading,show gridHeckeP 76=3 from rfl,show gridHeckeT 76=(182:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h78,h182,h442,h546,h702]

theorem heckeSource_restrict_77 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 77=
      gridHeckeLeading m f s v 77 := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h185 : extension support (fun a => v (support a)) 185=v 185 :=
    extend_at support support_injective (fun a => v (support a)) 86
  have h445 : extension support (fun a => v (support a)) 445=v 445 :=
    extend_at support support_injective (fun a => v (support a)) 202
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  have h705 : extension support (fun a => v (support a)) 705=v 705 :=
    extend_at support support_injective (fun a => v (support a)) 262
  simp only [gridHeckeLeading,show gridHeckeP 77=3 from rfl,show gridHeckeT 77=(185:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h185,h445,h555,h705]

theorem heckeSource_restrict_78 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 78=
      gridHeckeLeading m f s v 78 := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  simp only [gridHeckeLeading,show gridHeckeP 78=3 from rfl,show gridHeckeT 78=(190:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h190,h450,h570,h710]

theorem heckeSource_restrict_79 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 79=
      gridHeckeLeading m f s v 79 := by
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h455 : extension support (fun a => v (support a)) 455=v 455 :=
    extend_at support support_injective (fun a => v (support a)) 205
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  have h715 : extension support (fun a => v (support a)) 715=v 715 :=
    extend_at support support_injective (fun a => v (support a)) 267
  simp only [gridHeckeLeading,show gridHeckeP 79=3 from rfl,show gridHeckeT 79=(195:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h195,h455,h585,h715]

theorem heckeSource_restrict_80 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 80=
      gridHeckeLeading m f s v 80 := by
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [gridHeckeLeading,show gridHeckeP 80=3 from rfl,show gridHeckeT 80=(200:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h200,h240,h460,h600,h720]

theorem heckeSource_restrict_81 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 81=
      gridHeckeLeading m f s v 81 := by
  have h205 : extension support (fun a => v (support a)) 205=v 205 :=
    extend_at support support_injective (fun a => v (support a)) 90
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h465 : extension support (fun a => v (support a)) 465=v 465 :=
    extend_at support support_injective (fun a => v (support a)) 208
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  have h725 : extension support (fun a => v (support a)) 725=v 725 :=
    extend_at support support_injective (fun a => v (support a)) 277
  simp only [gridHeckeLeading,show gridHeckeP 81=3 from rfl,show gridHeckeT 81=(205:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h205,h285,h465,h615,h725]

theorem heckeSource_restrict_82 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 82=
      gridHeckeLeading m f s v 82 := by
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [gridHeckeLeading,show gridHeckeP 82=3 from rfl,show gridHeckeT 82=(208:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h208,h312,h468,h624,h728]

theorem heckeSource_restrict_83 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 83=
      gridHeckeLeading m f s v 83 := by
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  simp only [gridHeckeLeading,show gridHeckeP 83=3 from rfl,show gridHeckeT 83=(210:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h210,h330,h470,h630,h730]

theorem heckeSource_restrict_84 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 84=
      gridHeckeLeading m f s v 84 := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [gridHeckeLeading,show gridHeckeP 84=3 from rfl,show gridHeckeT 84=(220:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h420,h480,h660,h740]

theorem heckeSource_restrict_85 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 85=
      gridHeckeLeading m f s v 85 := by
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h465 : extension support (fun a => v (support a)) 465=v 465 :=
    extend_at support support_injective (fun a => v (support a)) 208
  have h485 : extension support (fun a => v (support a)) 485=v 485 :=
    extend_at support support_injective (fun a => v (support a)) 212
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  have h745 : extension support (fun a => v (support a)) 745=v 745 :=
    extend_at support support_injective (fun a => v (support a)) 289
  simp only [gridHeckeLeading,show gridHeckeP 85=3 from rfl,show gridHeckeT 85=(225:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h225,h465,h485,h675,h745]

theorem heckeSource_restrict_86 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 86=
      gridHeckeLeading m f s v 86 := by
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [gridHeckeLeading,show gridHeckeP 86=3 from rfl,show gridHeckeT 86=(230:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h230,h490,h510,h690,h750]

theorem heckeSource_restrict_87 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 87=
      gridHeckeLeading m f s v 87 := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  simp only [gridHeckeLeading,show gridHeckeP 87=3 from rfl,show gridHeckeT 87=(234:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h494,h546,h702,h754]

theorem heckeSource_restrict_88 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 88=
      gridHeckeLeading m f s v 88 := by
  have h235 : extension support (fun a => v (support a)) 235=v 235 :=
    extend_at support support_injective (fun a => v (support a)) 98
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  have h705 : extension support (fun a => v (support a)) 705=v 705 :=
    extend_at support support_injective (fun a => v (support a)) 262
  have h755 : extension support (fun a => v (support a)) 755=v 755 :=
    extend_at support support_injective (fun a => v (support a)) 298
  simp only [gridHeckeLeading,show gridHeckeP 88=3 from rfl,show gridHeckeT 88=(235:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h235,h495,h555,h705,h755]

theorem heckeSource_restrict_89 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 89=
      gridHeckeLeading m f s v 89 := by
  have h247 : extension support (fun a => v (support a)) 247=v 247 :=
    extend_at support support_injective (fun a => v (support a)) 100
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  have h741 : extension support (fun a => v (support a)) 741=v 741 :=
    extend_at support support_injective (fun a => v (support a)) 287
  have h767 : extension support (fun a => v (support a)) 767=v 767 :=
    extend_at support support_injective (fun a => v (support a)) 308
  simp only [gridHeckeLeading,show gridHeckeP 89=3 from rfl,show gridHeckeT 89=(247:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h247,h507,h663,h741,h767]

theorem heckeSource_restrict_90 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 90=
      gridHeckeLeading m f s v 90 := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [gridHeckeLeading,show gridHeckeP 90=5 from rfl,show gridHeckeT 90=(26:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h130,h182,h338,h494,h650]

theorem heckeSource_restrict_91 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 91=
      gridHeckeLeading m f s v 91 := by
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h351 : extension support (fun a => v (support a)) 351=v 351 :=
    extend_at support support_injective (fun a => v (support a)) 126
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  simp only [gridHeckeLeading,show gridHeckeP 91=5 from rfl,show gridHeckeT 91=(39:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h39,h195,h351,h507,h663]

theorem heckeSource_restrict_92 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 92=
      gridHeckeLeading m f s v 92 := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h364 : extension support (fun a => v (support a)) 364=v 364 :=
    extend_at support support_injective (fun a => v (support a)) 138
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  simp only [gridHeckeLeading,show gridHeckeP 92=5 from rfl,show gridHeckeT 92=(52:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h208,h260,h364,h520,h676]

theorem heckeSource_restrict_93 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 93=
      gridHeckeLeading m f s v 93 := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h416 : extension support (fun a => v (support a)) 416=v 416 :=
    extend_at support support_injective (fun a => v (support a)) 183
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [gridHeckeLeading,show gridHeckeP 93=5 from rfl,show gridHeckeT 93=(104:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h260,h416,h520,h572,h728]

theorem heckeSource_restrict_94 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 94=
      gridHeckeLeading m f s v 94 := by
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h429 : extension support (fun a => v (support a)) 429=v 429 :=
    extend_at support support_injective (fun a => v (support a)) 195
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  have h741 : extension support (fun a => v (support a)) 741=v 741 :=
    extend_at support support_injective (fun a => v (support a)) 287
  simp only [gridHeckeLeading,show gridHeckeP 94=5 from rfl,show gridHeckeT 94=(117:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h117,h273,h429,h585,h741]

theorem heckeSource_restrict_95 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 95=
      gridHeckeLeading m f s v 95 := by
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  simp only [gridHeckeLeading,show gridHeckeP 95=5 from rfl,show gridHeckeT 95=(130:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h130,h286,h442,h598,h650,h754]

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermRateDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

def groupPowers : Fin 235→ℤ×ℤ×ℤ×ℤ
  | 0 => (3, 2, -1, 2)
  | 1 => (-2, 0, 0, 0)
  | 2 => (2, 0, 0, -2)
  | 3 => (0, 0, 0, -2)
  | 4 => (-2, 0, 0, -2)
  | 5 => (-2, 0, 0, -2)
  | 6 => (0, 0, 0, -2)
  | 7 => (2, 0, 0, -2)
  | 8 => (-2, 0, 0, 0)
  | 9 => (0, 0, 0, 0)
  | 10 => (2, 0, 0, 0)
  | 11 => (-2, 0, 0, 2)
  | 12 => (0, 0, 0, 2)
  | 13 => (2, 0, 0, 2)
  | 14 => (3, 2, 0, 2)
  | 15 => (1, 2, 0, 2)
  | 16 => (-1, 2, 0, 2)
  | 17 => (-3, -2, 0, 0)
  | 18 => (-1, 0, 0, -2)
  | 19 => (1, 0, 0, 0)
  | 20 => (-1, -2, 0, 2)
  | 21 => (-3, 2, 0, 0)
  | 22 => (3, -2, 0, 0)
  | 23 => (1, 2, 0, -2)
  | 24 => (-1, 0, 0, 0)
  | 25 => (-3, -2, 0, 2)
  | 26 => (3, 0, 0, -2)
  | 27 => (1, -2, 0, 0)
  | 28 => (-1, 2, 0, -2)
  | 29 => (-3, 0, 0, 0)
  | 30 => (1, 0, 0, -2)
  | 31 => (-1, -2, 0, 0)
  | 32 => (-3, 2, 0, -2)
  | 33 => (3, -2, 0, -2)
  | 34 => (-1, 0, 0, -2)
  | 35 => (-3, -2, 0, 0)
  | 36 => (1, -2, 0, -2)
  | 37 => (-3, 0, 0, -2)
  | 38 => (-1, -2, 0, -2)
  | 39 => (-3, -2, 0, -2)
  | 40 => (-3, -2, 0, -2)
  | 41 => (-1, -2, 0, -2)
  | 42 => (-3, 0, 0, -2)
  | 43 => (1, -2, 0, -2)
  | 44 => (-3, -2, 0, 0)
  | 45 => (-1, 0, 0, -2)
  | 46 => (-3, 2, 0, -2)
  | 47 => (-1, -2, 0, 0)
  | 48 => (1, 0, 0, -2)
  | 49 => (-3, 0, 0, 0)
  | 50 => (-1, 2, 0, -2)
  | 51 => (1, -2, 0, 0)
  | 52 => (3, 0, 0, -2)
  | 53 => (-1, 0, 0, 0)
  | 54 => (1, 2, 0, -2)
  | 55 => (3, -2, 0, 0)
  | 56 => (-3, 2, 0, 0)
  | 57 => (-1, -2, 0, 2)
  | 58 => (1, 0, 0, 0)
  | 59 => (3, 2, 0, -2)
  | 60 => (-1, 2, 0, 0)
  | 61 => (1, -2, 0, 2)
  | 62 => (3, 0, 0, 0)
  | 63 => (-1, 0, 0, 2)
  | 64 => (1, 2, 0, 0)
  | 65 => (3, -2, 0, 2)
  | 66 => (-3, 2, 0, 2)
  | 67 => (1, 0, 0, 2)
  | 68 => (3, 2, 0, 0)
  | 69 => (-1, 2, 0, 2)
  | 70 => (3, 0, 0, 2)
  | 71 => (0, 0, 1, 2)
  | 72 => (0, 0, -1, 2)
  | 73 => (0, 0, 1, 2)
  | 74 => (0, 0, 1, 0)
  | 75 => (-2, -2, 1, 2)
  | 76 => (2, 0, -1, 2)
  | 77 => (2, -2, 1, 0)
  | 78 => (0, 2, 1, -2)
  | 79 => (-2, 2, -1, 2)
  | 80 => (-2, 0, 1, 0)
  | 81 => (2, 2, -1, 0)
  | 82 => (2, 0, 1, -2)
  | 83 => (0, 0, -1, 2)
  | 84 => (0, -2, 1, 0)
  | 85 => (-2, 2, 1, -2)
  | 86 => (2, -2, -1, 2)
  | 87 => (0, 2, -1, 0)
  | 88 => (0, 0, 1, -2)
  | 89 => (-2, 0, -1, 2)
  | 90 => (-2, -2, 1, 0)
  | 91 => (2, 0, -1, 0)
  | 92 => (2, -2, 1, -2)
  | 93 => (0, -2, -1, 2)
  | 94 => (-2, 2, -1, 0)
  | 95 => (2, 2, -1, -2)
  | 96 => (0, -2, 1, -2)
  | 97 => (-2, -2, -1, 2)
  | 98 => (2, -2, -1, 0)
  | 99 => (0, 2, -1, -2)
  | 100 => (-2, 0, -1, 0)
  | 101 => (-2, -2, 1, -2)
  | 102 => (2, 0, -1, -2)
  | 103 => (0, -2, -1, 0)
  | 104 => (-2, 2, -1, -2)
  | 105 => (0, 0, -1, -2)
  | 106 => (-2, -2, -1, 0)
  | 107 => (2, -2, -1, -2)
  | 108 => (-2, 0, -1, -2)
  | 109 => (0, -2, -1, -2)
  | 110 => (-2, -2, -1, -2)
  | 111 => (-2, -2, -1, -2)
  | 112 => (0, -2, -1, -2)
  | 113 => (-2, 0, -1, -2)
  | 114 => (2, -2, -1, -2)
  | 115 => (-2, -2, -1, 0)
  | 116 => (-2, 2, -1, -2)
  | 117 => (2, 0, -1, -2)
  | 118 => (-2, -2, 1, -2)
  | 119 => (0, 2, -1, -2)
  | 120 => (2, -2, -1, 0)
  | 121 => (-2, -2, -1, 2)
  | 122 => (1, 2, 0, 2)
  | 123 => (-3, -2, 0, -2)
  | 124 => (2, 0, 0, -2)
  | 125 => (-2, 2, 0, -2)
  | 126 => (-3, 2, 0, 2)
  | 127 => (3, -2, 0, 2)
  | 128 => (-1, 0, 0, 2)
  | 129 => (1, -2, 0, 2)
  | 130 => (-3, 0, 0, 2)
  | 131 => (-3, 2, 0, -2)
  | 132 => (3, -2, 0, -2)
  | 133 => (-3, -2, 0, -2)
  | 134 => (-3, -2, 0, -2)
  | 135 => (1, -2, 0, -2)
  | 136 => (-3, -2, 0, 0)
  | 137 => (3, -2, 0, -2)
  | 138 => (1, 0, 0, -2)
  | 139 => (-1, 2, 0, -2)
  | 140 => (1, -2, 0, 0)
  | 141 => (-3, -2, 0, 2)
  | 142 => (1, 2, 0, -2)
  | 143 => (3, -2, 0, 0)
  | 144 => (-3, 2, 0, 0)
  | 145 => (-1, -2, 0, 2)
  | 146 => (-3, 0, 0, 2)
  | 147 => (-1, 2, 0, 0)
  | 148 => (-1, 0, 0, 2)
  | 149 => (1, 2, 0, 0)
  | 150 => (3, -2, 0, 2)
  | 151 => (1, 0, 0, 2)
  | 152 => (-1, 2, 0, 2)
  | 153 => (3, 0, 0, 2)
  | 154 => (1, 2, 0, 2)
  | 155 => (2, 0, 0, 2)
  | 156 => (2, 2, 0, -2)
  | 157 => (0, 0, 0, 2)
  | 158 => (-3, 2, -1, -2)
  | 159 => (3, -2, -1, -2)
  | 160 => (-1, 0, -1, -2)
  | 161 => (1, -2, -1, -2)
  | 162 => (-3, 0, -1, -2)
  | 163 => (-1, -2, -1, -2)
  | 164 => (-3, -2, -1, -2)
  | 165 => (1, 0, 1, 0)
  | 166 => (3, 0, 1, 2)
  | 167 => (-3, -2, -1, -2)
  | 168 => (-1, -2, -1, -2)
  | 169 => (-3, 0, -1, -2)
  | 170 => (1, -2, -1, -2)
  | 171 => (-3, -2, 1, -2)
  | 172 => (3, -2, 1, -2)
  | 173 => (-3, 2, 1, -2)
  | 174 => (3, -2, -1, 2)
  | 175 => (-3, 2, -1, 2)
  | 176 => (3, 2, 1, 0)
  | 177 => (1, 2, -1, 2)
  | 178 => (0, 2, 0, 2)
  | 179 => (0, -2, 0, -2)
  | 180 => (2, 2, 0, 2)
  | 181 => (-1, -2, 0, -2)
  | 182 => (-3, -2, 0, -2)
  | 183 => (-3, -2, 0, -2)
  | 184 => (-1, -2, 0, -2)
  | 185 => (-3, 0, 0, -2)
  | 186 => (-1, 0, 0, -2)
  | 187 => (3, -2, 0, -2)
  | 188 => (-3, 2, 0, -2)
  | 189 => (1, -2, 0, 2)
  | 190 => (-3, 2, 0, -2)
  | 191 => (1, -2, 0, -2)
  | 192 => (-1, 0, 0, 0)
  | 193 => (-3, 2, 0, 2)
  | 194 => (1, 0, 0, -2)
  | 195 => (-1, 0, 0, -2)
  | 196 => (-3, 0, 0, -2)
  | 197 => (-3, 0, 0, -2)
  | 198 => (-1, 0, 0, -2)
  | 199 => (-3, 0, 0, 0)
  | 200 => (-1, 0, 0, 2)
  | 201 => (3, 0, 0, 2)
  | 202 => (0, -2, 0, -2)
  | 203 => (-2, 0, 0, -2)
  | 204 => (-2, 2, 0, -2)
  | 205 => (0, 2, 0, 2)
  | 206 => (3, 0, 0, 2)
  | 207 => (1, 0, 0, 2)
  | 208 => (-1, 0, 0, 2)
  | 209 => (1, 0, 0, 0)
  | 210 => (-1, 0, 0, -2)
  | 211 => (-3, 0, 0, -2)
  | 212 => (-1, 0, 0, -2)
  | 213 => (1, 0, 0, -2)
  | 214 => (3, 0, 0, -2)
  | 215 => (-1, 0, 0, 0)
  | 216 => (-3, 0, 0, 2)
  | 217 => (3, 0, 0, 0)
  | 218 => (-1, 0, 0, 2)
  | 219 => (1, 0, 0, 2)
  | 220 => (3, 0, 0, 2)
  | 221 => (-2, 2, 0, 2)
  | 222 => (2, -2, 0, -2)
  | 223 => (-2, 2, 0, -2)
  | 224 => (2, -2, 0, 2)
  | 225 => (0, -2, 1, -2)
  | 226 => (0, 2, 0, 2)
  | 227 => (0, 2, 0, 0)
  | 228 => (0, -2, 0, 2)
  | 229 => (0, 2, 0, -2)
  | 230 => (0, -2, 0, 0)
  | 231 => (0, -2, 0, -2)
  | 232 => (0, 0, 0, -2)
  | 233 => (0, 0, 0, 0)
  | _ => (0, 0, 0, 2)

def taylorPowers : Fin 53→ℤ×ℤ×ℤ×ℤ
  | 0 => (-1, 0, -1, 0)
  | 1 => (-1, 0, -1, 0)
  | 2 => (-3, 0, 1, -2)
  | 3 => (-3, 0, 1, -2)
  | 4 => (1, 0, -1, 0)
  | 5 => (1, 0, -1, 0)
  | 6 => (-3, 0, -1, 2)
  | 7 => (-3, 0, -1, 2)
  | 8 => (-1, 0, 1, -2)
  | 9 => (-1, 0, 1, -2)
  | 10 => (3, 0, -1, 0)
  | 11 => (3, 0, -1, 0)
  | 12 => (-1, 0, -1, 2)
  | 13 => (-1, 0, -1, 2)
  | 14 => (0, -2, -1, 0)
  | 15 => (0, -2, -1, 0)
  | 16 => (0, -2, 1, -2)
  | 17 => (0, -2, 1, -2)
  | 18 => (0, 0, -1, 0)
  | 19 => (0, 0, -1, 0)
  | 20 => (0, -2, -1, 2)
  | 21 => (0, -2, -1, 2)
  | 22 => (0, 0, 1, -2)
  | 23 => (0, 0, 1, -2)
  | 24 => (0, 2, -1, 0)
  | 25 => (0, 2, -1, 0)
  | 26 => (0, -2, 1, 0)
  | 27 => (0, 0, -1, 2)
  | 28 => (0, 0, -1, -2)
  | 29 => (0, 0, -1, -2)
  | 30 => (0, 0, -1, 0)
  | 31 => (0, 0, -1, 0)
  | 32 => (-2, 0, 1, -2)
  | 33 => (-2, 0, 1, -2)
  | 34 => (2, 0, -1, 0)
  | 35 => (2, 0, -1, 0)
  | 36 => (-2, 0, -1, 2)
  | 37 => (-2, 0, -1, 2)
  | 38 => (0, 0, 1, -2)
  | 39 => (0, 0, 1, -2)
  | 40 => (0, 0, -1, 0)
  | 41 => (0, 0, -1, 0)
  | 42 => (0, 0, -1, -2)
  | 43 => (0, 0, -1, -2)
  | 44 => (0, 0, -1, 0)
  | 45 => (0, 0, -1, 0)
  | 46 => (0, 0, 1, -2)
  | 47 => (0, 0, 1, -2)
  | 48 => (-1, -2, 0, 0)
  | 49 => (1, -2, 0, 0)
  | 50 => (-1, 0, 0, 0)
  | 51 => (0, -2, 0, 0)
  | _ => (0, 2, 0, 0)

def taylorRate (i : Fin 53) : ℚ := (gridTaylorL i:ℚ)*((gridTaylorT i:ℚ)/780)^2

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSignScalingTaylorBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid

theorem taylor_scale_sign_0 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 0 then -c else 1)*(-1))*u^(taylorPowers 0).1*v^(taylorPowers 0).2.2.1=
      ((if 2∣gridTaylorQ 0 then u else 1)*(if 13∣gridTaylorQ 0 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 0=3 from rfl,show taylorPowers 0=(-1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_1 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 1 then -c else 1)*(-1))*u^(taylorPowers 1).1*v^(taylorPowers 1).2.2.1=
      ((if 2∣gridTaylorQ 1 then u else 1)*(if 13∣gridTaylorQ 1 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 1=3 from rfl,show taylorPowers 1=(-1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_2 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 2 then -c else 1)*(-1))*u^(taylorPowers 2).1*v^(taylorPowers 2).2.2.1=
      ((if 2∣gridTaylorQ 2 then u else 1)*(if 13∣gridTaylorQ 2 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 2=3 from rfl,show taylorPowers 2=(-3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_3 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 3 then -c else 1)*(-1))*u^(taylorPowers 3).1*v^(taylorPowers 3).2.2.1=
      ((if 2∣gridTaylorQ 3 then u else 1)*(if 13∣gridTaylorQ 3 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 3=3 from rfl,show taylorPowers 3=(-3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_4 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 4 then -c else 1)*(-1))*u^(taylorPowers 4).1*v^(taylorPowers 4).2.2.1=
      ((if 2∣gridTaylorQ 4 then u else 1)*(if 13∣gridTaylorQ 4 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 4=3 from rfl,show taylorPowers 4=(1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_5 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 5 then -c else 1)*(-1))*u^(taylorPowers 5).1*v^(taylorPowers 5).2.2.1=
      ((if 2∣gridTaylorQ 5 then u else 1)*(if 13∣gridTaylorQ 5 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 5=3 from rfl,show taylorPowers 5=(1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_6 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 6 then -c else 1)*(-1))*u^(taylorPowers 6).1*v^(taylorPowers 6).2.2.1=
      ((if 2∣gridTaylorQ 6 then u else 1)*(if 13∣gridTaylorQ 6 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 6=3 from rfl,show taylorPowers 6=(-3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_7 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 7 then -c else 1)*(-1))*u^(taylorPowers 7).1*v^(taylorPowers 7).2.2.1=
      ((if 2∣gridTaylorQ 7 then u else 1)*(if 13∣gridTaylorQ 7 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 7=3 from rfl,show taylorPowers 7=(-3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_8 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 8 then -c else 1)*(-1))*u^(taylorPowers 8).1*v^(taylorPowers 8).2.2.1=
      ((if 2∣gridTaylorQ 8 then u else 1)*(if 13∣gridTaylorQ 8 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 8=3 from rfl,show taylorPowers 8=(-1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_9 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 9 then -c else 1)*(-1))*u^(taylorPowers 9).1*v^(taylorPowers 9).2.2.1=
      ((if 2∣gridTaylorQ 9 then u else 1)*(if 13∣gridTaylorQ 9 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 9=3 from rfl,show taylorPowers 9=(-1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_10 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 10 then -c else 1)*(-1))*u^(taylorPowers 10).1*v^(taylorPowers 10).2.2.1=
      ((if 2∣gridTaylorQ 10 then u else 1)*(if 13∣gridTaylorQ 10 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 10=3 from rfl,show taylorPowers 10=(3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_11 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 11 then -c else 1)*(-1))*u^(taylorPowers 11).1*v^(taylorPowers 11).2.2.1=
      ((if 2∣gridTaylorQ 11 then u else 1)*(if 13∣gridTaylorQ 11 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 11=3 from rfl,show taylorPowers 11=(3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_12 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 12 then -c else 1)*(-1))*u^(taylorPowers 12).1*v^(taylorPowers 12).2.2.1=
      ((if 2∣gridTaylorQ 12 then u else 1)*(if 13∣gridTaylorQ 12 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 12=3 from rfl,show taylorPowers 12=(-1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_13 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 13 then -c else 1)*(-1))*u^(taylorPowers 13).1*v^(taylorPowers 13).2.2.1=
      ((if 2∣gridTaylorQ 13 then u else 1)*(if 13∣gridTaylorQ 13 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 13=3 from rfl,show taylorPowers 13=(-1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_14 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 14 then -c else 1)*(-1))*u^(taylorPowers 14).1*v^(taylorPowers 14).2.2.1=
      ((if 2∣gridTaylorQ 14 then u else 1)*(if 13∣gridTaylorQ 14 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 14=4 from rfl,show taylorPowers 14=(0, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_15 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 15 then -c else 1)*(-1))*u^(taylorPowers 15).1*v^(taylorPowers 15).2.2.1=
      ((if 2∣gridTaylorQ 15 then u else 1)*(if 13∣gridTaylorQ 15 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 15=4 from rfl,show taylorPowers 15=(0, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_16 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 16 then -c else 1)*(-1))*u^(taylorPowers 16).1*v^(taylorPowers 16).2.2.1=
      ((if 2∣gridTaylorQ 16 then u else 1)*(if 13∣gridTaylorQ 16 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 16=4 from rfl,show taylorPowers 16=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_17 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 17 then -c else 1)*(-1))*u^(taylorPowers 17).1*v^(taylorPowers 17).2.2.1=
      ((if 2∣gridTaylorQ 17 then u else 1)*(if 13∣gridTaylorQ 17 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 17=4 from rfl,show taylorPowers 17=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_18 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 18 then -c else 1)*(-1))*u^(taylorPowers 18).1*v^(taylorPowers 18).2.2.1=
      ((if 2∣gridTaylorQ 18 then u else 1)*(if 13∣gridTaylorQ 18 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 18=4 from rfl,show taylorPowers 18=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_19 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 19 then -c else 1)*(-1))*u^(taylorPowers 19).1*v^(taylorPowers 19).2.2.1=
      ((if 2∣gridTaylorQ 19 then u else 1)*(if 13∣gridTaylorQ 19 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 19=4 from rfl,show taylorPowers 19=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_20 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 20 then -c else 1)*(-1))*u^(taylorPowers 20).1*v^(taylorPowers 20).2.2.1=
      ((if 2∣gridTaylorQ 20 then u else 1)*(if 13∣gridTaylorQ 20 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 20=4 from rfl,show taylorPowers 20=(0, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_21 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 21 then -c else 1)*(-1))*u^(taylorPowers 21).1*v^(taylorPowers 21).2.2.1=
      ((if 2∣gridTaylorQ 21 then u else 1)*(if 13∣gridTaylorQ 21 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 21=4 from rfl,show taylorPowers 21=(0, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_22 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 22 then -c else 1)*(-1))*u^(taylorPowers 22).1*v^(taylorPowers 22).2.2.1=
      ((if 2∣gridTaylorQ 22 then u else 1)*(if 13∣gridTaylorQ 22 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 22=4 from rfl,show taylorPowers 22=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_23 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 23 then -c else 1)*(-1))*u^(taylorPowers 23).1*v^(taylorPowers 23).2.2.1=
      ((if 2∣gridTaylorQ 23 then u else 1)*(if 13∣gridTaylorQ 23 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 23=4 from rfl,show taylorPowers 23=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_24 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 24 then -c else 1)*(-1))*u^(taylorPowers 24).1*v^(taylorPowers 24).2.2.1=
      ((if 2∣gridTaylorQ 24 then u else 1)*(if 13∣gridTaylorQ 24 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 24=4 from rfl,show taylorPowers 24=(0, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_25 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 25 then -c else 1)*(-1))*u^(taylorPowers 25).1*v^(taylorPowers 25).2.2.1=
      ((if 2∣gridTaylorQ 25 then u else 1)*(if 13∣gridTaylorQ 25 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 25=4 from rfl,show taylorPowers 25=(0, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_26 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 26 then -c else 1)*(-1))*u^(taylorPowers 26).1*v^(taylorPowers 26).2.2.1=
      ((if 2∣gridTaylorQ 26 then u else 1)*(if 13∣gridTaylorQ 26 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 26=4 from rfl,show taylorPowers 26=(0, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_27 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 27 then -c else 1)*(-1))*u^(taylorPowers 27).1*v^(taylorPowers 27).2.2.1=
      ((if 2∣gridTaylorQ 27 then u else 1)*(if 13∣gridTaylorQ 27 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 27=4 from rfl,show taylorPowers 27=(0, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_28 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 28 then -c else 1)*(-1))*u^(taylorPowers 28).1*v^(taylorPowers 28).2.2.1=
      ((if 2∣gridTaylorQ 28 then u else 1)*(if 13∣gridTaylorQ 28 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 28=6 from rfl,show taylorPowers 28=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_29 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 29 then -c else 1)*(-1))*u^(taylorPowers 29).1*v^(taylorPowers 29).2.2.1=
      ((if 2∣gridTaylorQ 29 then u else 1)*(if 13∣gridTaylorQ 29 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 29=6 from rfl,show taylorPowers 29=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_30 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 30 then -c else 1)*(-1))*u^(taylorPowers 30).1*v^(taylorPowers 30).2.2.1=
      ((if 2∣gridTaylorQ 30 then u else 1)*(if 13∣gridTaylorQ 30 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 30=6 from rfl,show taylorPowers 30=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_31 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 31 then -c else 1)*(-1))*u^(taylorPowers 31).1*v^(taylorPowers 31).2.2.1=
      ((if 2∣gridTaylorQ 31 then u else 1)*(if 13∣gridTaylorQ 31 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 31=6 from rfl,show taylorPowers 31=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_32 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 32 then -c else 1)*(-1))*u^(taylorPowers 32).1*v^(taylorPowers 32).2.2.1=
      ((if 2∣gridTaylorQ 32 then u else 1)*(if 13∣gridTaylorQ 32 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 32=6 from rfl,show taylorPowers 32=(-2, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_33 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 33 then -c else 1)*(-1))*u^(taylorPowers 33).1*v^(taylorPowers 33).2.2.1=
      ((if 2∣gridTaylorQ 33 then u else 1)*(if 13∣gridTaylorQ 33 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 33=6 from rfl,show taylorPowers 33=(-2, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_34 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 34 then -c else 1)*(-1))*u^(taylorPowers 34).1*v^(taylorPowers 34).2.2.1=
      ((if 2∣gridTaylorQ 34 then u else 1)*(if 13∣gridTaylorQ 34 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 34=6 from rfl,show taylorPowers 34=(2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_35 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 35 then -c else 1)*(-1))*u^(taylorPowers 35).1*v^(taylorPowers 35).2.2.1=
      ((if 2∣gridTaylorQ 35 then u else 1)*(if 13∣gridTaylorQ 35 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 35=6 from rfl,show taylorPowers 35=(2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_36 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 36 then -c else 1)*(-1))*u^(taylorPowers 36).1*v^(taylorPowers 36).2.2.1=
      ((if 2∣gridTaylorQ 36 then u else 1)*(if 13∣gridTaylorQ 36 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 36=6 from rfl,show taylorPowers 36=(-2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_37 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 37 then -c else 1)*(-1))*u^(taylorPowers 37).1*v^(taylorPowers 37).2.2.1=
      ((if 2∣gridTaylorQ 37 then u else 1)*(if 13∣gridTaylorQ 37 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 37=6 from rfl,show taylorPowers 37=(-2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_38 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 38 then -c else 1)*(-1))*u^(taylorPowers 38).1*v^(taylorPowers 38).2.2.1=
      ((if 2∣gridTaylorQ 38 then u else 1)*(if 13∣gridTaylorQ 38 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 38=6 from rfl,show taylorPowers 38=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_39 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 39 then -c else 1)*(-1))*u^(taylorPowers 39).1*v^(taylorPowers 39).2.2.1=
      ((if 2∣gridTaylorQ 39 then u else 1)*(if 13∣gridTaylorQ 39 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 39=6 from rfl,show taylorPowers 39=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_40 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 40 then -c else 1)*(-1))*u^(taylorPowers 40).1*v^(taylorPowers 40).2.2.1=
      ((if 2∣gridTaylorQ 40 then u else 1)*(if 13∣gridTaylorQ 40 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 40=10 from rfl,show taylorPowers 40=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_41 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 41 then -c else 1)*(-1))*u^(taylorPowers 41).1*v^(taylorPowers 41).2.2.1=
      ((if 2∣gridTaylorQ 41 then u else 1)*(if 13∣gridTaylorQ 41 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 41=10 from rfl,show taylorPowers 41=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_42 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 42 then -c else 1)*(-1))*u^(taylorPowers 42).1*v^(taylorPowers 42).2.2.1=
      ((if 2∣gridTaylorQ 42 then u else 1)*(if 13∣gridTaylorQ 42 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 42=12 from rfl,show taylorPowers 42=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_43 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 43 then -c else 1)*(-1))*u^(taylorPowers 43).1*v^(taylorPowers 43).2.2.1=
      ((if 2∣gridTaylorQ 43 then u else 1)*(if 13∣gridTaylorQ 43 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 43=12 from rfl,show taylorPowers 43=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_44 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 44 then -c else 1)*(-1))*u^(taylorPowers 44).1*v^(taylorPowers 44).2.2.1=
      ((if 2∣gridTaylorQ 44 then u else 1)*(if 13∣gridTaylorQ 44 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 44=12 from rfl,show taylorPowers 44=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_45 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 45 then -c else 1)*(-1))*u^(taylorPowers 45).1*v^(taylorPowers 45).2.2.1=
      ((if 2∣gridTaylorQ 45 then u else 1)*(if 13∣gridTaylorQ 45 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 45=12 from rfl,show taylorPowers 45=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_46 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 46 then -c else 1)*(-1))*u^(taylorPowers 46).1*v^(taylorPowers 46).2.2.1=
      ((if 2∣gridTaylorQ 46 then u else 1)*(if 13∣gridTaylorQ 46 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 46=12 from rfl,show taylorPowers 46=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_47 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 47 then -c else 1)*(-1))*u^(taylorPowers 47).1*v^(taylorPowers 47).2.2.1=
      ((if 2∣gridTaylorQ 47 then u else 1)*(if 13∣gridTaylorQ 47 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 47=12 from rfl,show taylorPowers 47=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_48 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 48 then -c else 1)*(-1))*u^(taylorPowers 48).1*v^(taylorPowers 48).2.2.1=
      ((if 2∣gridTaylorQ 48 then u else 1)*(if 13∣gridTaylorQ 48 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 48=13 from rfl,show taylorPowers 48=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_49 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 49 then -c else 1)*(-1))*u^(taylorPowers 49).1*v^(taylorPowers 49).2.2.1=
      ((if 2∣gridTaylorQ 49 then u else 1)*(if 13∣gridTaylorQ 49 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 49=13 from rfl,show taylorPowers 49=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_50 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 50 then -c else 1)*(-1))*u^(taylorPowers 50).1*v^(taylorPowers 50).2.2.1=
      ((if 2∣gridTaylorQ 50 then u else 1)*(if 13∣gridTaylorQ 50 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 50=13 from rfl,show taylorPowers 50=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_51 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 51 then -c else 1)*(-1))*u^(taylorPowers 51).1*v^(taylorPowers 51).2.2.1=
      ((if 2∣gridTaylorQ 51 then u else 1)*(if 13∣gridTaylorQ 51 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 51=52 from rfl,show taylorPowers 51=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_52 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 52 then -c else 1)*(-1))*u^(taylorPowers 52).1*v^(taylorPowers 52).2.2.1=
      ((if 2∣gridTaylorQ 52 then u else 1)*(if 13∣gridTaylorQ 52 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 52=52 from rfl,show taylorPowers 52=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSignScalingWordBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid

theorem word_scale_sign_0 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 0))*u^(groupPowers 0).1*v^(groupPowers 0).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 0)) := by
  simp only [show gridGroupSource 0=(25:Fin 32) from rfl,
    show sourceWord 25=[(3,false),(0,false),(0,false)] from rfl,show groupPowers 0=(3, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_1 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 1))*u^(groupPowers 1).1*v^(groupPowers 1).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 1)) := by
  simp only [show gridGroupSource 1=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 1=(-2, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_2 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 2))*u^(groupPowers 2).1*v^(groupPowers 2).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 2)) := by
  simp only [show gridGroupSource 2=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 2=(2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_3 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 3))*u^(groupPowers 3).1*v^(groupPowers 3).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 3)) := by
  simp only [show gridGroupSource 3=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 3=(0, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_4 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 4))*u^(groupPowers 4).1*v^(groupPowers 4).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 4)) := by
  simp only [show gridGroupSource 4=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 4=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_5 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 5))*u^(groupPowers 5).1*v^(groupPowers 5).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 5)) := by
  simp only [show gridGroupSource 5=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 5=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_6 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 6))*u^(groupPowers 6).1*v^(groupPowers 6).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 6)) := by
  simp only [show gridGroupSource 6=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 6=(0, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_7 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 7))*u^(groupPowers 7).1*v^(groupPowers 7).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 7)) := by
  simp only [show gridGroupSource 7=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 7=(2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_8 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 8))*u^(groupPowers 8).1*v^(groupPowers 8).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 8)) := by
  simp only [show gridGroupSource 8=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 8=(-2, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_9 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 9))*u^(groupPowers 9).1*v^(groupPowers 9).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 9)) := by
  simp only [show gridGroupSource 9=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 9=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_10 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 10))*u^(groupPowers 10).1*v^(groupPowers 10).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 10)) := by
  simp only [show gridGroupSource 10=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 10=(2, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_11 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 11))*u^(groupPowers 11).1*v^(groupPowers 11).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 11)) := by
  simp only [show gridGroupSource 11=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 11=(-2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_12 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 12))*u^(groupPowers 12).1*v^(groupPowers 12).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 12)) := by
  simp only [show gridGroupSource 12=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 12=(0, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_13 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 13))*u^(groupPowers 13).1*v^(groupPowers 13).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 13)) := by
  simp only [show gridGroupSource 13=(15:Fin 32) from rfl,
    show sourceWord 15=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 13=(2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_14 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 14))*u^(groupPowers 14).1*v^(groupPowers 14).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 14)) := by
  simp only [show gridGroupSource 14=(18:Fin 32) from rfl,
    show sourceWord 18=[(2,false),(0,true),(0,true)] from rfl,show groupPowers 14=(3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_15 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 15))*u^(groupPowers 15).1*v^(groupPowers 15).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 15)) := by
  simp only [show gridGroupSource 15=(17:Fin 32) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,show groupPowers 15=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_16 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 16))*u^(groupPowers 16).1*v^(groupPowers 16).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 16)) := by
  simp only [show gridGroupSource 16=(17:Fin 32) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,show groupPowers 16=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_17 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 17))*u^(groupPowers 17).1*v^(groupPowers 17).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 17)) := by
  simp only [show gridGroupSource 17=(16:Fin 32) from rfl,
    show sourceWord 16=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 17=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_18 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 18))*u^(groupPowers 18).1*v^(groupPowers 18).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 18)) := by
  simp only [show gridGroupSource 18=(11:Fin 32) from rfl,
    show sourceWord 11=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 18=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_19 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 19))*u^(groupPowers 19).1*v^(groupPowers 19).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 19)) := by
  simp only [show gridGroupSource 19=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 19=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_20 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 20))*u^(groupPowers 20).1*v^(groupPowers 20).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 20)) := by
  simp only [show gridGroupSource 20=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 20=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_21 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 21))*u^(groupPowers 21).1*v^(groupPowers 21).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 21)) := by
  simp only [show gridGroupSource 21=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 21=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_22 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 22))*u^(groupPowers 22).1*v^(groupPowers 22).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 22)) := by
  simp only [show gridGroupSource 22=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 22=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_23 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 23))*u^(groupPowers 23).1*v^(groupPowers 23).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 23)) := by
  simp only [show gridGroupSource 23=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 23=(1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_24 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 24))*u^(groupPowers 24).1*v^(groupPowers 24).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 24)) := by
  simp only [show gridGroupSource 24=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 24=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_25 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 25))*u^(groupPowers 25).1*v^(groupPowers 25).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 25)) := by
  simp only [show gridGroupSource 25=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 25=(-3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_26 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 26))*u^(groupPowers 26).1*v^(groupPowers 26).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 26)) := by
  simp only [show gridGroupSource 26=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 26=(3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_27 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 27))*u^(groupPowers 27).1*v^(groupPowers 27).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 27)) := by
  simp only [show gridGroupSource 27=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 27=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_28 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 28))*u^(groupPowers 28).1*v^(groupPowers 28).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 28)) := by
  simp only [show gridGroupSource 28=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 28=(-1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_29 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 29))*u^(groupPowers 29).1*v^(groupPowers 29).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 29)) := by
  simp only [show gridGroupSource 29=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 29=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_30 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 30))*u^(groupPowers 30).1*v^(groupPowers 30).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 30)) := by
  simp only [show gridGroupSource 30=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 30=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_31 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 31))*u^(groupPowers 31).1*v^(groupPowers 31).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 31)) := by
  simp only [show gridGroupSource 31=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 31=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_32 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 32))*u^(groupPowers 32).1*v^(groupPowers 32).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 32)) := by
  simp only [show gridGroupSource 32=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 32=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_33 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 33))*u^(groupPowers 33).1*v^(groupPowers 33).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 33)) := by
  simp only [show gridGroupSource 33=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 33=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_34 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 34))*u^(groupPowers 34).1*v^(groupPowers 34).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 34)) := by
  simp only [show gridGroupSource 34=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 34=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_35 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 35))*u^(groupPowers 35).1*v^(groupPowers 35).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 35)) := by
  simp only [show gridGroupSource 35=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 35=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_36 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 36))*u^(groupPowers 36).1*v^(groupPowers 36).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 36)) := by
  simp only [show gridGroupSource 36=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 36=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_37 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 37))*u^(groupPowers 37).1*v^(groupPowers 37).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 37)) := by
  simp only [show gridGroupSource 37=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 37=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_38 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 38))*u^(groupPowers 38).1*v^(groupPowers 38).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 38)) := by
  simp only [show gridGroupSource 38=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 38=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_39 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 39))*u^(groupPowers 39).1*v^(groupPowers 39).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 39)) := by
  simp only [show gridGroupSource 39=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 39=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_40 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 40))*u^(groupPowers 40).1*v^(groupPowers 40).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 40)) := by
  simp only [show gridGroupSource 40=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 40=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_41 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 41))*u^(groupPowers 41).1*v^(groupPowers 41).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 41)) := by
  simp only [show gridGroupSource 41=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 41=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_42 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 42))*u^(groupPowers 42).1*v^(groupPowers 42).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 42)) := by
  simp only [show gridGroupSource 42=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 42=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_43 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 43))*u^(groupPowers 43).1*v^(groupPowers 43).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 43)) := by
  simp only [show gridGroupSource 43=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 43=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_44 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 44))*u^(groupPowers 44).1*v^(groupPowers 44).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 44)) := by
  simp only [show gridGroupSource 44=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 44=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_45 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 45))*u^(groupPowers 45).1*v^(groupPowers 45).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 45)) := by
  simp only [show gridGroupSource 45=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 45=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_46 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 46))*u^(groupPowers 46).1*v^(groupPowers 46).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 46)) := by
  simp only [show gridGroupSource 46=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 46=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_47 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 47))*u^(groupPowers 47).1*v^(groupPowers 47).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 47)) := by
  simp only [show gridGroupSource 47=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 47=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_48 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 48))*u^(groupPowers 48).1*v^(groupPowers 48).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 48)) := by
  simp only [show gridGroupSource 48=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 48=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_49 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 49))*u^(groupPowers 49).1*v^(groupPowers 49).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 49)) := by
  simp only [show gridGroupSource 49=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 49=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_50 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 50))*u^(groupPowers 50).1*v^(groupPowers 50).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 50)) := by
  simp only [show gridGroupSource 50=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 50=(-1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_51 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 51))*u^(groupPowers 51).1*v^(groupPowers 51).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 51)) := by
  simp only [show gridGroupSource 51=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 51=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_52 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 52))*u^(groupPowers 52).1*v^(groupPowers 52).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 52)) := by
  simp only [show gridGroupSource 52=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 52=(3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_53 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 53))*u^(groupPowers 53).1*v^(groupPowers 53).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 53)) := by
  simp only [show gridGroupSource 53=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 53=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_54 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 54))*u^(groupPowers 54).1*v^(groupPowers 54).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 54)) := by
  simp only [show gridGroupSource 54=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 54=(1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_55 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 55))*u^(groupPowers 55).1*v^(groupPowers 55).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 55)) := by
  simp only [show gridGroupSource 55=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 55=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_56 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 56))*u^(groupPowers 56).1*v^(groupPowers 56).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 56)) := by
  simp only [show gridGroupSource 56=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 56=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_57 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 57))*u^(groupPowers 57).1*v^(groupPowers 57).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 57)) := by
  simp only [show gridGroupSource 57=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 57=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_58 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 58))*u^(groupPowers 58).1*v^(groupPowers 58).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 58)) := by
  simp only [show gridGroupSource 58=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 58=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_59 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 59))*u^(groupPowers 59).1*v^(groupPowers 59).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 59)) := by
  simp only [show gridGroupSource 59=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 59=(3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_60 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 60))*u^(groupPowers 60).1*v^(groupPowers 60).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 60)) := by
  simp only [show gridGroupSource 60=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 60=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_61 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 61))*u^(groupPowers 61).1*v^(groupPowers 61).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 61)) := by
  simp only [show gridGroupSource 61=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 61=(1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_62 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 62))*u^(groupPowers 62).1*v^(groupPowers 62).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 62)) := by
  simp only [show gridGroupSource 62=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 62=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_63 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 63))*u^(groupPowers 63).1*v^(groupPowers 63).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 63)) := by
  simp only [show gridGroupSource 63=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 63=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_64 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 64))*u^(groupPowers 64).1*v^(groupPowers 64).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 64)) := by
  simp only [show gridGroupSource 64=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 64=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_65 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 65))*u^(groupPowers 65).1*v^(groupPowers 65).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 65)) := by
  simp only [show gridGroupSource 65=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 65=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_66 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 66))*u^(groupPowers 66).1*v^(groupPowers 66).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 66)) := by
  simp only [show gridGroupSource 66=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 66=(-3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_67 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 67))*u^(groupPowers 67).1*v^(groupPowers 67).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 67)) := by
  simp only [show gridGroupSource 67=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 67=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_68 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 68))*u^(groupPowers 68).1*v^(groupPowers 68).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 68)) := by
  simp only [show gridGroupSource 68=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 68=(3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_69 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 69))*u^(groupPowers 69).1*v^(groupPowers 69).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 69)) := by
  simp only [show gridGroupSource 69=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 69=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_70 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 70))*u^(groupPowers 70).1*v^(groupPowers 70).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 70)) := by
  simp only [show gridGroupSource 70=(23:Fin 32) from rfl,
    show sourceWord 23=[(2,true),(1,true)] from rfl,show groupPowers 70=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_71 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 71))*u^(groupPowers 71).1*v^(groupPowers 71).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 71)) := by
  simp only [show gridGroupSource 71=(27:Fin 32) from rfl,
    show sourceWord 27=[(3,false),(0,false),(2,false)] from rfl,show groupPowers 71=(0, 0, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_72 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 72))*u^(groupPowers 72).1*v^(groupPowers 72).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 72)) := by
  simp only [show gridGroupSource 72=(27:Fin 32) from rfl,
    show sourceWord 27=[(3,false),(0,false),(2,false)] from rfl,show groupPowers 72=(0, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_73 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 73))*u^(groupPowers 73).1*v^(groupPowers 73).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 73)) := by
  simp only [show gridGroupSource 73=(27:Fin 32) from rfl,
    show sourceWord 27=[(3,false),(0,false),(2,false)] from rfl,show groupPowers 73=(0, 0, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_74 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 74))*u^(groupPowers 74).1*v^(groupPowers 74).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 74)) := by
  simp only [show gridGroupSource 74=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 74=(0, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_75 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 75))*u^(groupPowers 75).1*v^(groupPowers 75).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 75)) := by
  simp only [show gridGroupSource 75=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 75=(-2, -2, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_76 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 76))*u^(groupPowers 76).1*v^(groupPowers 76).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 76)) := by
  simp only [show gridGroupSource 76=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 76=(2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_77 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 77))*u^(groupPowers 77).1*v^(groupPowers 77).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 77)) := by
  simp only [show gridGroupSource 77=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 77=(2, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_78 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 78))*u^(groupPowers 78).1*v^(groupPowers 78).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 78)) := by
  simp only [show gridGroupSource 78=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 78=(0, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_79 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 79))*u^(groupPowers 79).1*v^(groupPowers 79).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 79)) := by
  simp only [show gridGroupSource 79=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 79=(-2, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_80 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 80))*u^(groupPowers 80).1*v^(groupPowers 80).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 80)) := by
  simp only [show gridGroupSource 80=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 80=(-2, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_81 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 81))*u^(groupPowers 81).1*v^(groupPowers 81).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 81)) := by
  simp only [show gridGroupSource 81=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 81=(2, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_82 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 82))*u^(groupPowers 82).1*v^(groupPowers 82).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 82)) := by
  simp only [show gridGroupSource 82=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 82=(2, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_83 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 83))*u^(groupPowers 83).1*v^(groupPowers 83).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 83)) := by
  simp only [show gridGroupSource 83=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 83=(0, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_84 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 84))*u^(groupPowers 84).1*v^(groupPowers 84).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 84)) := by
  simp only [show gridGroupSource 84=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 84=(0, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_85 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 85))*u^(groupPowers 85).1*v^(groupPowers 85).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 85)) := by
  simp only [show gridGroupSource 85=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 85=(-2, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_86 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 86))*u^(groupPowers 86).1*v^(groupPowers 86).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 86)) := by
  simp only [show gridGroupSource 86=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 86=(2, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_87 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 87))*u^(groupPowers 87).1*v^(groupPowers 87).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 87)) := by
  simp only [show gridGroupSource 87=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 87=(0, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_88 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 88))*u^(groupPowers 88).1*v^(groupPowers 88).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 88)) := by
  simp only [show gridGroupSource 88=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 88=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_89 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 89))*u^(groupPowers 89).1*v^(groupPowers 89).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 89)) := by
  simp only [show gridGroupSource 89=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 89=(-2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_90 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 90))*u^(groupPowers 90).1*v^(groupPowers 90).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 90)) := by
  simp only [show gridGroupSource 90=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 90=(-2, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_91 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 91))*u^(groupPowers 91).1*v^(groupPowers 91).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 91)) := by
  simp only [show gridGroupSource 91=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 91=(2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_92 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 92))*u^(groupPowers 92).1*v^(groupPowers 92).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 92)) := by
  simp only [show gridGroupSource 92=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 92=(2, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_93 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 93))*u^(groupPowers 93).1*v^(groupPowers 93).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 93)) := by
  simp only [show gridGroupSource 93=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 93=(0, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_94 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 94))*u^(groupPowers 94).1*v^(groupPowers 94).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 94)) := by
  simp only [show gridGroupSource 94=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 94=(-2, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_95 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 95))*u^(groupPowers 95).1*v^(groupPowers 95).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 95)) := by
  simp only [show gridGroupSource 95=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 95=(2, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_96 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 96))*u^(groupPowers 96).1*v^(groupPowers 96).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 96)) := by
  simp only [show gridGroupSource 96=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 96=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_97 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 97))*u^(groupPowers 97).1*v^(groupPowers 97).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 97)) := by
  simp only [show gridGroupSource 97=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 97=(-2, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_98 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 98))*u^(groupPowers 98).1*v^(groupPowers 98).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 98)) := by
  simp only [show gridGroupSource 98=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 98=(2, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_99 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 99))*u^(groupPowers 99).1*v^(groupPowers 99).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 99)) := by
  simp only [show gridGroupSource 99=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 99=(0, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_100 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 100))*u^(groupPowers 100).1*v^(groupPowers 100).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 100)) := by
  simp only [show gridGroupSource 100=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 100=(-2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_101 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 101))*u^(groupPowers 101).1*v^(groupPowers 101).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 101)) := by
  simp only [show gridGroupSource 101=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 101=(-2, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_102 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 102))*u^(groupPowers 102).1*v^(groupPowers 102).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 102)) := by
  simp only [show gridGroupSource 102=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 102=(2, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_103 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 103))*u^(groupPowers 103).1*v^(groupPowers 103).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 103)) := by
  simp only [show gridGroupSource 103=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 103=(0, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_104 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 104))*u^(groupPowers 104).1*v^(groupPowers 104).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 104)) := by
  simp only [show gridGroupSource 104=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 104=(-2, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_105 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 105))*u^(groupPowers 105).1*v^(groupPowers 105).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 105)) := by
  simp only [show gridGroupSource 105=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 105=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_106 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 106))*u^(groupPowers 106).1*v^(groupPowers 106).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 106)) := by
  simp only [show gridGroupSource 106=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 106=(-2, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_107 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 107))*u^(groupPowers 107).1*v^(groupPowers 107).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 107)) := by
  simp only [show gridGroupSource 107=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 107=(2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_108 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 108))*u^(groupPowers 108).1*v^(groupPowers 108).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 108)) := by
  simp only [show gridGroupSource 108=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 108=(-2, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_109 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 109))*u^(groupPowers 109).1*v^(groupPowers 109).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 109)) := by
  simp only [show gridGroupSource 109=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 109=(0, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_110 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 110))*u^(groupPowers 110).1*v^(groupPowers 110).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 110)) := by
  simp only [show gridGroupSource 110=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 110=(-2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_111 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 111))*u^(groupPowers 111).1*v^(groupPowers 111).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 111)) := by
  simp only [show gridGroupSource 111=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 111=(-2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_112 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 112))*u^(groupPowers 112).1*v^(groupPowers 112).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 112)) := by
  simp only [show gridGroupSource 112=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 112=(0, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_113 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 113))*u^(groupPowers 113).1*v^(groupPowers 113).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 113)) := by
  simp only [show gridGroupSource 113=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 113=(-2, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_114 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 114))*u^(groupPowers 114).1*v^(groupPowers 114).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 114)) := by
  simp only [show gridGroupSource 114=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 114=(2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_115 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 115))*u^(groupPowers 115).1*v^(groupPowers 115).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 115)) := by
  simp only [show gridGroupSource 115=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 115=(-2, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_116 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 116))*u^(groupPowers 116).1*v^(groupPowers 116).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 116)) := by
  simp only [show gridGroupSource 116=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 116=(-2, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_117 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 117))*u^(groupPowers 117).1*v^(groupPowers 117).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 117)) := by
  simp only [show gridGroupSource 117=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 117=(2, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_118 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 118))*u^(groupPowers 118).1*v^(groupPowers 118).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 118)) := by
  simp only [show gridGroupSource 118=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 118=(-2, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_119 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 119))*u^(groupPowers 119).1*v^(groupPowers 119).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 119)) := by
  simp only [show gridGroupSource 119=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 119=(0, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_120 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 120))*u^(groupPowers 120).1*v^(groupPowers 120).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 120)) := by
  simp only [show gridGroupSource 120=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 120=(2, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_121 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 121))*u^(groupPowers 121).1*v^(groupPowers 121).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 121)) := by
  simp only [show gridGroupSource 121=(10:Fin 32) from rfl,
    show sourceWord 10=[(0,true),(2,true),(3,false)] from rfl,show groupPowers 121=(-2, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_122 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 122))*u^(groupPowers 122).1*v^(groupPowers 122).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 122)) := by
  simp only [show gridGroupSource 122=(21:Fin 32) from rfl,
    show sourceWord 21=[(2,true),(0,true),(0,true)] from rfl,show groupPowers 122=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_123 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 123))*u^(groupPowers 123).1*v^(groupPowers 123).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 123)) := by
  simp only [show gridGroupSource 123=(20:Fin 32) from rfl,
    show sourceWord 20=[(2,true),(0,true)] from rfl,show groupPowers 123=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_124 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 124))*u^(groupPowers 124).1*v^(groupPowers 124).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 124)) := by
  simp only [show gridGroupSource 124=(13:Fin 32) from rfl,
    show sourceWord 13=[(1,false),(2,false),(2,false)] from rfl,show groupPowers 124=(2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_125 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 125))*u^(groupPowers 125).1*v^(groupPowers 125).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 125)) := by
  simp only [show gridGroupSource 125=(13:Fin 32) from rfl,
    show sourceWord 13=[(1,false),(2,false),(2,false)] from rfl,show groupPowers 125=(-2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_126 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 126))*u^(groupPowers 126).1*v^(groupPowers 126).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 126)) := by
  simp only [show gridGroupSource 126=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 126=(-3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_127 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 127))*u^(groupPowers 127).1*v^(groupPowers 127).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 127)) := by
  simp only [show gridGroupSource 127=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 127=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_128 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 128))*u^(groupPowers 128).1*v^(groupPowers 128).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 128)) := by
  simp only [show gridGroupSource 128=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 128=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_129 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 129))*u^(groupPowers 129).1*v^(groupPowers 129).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 129)) := by
  simp only [show gridGroupSource 129=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 129=(1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_130 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 130))*u^(groupPowers 130).1*v^(groupPowers 130).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 130)) := by
  simp only [show gridGroupSource 130=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 130=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_131 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 131))*u^(groupPowers 131).1*v^(groupPowers 131).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 131)) := by
  simp only [show gridGroupSource 131=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 131=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_132 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 132))*u^(groupPowers 132).1*v^(groupPowers 132).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 132)) := by
  simp only [show gridGroupSource 132=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 132=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_133 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 133))*u^(groupPowers 133).1*v^(groupPowers 133).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 133)) := by
  simp only [show gridGroupSource 133=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 133=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_134 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 134))*u^(groupPowers 134).1*v^(groupPowers 134).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 134)) := by
  simp only [show gridGroupSource 134=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 134=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_135 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 135))*u^(groupPowers 135).1*v^(groupPowers 135).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 135)) := by
  simp only [show gridGroupSource 135=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 135=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_136 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 136))*u^(groupPowers 136).1*v^(groupPowers 136).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 136)) := by
  simp only [show gridGroupSource 136=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 136=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_137 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 137))*u^(groupPowers 137).1*v^(groupPowers 137).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 137)) := by
  simp only [show gridGroupSource 137=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 137=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_138 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 138))*u^(groupPowers 138).1*v^(groupPowers 138).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 138)) := by
  simp only [show gridGroupSource 138=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 138=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_139 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 139))*u^(groupPowers 139).1*v^(groupPowers 139).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 139)) := by
  simp only [show gridGroupSource 139=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 139=(-1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_140 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 140))*u^(groupPowers 140).1*v^(groupPowers 140).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 140)) := by
  simp only [show gridGroupSource 140=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 140=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_141 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 141))*u^(groupPowers 141).1*v^(groupPowers 141).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 141)) := by
  simp only [show gridGroupSource 141=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 141=(-3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_142 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 142))*u^(groupPowers 142).1*v^(groupPowers 142).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 142)) := by
  simp only [show gridGroupSource 142=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 142=(1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_143 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 143))*u^(groupPowers 143).1*v^(groupPowers 143).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 143)) := by
  simp only [show gridGroupSource 143=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 143=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_144 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 144))*u^(groupPowers 144).1*v^(groupPowers 144).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 144)) := by
  simp only [show gridGroupSource 144=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 144=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_145 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 145))*u^(groupPowers 145).1*v^(groupPowers 145).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 145)) := by
  simp only [show gridGroupSource 145=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 145=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_146 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 146))*u^(groupPowers 146).1*v^(groupPowers 146).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 146)) := by
  simp only [show gridGroupSource 146=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 146=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_147 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 147))*u^(groupPowers 147).1*v^(groupPowers 147).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 147)) := by
  simp only [show gridGroupSource 147=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 147=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_148 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 148))*u^(groupPowers 148).1*v^(groupPowers 148).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 148)) := by
  simp only [show gridGroupSource 148=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 148=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_149 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 149))*u^(groupPowers 149).1*v^(groupPowers 149).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 149)) := by
  simp only [show gridGroupSource 149=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 149=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_150 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 150))*u^(groupPowers 150).1*v^(groupPowers 150).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 150)) := by
  simp only [show gridGroupSource 150=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 150=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_151 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 151))*u^(groupPowers 151).1*v^(groupPowers 151).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 151)) := by
  simp only [show gridGroupSource 151=(5:Fin 32) from rfl,
    show sourceWord 5=[(0,false),(2,false)] from rfl,show groupPowers 151=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_152 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 152))*u^(groupPowers 152).1*v^(groupPowers 152).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 152)) := by
  simp only [show gridGroupSource 152=(6:Fin 32) from rfl,
    show sourceWord 6=[(0,false),(2,false),(0,false)] from rfl,show groupPowers 152=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_153 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 153))*u^(groupPowers 153).1*v^(groupPowers 153).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 153)) := by
  simp only [show gridGroupSource 153=(6:Fin 32) from rfl,
    show sourceWord 6=[(0,false),(2,false),(0,false)] from rfl,show groupPowers 153=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_154 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 154))*u^(groupPowers 154).1*v^(groupPowers 154).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 154)) := by
  simp only [show gridGroupSource 154=(6:Fin 32) from rfl,
    show sourceWord 6=[(0,false),(2,false),(0,false)] from rfl,show groupPowers 154=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_155 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 155))*u^(groupPowers 155).1*v^(groupPowers 155).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 155)) := by
  simp only [show gridGroupSource 155=(3:Fin 32) from rfl,
    show sourceWord 3=[(0,false),(1,true),(0,true)] from rfl,show groupPowers 155=(2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_156 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 156))*u^(groupPowers 156).1*v^(groupPowers 156).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 156)) := by
  simp only [show gridGroupSource 156=(3:Fin 32) from rfl,
    show sourceWord 3=[(0,false),(1,true),(0,true)] from rfl,show groupPowers 156=(2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_157 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 157))*u^(groupPowers 157).1*v^(groupPowers 157).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 157)) := by
  simp only [show gridGroupSource 157=(14:Fin 32) from rfl,
    show sourceWord 14=[(1,true),(0,false),(1,true)] from rfl,show groupPowers 157=(0, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_158 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 158))*u^(groupPowers 158).1*v^(groupPowers 158).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 158)) := by
  simp only [show gridGroupSource 158=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 158=(-3, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_159 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 159))*u^(groupPowers 159).1*v^(groupPowers 159).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 159)) := by
  simp only [show gridGroupSource 159=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 159=(3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_160 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 160))*u^(groupPowers 160).1*v^(groupPowers 160).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 160)) := by
  simp only [show gridGroupSource 160=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 160=(-1, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_161 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 161))*u^(groupPowers 161).1*v^(groupPowers 161).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 161)) := by
  simp only [show gridGroupSource 161=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 161=(1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_162 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 162))*u^(groupPowers 162).1*v^(groupPowers 162).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 162)) := by
  simp only [show gridGroupSource 162=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 162=(-3, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_163 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 163))*u^(groupPowers 163).1*v^(groupPowers 163).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 163)) := by
  simp only [show gridGroupSource 163=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 163=(-1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_164 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 164))*u^(groupPowers 164).1*v^(groupPowers 164).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 164)) := by
  simp only [show gridGroupSource 164=(8:Fin 32) from rfl,
    show sourceWord 8=[(0,true),(1,false),(3,false)] from rfl,show groupPowers 164=(-3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_165 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 165))*u^(groupPowers 165).1*v^(groupPowers 165).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 165)) := by
  simp only [show gridGroupSource 165=(26:Fin 32) from rfl,
    show sourceWord 26=[(3,false),(0,false),(1,false)] from rfl,show groupPowers 165=(1, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_166 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 166))*u^(groupPowers 166).1*v^(groupPowers 166).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 166)) := by
  simp only [show gridGroupSource 166=(26:Fin 32) from rfl,
    show sourceWord 26=[(3,false),(0,false),(1,false)] from rfl,show groupPowers 166=(3, 0, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_167 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 167))*u^(groupPowers 167).1*v^(groupPowers 167).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 167)) := by
  simp only [show gridGroupSource 167=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 167=(-3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_168 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 168))*u^(groupPowers 168).1*v^(groupPowers 168).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 168)) := by
  simp only [show gridGroupSource 168=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 168=(-1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_169 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 169))*u^(groupPowers 169).1*v^(groupPowers 169).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 169)) := by
  simp only [show gridGroupSource 169=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 169=(-3, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_170 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 170))*u^(groupPowers 170).1*v^(groupPowers 170).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 170)) := by
  simp only [show gridGroupSource 170=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 170=(1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_171 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 171))*u^(groupPowers 171).1*v^(groupPowers 171).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 171)) := by
  simp only [show gridGroupSource 171=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 171=(-3, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_172 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 172))*u^(groupPowers 172).1*v^(groupPowers 172).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 172)) := by
  simp only [show gridGroupSource 172=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 172=(3, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_173 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 173))*u^(groupPowers 173).1*v^(groupPowers 173).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 173)) := by
  simp only [show gridGroupSource 173=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 173=(-3, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_174 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 174))*u^(groupPowers 174).1*v^(groupPowers 174).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 174)) := by
  simp only [show gridGroupSource 174=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 174=(3, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_175 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 175))*u^(groupPowers 175).1*v^(groupPowers 175).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 175)) := by
  simp only [show gridGroupSource 175=(29:Fin 32) from rfl,
    show sourceWord 29=[(3,false),(1,false)] from rfl,show groupPowers 175=(-3, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_176 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 176))*u^(groupPowers 176).1*v^(groupPowers 176).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 176)) := by
  simp only [show gridGroupSource 176=(28:Fin 32) from rfl,
    show sourceWord 28=[(3,false),(0,true),(1,false)] from rfl,show groupPowers 176=(3, 2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_177 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 177))*u^(groupPowers 177).1*v^(groupPowers 177).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 177)) := by
  simp only [show gridGroupSource 177=(30:Fin 32) from rfl,
    show sourceWord 30=[(3,false),(1,false),(0,false)] from rfl,show groupPowers 177=(1, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_178 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 178))*u^(groupPowers 178).1*v^(groupPowers 178).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 178)) := by
  simp only [show gridGroupSource 178=(22:Fin 32) from rfl,
    show sourceWord 22=[(2,true),(1,false),(2,false)] from rfl,show groupPowers 178=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_179 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 179))*u^(groupPowers 179).1*v^(groupPowers 179).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 179)) := by
  simp only [show gridGroupSource 179=(22:Fin 32) from rfl,
    show sourceWord 22=[(2,true),(1,false),(2,false)] from rfl,show groupPowers 179=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_180 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 180))*u^(groupPowers 180).1*v^(groupPowers 180).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 180)) := by
  simp only [show gridGroupSource 180=(0:Fin 32) from rfl,
    show sourceWord 0=[(0,false),(1,false),(0,false)] from rfl,show groupPowers 180=(2, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_181 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 181))*u^(groupPowers 181).1*v^(groupPowers 181).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 181)) := by
  simp only [show gridGroupSource 181=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 181=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_182 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 182))*u^(groupPowers 182).1*v^(groupPowers 182).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 182)) := by
  simp only [show gridGroupSource 182=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 182=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_183 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 183))*u^(groupPowers 183).1*v^(groupPowers 183).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 183)) := by
  simp only [show gridGroupSource 183=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 183=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_184 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 184))*u^(groupPowers 184).1*v^(groupPowers 184).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 184)) := by
  simp only [show gridGroupSource 184=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 184=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_185 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 185))*u^(groupPowers 185).1*v^(groupPowers 185).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 185)) := by
  simp only [show gridGroupSource 185=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 185=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_186 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 186))*u^(groupPowers 186).1*v^(groupPowers 186).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 186)) := by
  simp only [show gridGroupSource 186=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 186=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_187 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 187))*u^(groupPowers 187).1*v^(groupPowers 187).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 187)) := by
  simp only [show gridGroupSource 187=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 187=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_188 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 188))*u^(groupPowers 188).1*v^(groupPowers 188).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 188)) := by
  simp only [show gridGroupSource 188=(2:Fin 32) from rfl,
    show sourceWord 2=[(0,false),(1,false),(2,false)] from rfl,show groupPowers 188=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_189 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 189))*u^(groupPowers 189).1*v^(groupPowers 189).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 189)) := by
  simp only [show gridGroupSource 189=(12:Fin 32) from rfl,
    show sourceWord 12=[(1,false),(2,false),(1,true)] from rfl,show groupPowers 189=(1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_190 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 190))*u^(groupPowers 190).1*v^(groupPowers 190).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 190)) := by
  simp only [show gridGroupSource 190=(12:Fin 32) from rfl,
    show sourceWord 12=[(1,false),(2,false),(1,true)] from rfl,show groupPowers 190=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_191 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 191))*u^(groupPowers 191).1*v^(groupPowers 191).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 191)) := by
  simp only [show gridGroupSource 191=(12:Fin 32) from rfl,
    show sourceWord 12=[(1,false),(2,false),(1,true)] from rfl,show groupPowers 191=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_192 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 192))*u^(groupPowers 192).1*v^(groupPowers 192).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 192)) := by
  simp only [show gridGroupSource 192=(12:Fin 32) from rfl,
    show sourceWord 12=[(1,false),(2,false),(1,true)] from rfl,show groupPowers 192=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_193 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 193))*u^(groupPowers 193).1*v^(groupPowers 193).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 193)) := by
  simp only [show gridGroupSource 193=(12:Fin 32) from rfl,
    show sourceWord 12=[(1,false),(2,false),(1,true)] from rfl,show groupPowers 193=(-3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_194 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 194))*u^(groupPowers 194).1*v^(groupPowers 194).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 194)) := by
  simp only [show gridGroupSource 194=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 194=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_195 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 195))*u^(groupPowers 195).1*v^(groupPowers 195).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 195)) := by
  simp only [show gridGroupSource 195=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 195=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_196 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 196))*u^(groupPowers 196).1*v^(groupPowers 196).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 196)) := by
  simp only [show gridGroupSource 196=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 196=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_197 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 197))*u^(groupPowers 197).1*v^(groupPowers 197).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 197)) := by
  simp only [show gridGroupSource 197=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 197=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_198 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 198))*u^(groupPowers 198).1*v^(groupPowers 198).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 198)) := by
  simp only [show gridGroupSource 198=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 198=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_199 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 199))*u^(groupPowers 199).1*v^(groupPowers 199).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 199)) := by
  simp only [show gridGroupSource 199=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 199=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_200 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 200))*u^(groupPowers 200).1*v^(groupPowers 200).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 200)) := by
  simp only [show gridGroupSource 200=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 200=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_201 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 201))*u^(groupPowers 201).1*v^(groupPowers 201).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 201)) := by
  simp only [show gridGroupSource 201=(24:Fin 32) from rfl,
    show sourceWord 24=[(2,true),(1,true),(1,true)] from rfl,show groupPowers 201=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_202 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 202))*u^(groupPowers 202).1*v^(groupPowers 202).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 202)) := by
  simp only [show gridGroupSource 202=(7:Fin 32) from rfl,
    show sourceWord 7=[(0,true),(0,true),(1,true)] from rfl,show groupPowers 202=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_203 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 203))*u^(groupPowers 203).1*v^(groupPowers 203).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 203)) := by
  simp only [show gridGroupSource 203=(7:Fin 32) from rfl,
    show sourceWord 7=[(0,true),(0,true),(1,true)] from rfl,show groupPowers 203=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_204 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 204))*u^(groupPowers 204).1*v^(groupPowers 204).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 204)) := by
  simp only [show gridGroupSource 204=(7:Fin 32) from rfl,
    show sourceWord 7=[(0,true),(0,true),(1,true)] from rfl,show groupPowers 204=(-2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_205 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 205))*u^(groupPowers 205).1*v^(groupPowers 205).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 205)) := by
  simp only [show gridGroupSource 205=(1:Fin 32) from rfl,
    show sourceWord 1=[(0,false),(1,false),(1,false)] from rfl,show groupPowers 205=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_206 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 206))*u^(groupPowers 206).1*v^(groupPowers 206).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 206)) := by
  simp only [show gridGroupSource 206=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 206=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_207 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 207))*u^(groupPowers 207).1*v^(groupPowers 207).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 207)) := by
  simp only [show gridGroupSource 207=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 207=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_208 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 208))*u^(groupPowers 208).1*v^(groupPowers 208).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 208)) := by
  simp only [show gridGroupSource 208=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 208=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_209 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 209))*u^(groupPowers 209).1*v^(groupPowers 209).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 209)) := by
  simp only [show gridGroupSource 209=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 209=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_210 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 210))*u^(groupPowers 210).1*v^(groupPowers 210).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 210)) := by
  simp only [show gridGroupSource 210=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 210=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_211 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 211))*u^(groupPowers 211).1*v^(groupPowers 211).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 211)) := by
  simp only [show gridGroupSource 211=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 211=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_212 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 212))*u^(groupPowers 212).1*v^(groupPowers 212).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 212)) := by
  simp only [show gridGroupSource 212=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 212=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_213 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 213))*u^(groupPowers 213).1*v^(groupPowers 213).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 213)) := by
  simp only [show gridGroupSource 213=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 213=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_214 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 214))*u^(groupPowers 214).1*v^(groupPowers 214).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 214)) := by
  simp only [show gridGroupSource 214=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 214=(3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_215 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 215))*u^(groupPowers 215).1*v^(groupPowers 215).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 215)) := by
  simp only [show gridGroupSource 215=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 215=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_216 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 216))*u^(groupPowers 216).1*v^(groupPowers 216).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 216)) := by
  simp only [show gridGroupSource 216=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 216=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_217 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 217))*u^(groupPowers 217).1*v^(groupPowers 217).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 217)) := by
  simp only [show gridGroupSource 217=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 217=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_218 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 218))*u^(groupPowers 218).1*v^(groupPowers 218).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 218)) := by
  simp only [show gridGroupSource 218=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 218=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_219 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 219))*u^(groupPowers 219).1*v^(groupPowers 219).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 219)) := by
  simp only [show gridGroupSource 219=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 219=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_220 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 220))*u^(groupPowers 220).1*v^(groupPowers 220).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 220)) := by
  simp only [show gridGroupSource 220=(4:Fin 32) from rfl,
    show sourceWord 4=[(0,false),(1,true),(2,false)] from rfl,show groupPowers 220=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_221 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 221))*u^(groupPowers 221).1*v^(groupPowers 221).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 221)) := by
  simp only [show gridGroupSource 221=(19:Fin 32) from rfl,
    show sourceWord 19=[(2,true),(0,false),(2,false)] from rfl,show groupPowers 221=(-2, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_222 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 222))*u^(groupPowers 222).1*v^(groupPowers 222).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 222)) := by
  simp only [show gridGroupSource 222=(19:Fin 32) from rfl,
    show sourceWord 19=[(2,true),(0,false),(2,false)] from rfl,show groupPowers 222=(2, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_223 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 223))*u^(groupPowers 223).1*v^(groupPowers 223).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 223)) := by
  simp only [show gridGroupSource 223=(19:Fin 32) from rfl,
    show sourceWord 19=[(2,true),(0,false),(2,false)] from rfl,show groupPowers 223=(-2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_224 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 224))*u^(groupPowers 224).1*v^(groupPowers 224).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 224)) := by
  simp only [show gridGroupSource 224=(19:Fin 32) from rfl,
    show sourceWord 19=[(2,true),(0,false),(2,false)] from rfl,show groupPowers 224=(2, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_225 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 225))*u^(groupPowers 225).1*v^(groupPowers 225).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 225)) := by
  simp only [show gridGroupSource 225=(31:Fin 32) from rfl,
    show sourceWord 31=[(3,false),(2,false),(1,true)] from rfl,show groupPowers 225=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_226 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 226))*u^(groupPowers 226).1*v^(groupPowers 226).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 226)) := by
  simp only [show gridGroupSource 226=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 226=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_227 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 227))*u^(groupPowers 227).1*v^(groupPowers 227).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 227)) := by
  simp only [show gridGroupSource 227=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 227=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_228 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 228))*u^(groupPowers 228).1*v^(groupPowers 228).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 228)) := by
  simp only [show gridGroupSource 228=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 228=(0, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_229 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 229))*u^(groupPowers 229).1*v^(groupPowers 229).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 229)) := by
  simp only [show gridGroupSource 229=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 229=(0, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_230 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 230))*u^(groupPowers 230).1*v^(groupPowers 230).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 230)) := by
  simp only [show gridGroupSource 230=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 230=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_231 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 231))*u^(groupPowers 231).1*v^(groupPowers 231).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 231)) := by
  simp only [show gridGroupSource 231=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 231=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_232 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 232))*u^(groupPowers 232).1*v^(groupPowers 232).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 232)) := by
  simp only [show gridGroupSource 232=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 232=(0, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_233 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 233))*u^(groupPowers 233).1*v^(groupPowers 233).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 233)) := by
  simp only [show gridGroupSource 233=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 233=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_234 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 234))*u^(groupPowers 234).1*v^(groupPowers 234).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 234)) := by
  simp only [show gridGroupSource 234=(9:Fin 32) from rfl,
    show sourceWord 9=[(0,true),(2,false),(2,false)] from rfl,show groupPowers 234=(0, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSourcesTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixGermSources. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixGermOriginalRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive SmallLevelTaylor

/-- Every selected source equation is derived from the original solution,
with the same coherent sign and an analytic Taylor remainder of every order. -/
theorem original_source_row (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    (i : GridSource) :
    ∃ (B : ℝ) (error : ℕ→ℂ→ℂ),∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ,B<s.re →
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=error M s+
          ∑ n∈Finset.range M,gridShiftRows m f ε n s
            (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  cases i with
  | word i =>
    obtain ⟨B,error,hB⟩:=grid_matrix_rows_of_fricke m hf (grid_physical_sign m hε)
      (grid_fricke_of_laws m hε hlaw) i
    refine ⟨B,error,fun M => ⟨(hB M).1,?_⟩⟩
    intro s hs
    simpa only [gridLeadingRows,gridGroupLeading,gridShiftRows,gridVector] using (hB M).2 s hs
  | taylor i =>
    obtain ⟨B,hB⟩:=grid_ramanujan_rows_of_laws m hf hlaw i
    refine ⟨B,gridTaylorError m f ε i,fun M => ⟨(hB M).1,?_⟩⟩
    intro s hs
    simpa only [gridLeadingRows,gridRamanujanLeading,gridShiftRows,gridSample_grid] using (hB M).2 s hs
  | entire i =>
    obtain ⟨ha,B,hB⟩:=grid_ramanujan_entire m hm hf i
    refine ⟨B,fun _ => ramanujanEntire 26 (2*m) f (gridEntireQ i),?_⟩
    intro M
    refine ⟨fun s _ => ha s,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,gridSample_grid]
      using (hB s hs).symm
  | hecke i =>
    obtain ⟨B,hB⟩:=original_grid_hecke_row m hm hf i
    refine ⟨B,fun _ _ => 0,?_⟩
    intro M
    refine ⟨fun _ _ => analyticAt_const,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,gridHeckeLeading_grid]
      using hB s hs
  | infinity i =>
    have ha:=grid_infinity_entire_of_fricke m hm hf (grid_physical_sign m hε)
      (grid_fricke_of_laws m hε hlaw) i
    obtain ⟨B,hB⟩:=sourceEntire_initial m hf
    refine ⟨B,fun _ => sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/780),?_⟩
    intro M
    refine ⟨fun s _ => ha.analyticAt s,?_⟩
    intro s hs
    simpa only [gridLeadingRows,gridShiftRows,Finset.sum_const_zero,add_zero,
      gridVector,grid,Int.cast_natCast,Nat.cast_ofNat] using
        (hB (((gridInfinityIndex i:ℕ):ℝ)/780) s hs).symm

/-- One common half-plane for all397 original equations. -/
theorem original_source_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ (ε : ℂ) (B : ℝ) (error : GridSource→ℕ→ℂ→ℂ),
      (ε=1 ∨ ε= -1) ∧ GridFrickeLaws (2*m) f ε ∧
      ∀ i : GridSource,∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ,B<s.re →
          gridLeadingRows m f ε s (gridVector (2*m) f s) i=error i M s+
            ∑ n∈Finset.range M,gridShiftRows m f ε n s
              (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  choose b error hb using original_source_row m hm hf hε hlaw
  have : Nonempty GridSource := ⟨.word 0⟩
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : GridSource) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨ε,B,error,hε,hlaw,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms original_source_row
#print axioms original_source_system
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermShiftLinearV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Matrix SmallLevelFiniteGridSupport

/-- Every positive Taylor shift is a linear map on the additive grid. -/
def shiftLinearMap (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 780→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := gridShiftRows m f ε n s
  map_add' v w := by
    funext i
    cases i <;> simp [gridShiftRows,gridSample_add,mul_add]
  map_smul' c v := by
    funext i
    cases i <;> simp [gridShiftRows,gridSample_smul,mul_left_comm]

theorem shiftRows_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ)
    (v : Fin 780→ℂ) (i : GridSource) (z : ℂ) :
    AnalyticAt ℂ (fun s => gridShiftRows m f ε n s v i) z := by
  cases i with
  | word i => exact (gridMatrixScalar_analytic m f _ i (n+1) z).mul analyticAt_const
  | taylor i => exact (gridTaylorCoefficient_analytic m f ε i (n+1) z).mul analyticAt_const
  | entire i => exact analyticAt_const
  | hecke i => exact analyticAt_const
  | infinity i => exact analyticAt_const

def selectedShiftLinearMap {r : ℕ} (J : Fin r→GridSource)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 780→ℂ)→ₗ[ℂ](Fin r→ℂ) where
  toFun v i := gridShiftRows m f ε n s v (J i)
  map_add' v w := by
    funext i
    exact congrFun ((shiftLinearMap m f ε n s).map_add v w) (J i)
  map_smul' c v := by
    funext i
    exact congrFun ((shiftLinearMap m f ε n s).map_smul c v) (J i)

def restrictedShiftMatrix {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin r) (Fin d) ℂ :=
  ((selectedShiftLinearMap J m f ε n s).comp (extension u)).toMatrix'

theorem restrictedShiftMatrix_analytic {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (i : Fin r) (j : Fin d) (z : ℂ) :
    AnalyticAt ℂ (fun s => restrictedShiftMatrix J u m f ε n s i j) z := by
  simp only [restrictedShiftMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact shiftRows_analytic m f ε n (extension u (Pi.single j 1)) (J i) z

theorem restrictedShiftMatrix_mulVec {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin d→ℂ) (i : Fin r) :
    (restrictedShiftMatrix J u m f ε n s *ᵥ v) i=
      gridShiftRows m f ε n s (extension u v) (J i) := by
  rw [restrictedShiftMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

#print axioms shiftRows_analytic
#print axioms restrictedShiftMatrix_analytic
#print axioms restrictedShiftMatrix_mulVec
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLeadingLinearV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Matrix SmallLevelFiniteGridSupport SmallLevelPrimeRates

/-- The original leading equations form a linear map before any sign selection. -/
def leadingLinearMap (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) :
    (Fin 780→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := gridLeadingRows m f ε s
  map_add' v w := by
    funext i
    cases i <;>
      simp [gridLeadingRows,gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
        gridSample_add,mul_add,Finset.sum_add_distrib] <;> (try split) <;> (try simp only [←Finset.mul_sum]) <;> ring
  map_smul' c v := by
    funext i
    cases i <;>
      simp [gridLeadingRows,gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
        gridSample_smul,Finset.mul_sum,mul_left_comm] <;> (try split) <;> (try simp only [←Finset.mul_sum]) <;> ring

theorem leadingRows_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) (z : ℂ) :
    AnalyticAt ℂ (fun s => gridLeadingRows m f ε s v i) z := by
  cases i with
  | word i =>
    unfold gridLeadingRows gridGroupLeading
    apply AnalyticAt.sub
    · exact analyticAt_const
    · exact (gridMatrixScalar_analytic m f _ i 0 z).mul analyticAt_const
  | taylor i =>
    unfold gridLeadingRows gridRamanujanLeading
    apply AnalyticAt.sub
    · exact analyticAt_const
    · exact (gridTaylorCoefficient_analytic m f ε i 0 z).mul analyticAt_const
  | entire i => exact analyticAt_const
  | infinity i => exact analyticAt_const
  | hecke i =>
    have hp : gridHeckeP i≠0 := (gridHeckeSpecs_valid i).1.ne_zero
    have hi := (parameter_analytic (gridHeckeP i) m hp z).inv
      (parameter_ne_zero (gridHeckeP i) m hp z)
    unfold gridLeadingRows gridHeckeLeading
    apply AnalyticAt.add
    · exact analyticAt_const.sub ((analyticAt_const.mul hi).mul analyticAt_const)
    · split
      · exact analyticAt_const
      · exact (hi.pow 2).mul analyticAt_const

def selectedLeadingLinearMap {r : ℕ} (J : Fin r→GridSource)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin r→ℂ) where
  toFun v i := gridLeadingRows m f ε s v (J i)
  map_add' v w := by
    funext i
    exact congrFun ((leadingLinearMap m f ε s).map_add v w) (J i)
  map_smul' c v := by
    funext i
    exact congrFun ((leadingLinearMap m f ε s).map_smul c v) (J i)

def restrictedLeadingMatrix {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin r) (Fin d) ℂ :=
  ((selectedLeadingLinearMap J m f ε s).comp (extension u)).toMatrix'

theorem restrictedLeadingMatrix_analytic {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin r) (j : Fin d) (z : ℂ) :
    AnalyticAt ℂ (fun s => restrictedLeadingMatrix J u m f ε s i j) z := by
  simp only [restrictedLeadingMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact leadingRows_analytic m f ε (extension u (Pi.single j 1)) (J i) z

theorem restrictedLeadingMatrix_mulVec {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin d→ℂ) (i : Fin r) :
    (restrictedLeadingMatrix J u m f ε s *ᵥ v) i=
      gridLeadingRows m f ε s (extension u v) (J i) := by
  rw [restrictedLeadingMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

#print axioms restrictedLeadingMatrix_analytic
#print axioms restrictedLeadingMatrix_mulVec
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLeadingSupportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorSource_restrict (v : Fin 780→ℂ) (i : Fin 53) :
    gridSample (gridTaylorQ i) (gridTaylorT i) (extension support (fun j => v (support j)))=gridSample (gridTaylorQ i) (gridTaylorT i) v := by
  fin_cases i
  · exact taylorSource_restrict_0 v
  · exact taylorSource_restrict_1 v
  · exact taylorSource_restrict_2 v
  · exact taylorSource_restrict_3 v
  · exact taylorSource_restrict_4 v
  · exact taylorSource_restrict_5 v
  · exact taylorSource_restrict_6 v
  · exact taylorSource_restrict_7 v
  · exact taylorSource_restrict_8 v
  · exact taylorSource_restrict_9 v
  · exact taylorSource_restrict_10 v
  · exact taylorSource_restrict_11 v
  · exact taylorSource_restrict_12 v
  · exact taylorSource_restrict_13 v
  · exact taylorSource_restrict_14 v
  · exact taylorSource_restrict_15 v
  · exact taylorSource_restrict_16 v
  · exact taylorSource_restrict_17 v
  · exact taylorSource_restrict_18 v
  · exact taylorSource_restrict_19 v
  · exact taylorSource_restrict_20 v
  · exact taylorSource_restrict_21 v
  · exact taylorSource_restrict_22 v
  · exact taylorSource_restrict_23 v
  · exact taylorSource_restrict_24 v
  · exact taylorSource_restrict_25 v
  · exact taylorSource_restrict_26 v
  · exact taylorSource_restrict_27 v
  · exact taylorSource_restrict_28 v
  · exact taylorSource_restrict_29 v
  · exact taylorSource_restrict_30 v
  · exact taylorSource_restrict_31 v
  · exact taylorSource_restrict_32 v
  · exact taylorSource_restrict_33 v
  · exact taylorSource_restrict_34 v
  · exact taylorSource_restrict_35 v
  · exact taylorSource_restrict_36 v
  · exact taylorSource_restrict_37 v
  · exact taylorSource_restrict_38 v
  · exact taylorSource_restrict_39 v
  · exact taylorSource_restrict_40 v
  · exact taylorSource_restrict_41 v
  · exact taylorSource_restrict_42 v
  · exact taylorSource_restrict_43 v
  · exact taylorSource_restrict_44 v
  · exact taylorSource_restrict_45 v
  · exact taylorSource_restrict_46 v
  · exact taylorSource_restrict_47 v
  · exact taylorSource_restrict_48 v
  · exact taylorSource_restrict_49 v
  · exact taylorSource_restrict_50 v
  · exact taylorSource_restrict_51 v
  · exact taylorSource_restrict_52 v

theorem entireSource_restrict (v : Fin 780→ℂ) (i : Fin 11) :
    gridSample (gridEntireQ i) 0 (extension support (fun j => v (support j)))=gridSample (gridEntireQ i) 0 v := by
  fin_cases i
  · exact entireSource_restrict_0 v
  · exact entireSource_restrict_1 v
  · exact entireSource_restrict_2 v
  · exact entireSource_restrict_3 v
  · exact entireSource_restrict_4 v
  · exact entireSource_restrict_5 v
  · exact entireSource_restrict_6 v
  · exact entireSource_restrict_7 v
  · exact entireSource_restrict_8 v
  · exact entireSource_restrict_9 v
  · exact entireSource_restrict_10 v

theorem heckeSource_restrict (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) (i : Fin 96) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) i=gridHeckeLeading m f s v i := by
  fin_cases i
  · exact heckeSource_restrict_0 m f s v
  · exact heckeSource_restrict_1 m f s v
  · exact heckeSource_restrict_2 m f s v
  · exact heckeSource_restrict_3 m f s v
  · exact heckeSource_restrict_4 m f s v
  · exact heckeSource_restrict_5 m f s v
  · exact heckeSource_restrict_6 m f s v
  · exact heckeSource_restrict_7 m f s v
  · exact heckeSource_restrict_8 m f s v
  · exact heckeSource_restrict_9 m f s v
  · exact heckeSource_restrict_10 m f s v
  · exact heckeSource_restrict_11 m f s v
  · exact heckeSource_restrict_12 m f s v
  · exact heckeSource_restrict_13 m f s v
  · exact heckeSource_restrict_14 m f s v
  · exact heckeSource_restrict_15 m f s v
  · exact heckeSource_restrict_16 m f s v
  · exact heckeSource_restrict_17 m f s v
  · exact heckeSource_restrict_18 m f s v
  · exact heckeSource_restrict_19 m f s v
  · exact heckeSource_restrict_20 m f s v
  · exact heckeSource_restrict_21 m f s v
  · exact heckeSource_restrict_22 m f s v
  · exact heckeSource_restrict_23 m f s v
  · exact heckeSource_restrict_24 m f s v
  · exact heckeSource_restrict_25 m f s v
  · exact heckeSource_restrict_26 m f s v
  · exact heckeSource_restrict_27 m f s v
  · exact heckeSource_restrict_28 m f s v
  · exact heckeSource_restrict_29 m f s v
  · exact heckeSource_restrict_30 m f s v
  · exact heckeSource_restrict_31 m f s v
  · exact heckeSource_restrict_32 m f s v
  · exact heckeSource_restrict_33 m f s v
  · exact heckeSource_restrict_34 m f s v
  · exact heckeSource_restrict_35 m f s v
  · exact heckeSource_restrict_36 m f s v
  · exact heckeSource_restrict_37 m f s v
  · exact heckeSource_restrict_38 m f s v
  · exact heckeSource_restrict_39 m f s v
  · exact heckeSource_restrict_40 m f s v
  · exact heckeSource_restrict_41 m f s v
  · exact heckeSource_restrict_42 m f s v
  · exact heckeSource_restrict_43 m f s v
  · exact heckeSource_restrict_44 m f s v
  · exact heckeSource_restrict_45 m f s v
  · exact heckeSource_restrict_46 m f s v
  · exact heckeSource_restrict_47 m f s v
  · exact heckeSource_restrict_48 m f s v
  · exact heckeSource_restrict_49 m f s v
  · exact heckeSource_restrict_50 m f s v
  · exact heckeSource_restrict_51 m f s v
  · exact heckeSource_restrict_52 m f s v
  · exact heckeSource_restrict_53 m f s v
  · exact heckeSource_restrict_54 m f s v
  · exact heckeSource_restrict_55 m f s v
  · exact heckeSource_restrict_56 m f s v
  · exact heckeSource_restrict_57 m f s v
  · exact heckeSource_restrict_58 m f s v
  · exact heckeSource_restrict_59 m f s v
  · exact heckeSource_restrict_60 m f s v
  · exact heckeSource_restrict_61 m f s v
  · exact heckeSource_restrict_62 m f s v
  · exact heckeSource_restrict_63 m f s v
  · exact heckeSource_restrict_64 m f s v
  · exact heckeSource_restrict_65 m f s v
  · exact heckeSource_restrict_66 m f s v
  · exact heckeSource_restrict_67 m f s v
  · exact heckeSource_restrict_68 m f s v
  · exact heckeSource_restrict_69 m f s v
  · exact heckeSource_restrict_70 m f s v
  · exact heckeSource_restrict_71 m f s v
  · exact heckeSource_restrict_72 m f s v
  · exact heckeSource_restrict_73 m f s v
  · exact heckeSource_restrict_74 m f s v
  · exact heckeSource_restrict_75 m f s v
  · exact heckeSource_restrict_76 m f s v
  · exact heckeSource_restrict_77 m f s v
  · exact heckeSource_restrict_78 m f s v
  · exact heckeSource_restrict_79 m f s v
  · exact heckeSource_restrict_80 m f s v
  · exact heckeSource_restrict_81 m f s v
  · exact heckeSource_restrict_82 m f s v
  · exact heckeSource_restrict_83 m f s v
  · exact heckeSource_restrict_84 m f s v
  · exact heckeSource_restrict_85 m f s v
  · exact heckeSource_restrict_86 m f s v
  · exact heckeSource_restrict_87 m f s v
  · exact heckeSource_restrict_88 m f s v
  · exact heckeSource_restrict_89 m f s v
  · exact heckeSource_restrict_90 m f s v
  · exact heckeSource_restrict_91 m f s v
  · exact heckeSource_restrict_92 m f s v
  · exact heckeSource_restrict_93 m f s v
  · exact heckeSource_restrict_94 m f s v
  · exact heckeSource_restrict_95 m f s v

theorem leadingRows_restrict (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    gridLeadingRows m f ε s (extension support (fun j => v (support j))) i=
      gridLeadingRows m f ε s v i := by
  cases i with
  | word i => simp only [gridLeadingRows,gridGroupLeading,groupIndex_restrict,groupTarget_restrict]
  | taylor i => simp only [gridLeadingRows,gridRamanujanLeading,taylorSource_restrict,taylorTarget_restrict]
  | entire i => exact entireSource_restrict v i
  | hecke i => exact heckeSource_restrict m f s v i
  | infinity i => fin_cases i; exact infinity_restrict_0 v; exact infinity_restrict_1 v

#print axioms leadingRows_restrict

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermFullMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Matrix SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM

/-- All397 original rows, on the common320-coordinate support. -/
def fullLeadingMatrix (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix GridSource (Fin 320) ℂ :=
  ((leadingLinearMap m f ε s).comp (extension support)).toMatrix'

def fullShiftMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    Matrix GridSource (Fin 320) ℂ :=
  ((shiftLinearMap m f ε n s).comp (extension support)).toMatrix'

theorem fullLeadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (i : GridSource) (j : Fin 320) (z : ℂ) :
    AnalyticAt ℂ (fun s => fullLeadingMatrix m f ε s i j) z := by
  simp only [fullLeadingMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact leadingRows_analytic m f ε (extension support (Pi.single j 1)) i z

theorem fullShiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ)
    (i : GridSource) (j : Fin 320) (z : ℂ) :
    AnalyticAt ℂ (fun s => fullShiftMatrix m f ε n s i j) z := by
  simp only [fullShiftMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact shiftRows_analytic m f ε n (extension support (Pi.single j 1)) i z

theorem fullLeadingMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) :
    fullLeadingMatrix m f ε s *ᵥ (fun j => v (support j))=gridLeadingRows m f ε s v := by
  rw [fullLeadingMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  funext i
  exact leadingRows_restrict m f ε s v i

theorem fullShiftMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 780→ℂ) :
    fullShiftMatrix m f ε n s *ᵥ (fun j => v (support j))=gridShiftRows m f ε n s v := by
  rw [fullShiftMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  funext i
  exact shiftRows_restrict m f ε n s v i

#print axioms fullLeadingMatrix_mulVec
#print axioms fullShiftMatrix_mulVec
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermInitialSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive

/-- The original source system with a prescribed coherent sign and a common
half-plane that also provides analyticity of every original additive transform. -/
theorem initial_system_of_laws (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (error : GridSource→ℕ→ℂ→ℂ),
      (∀ i : Fin 780,∀ z : ℂ,B<z.re → AnalyticAt ℂ (fun s => gridVector (2*m) f s i) z) ∧
      (∀ M : ℕ,∀ i : GridSource,∀ z : ℂ,B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (error i M) z) ∧
      ∀ M : ℕ,∀ s : ℂ,B<s.re → ∀ i : GridSource,
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=error i M s+
          ∑ n∈Finset.range M,gridShiftRows m f ε n s
            (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  choose b error hb using original_source_row m hm hf hε hlaw
  have : Nonempty GridSource := ⟨.word 0⟩
  let BS : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbS (i : GridSource) : b i≤BS:=Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨BF,hF⟩:=original_common_halfplane hf
  let B : ℝ:=max BS BF
  have hBS : BS≤B:=le_max_left _ _
  have hBF : BF≤B:=le_max_right _ _
  refine ⟨B,error,?_,?_,?_⟩
  · intro i z hz
    exact (hF (((i:ℕ):ℝ)/780) z (lt_of_le_of_lt hBF hz)).1
  · intro M i z hz
    apply (hb i M).1 z
    change b i-((M:ℝ)+1)<z.re
    linarith [hbS i]
  · intro M s hs i
    exact (hb i M).2 s (lt_of_le_of_lt ((hbS i).trans hBS) hs)

#print axioms initial_system_of_laws
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

theorem groupRate_factor : ∀ i : Fin 235,
    gridGroupRate i=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*
      (13:ℚ)^(groupPowers i).2.2.1*(5:ℚ)^(groupPowers i).2.2.2 := by
  decide +kernel

theorem taylorRate_factor : ∀ i : Fin 53,
    taylorRate i=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*
      (13:ℚ)^(taylorPowers i).2.2.1*(5:ℚ)^(taylorPowers i).2.2.2 := by
  decide +kernel

theorem groupRate_complex (i : Fin 235) (h : ℂ) :
    (gridGroupRate i:ℂ)^h=monomial (groupPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((13:ℂ)^h) ((5:ℂ)^h) :=
  rational_power 2 3 13 5 (by decide) (by decide) (by decide) (by decide) _ _ (groupRate_factor i) h

theorem taylorRate_complex (i : Fin 53) (h : ℂ) :
    (taylorRate i:ℂ)^h=monomial (taylorPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((13:ℂ)^h) ((5:ℂ)^h) :=
  rational_power 2 3 13 5 (by decide) (by decide) (by decide) (by decide) _ _ (taylorRate_factor i) h

theorem matrixScalar_leading (m : ℕ) (f : ℕ→ℂ) (η s : ℂ) (i : Fin 235) :
    gridMatrixScalar m f η i 0 s=
      gridWordSign (-badParameter f 2) η (sourceWord (gridGroupSource i))*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s) := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one,root_two]
  rw [groupRate_complex]
  rfl

theorem taylorScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 53) :
    gridTaylorCoefficient m f ε i 0 s=
      (FinitenessNormalizedTwistProduct.root 26 f (gridTaylorQ i))*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s) := by
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  have hb : (((gridTaylorL i:ℝ)*((gridTaylorT i:ℝ)/780)^2:ℝ):ℂ)=(taylorRate i:ℂ) := by
    simp [taylorRate]
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Ring.choose_zero_right,mul_one,hm]
  rw [hb,taylorRate_complex]
  unfold phase parameter
  ring

#print axioms groupRate_complex
#print axioms taylorRate_complex
#print axioms matrixScalar_leading
#print axioms taylorScalar_leading

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermParametersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

def rootSource : Fin 53→Fin 71 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,18,18,18,18,18,18,18,18,18,18,18,18,18,28,28,28,28,28,28,28,28,28,28,28,28,40,40,42,42,42,42,42,42,46,46,46,63,63]

theorem rootSource_q : ∀ i : Fin 53,
    SmallLevelTwentySixGrid.gridTaylorQ (rootSource i)=gridTaylorQ i := by decide +kernel

theorem grid_ramanujan_root (f : ℕ→ℂ) (i : Fin 53) :
    FinitenessNormalizedTwistProduct.root 26 f (gridTaylorQ i)=
      (if 2∣gridTaylorQ i then -badParameter f 2 else 1)*
      (if 13∣gridTaylorQ i then -badParameter f 13 else 1) := by
  simpa only [rootSource_q] using SmallLevelTwentySixGrid.grid_ramanujan_root f (rootSource i)

#print axioms grid_ramanujan_root

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLaurentRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates FinitenessNormalizedTwistProduct

/-- Four physical prime parameters; the last branch is used only at p=5. -/
def primeParameter (p : ℕ) (X Y Z W : ℂ) : ℂ :=
  if p=2 then X else if p=3 then Y else if p=13 then Z else W

def primeEigenvalue (p : ℕ) (σ₂ σ₁₃ a b : ℂ) : ℂ :=
  if p=2 then σ₂ else if p=3 then a else if p=13 then σ₁₃ else b

def laurentHecke (X Y Z W σ₂ σ₁₃ a b : ℂ) (v : Fin 780→ℂ) (i : Fin 96) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),v (gridIndex (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ))))-
    primeEigenvalue (gridHeckeP i) σ₂ σ₁₃ a b*(primeParameter (gridHeckeP i) X Y Z W)⁻¹*
      v (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i))+
    (if gridHeckeP i∣26 then 0 else ((primeParameter (gridHeckeP i) X Y Z W)⁻¹)^2*
      v (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i)))

def laurentRows (X Y Z W η σ₂ σ₁₃ a b : ℂ) (v : Fin 780→ℂ) : GridSource→ℂ
  | .word i => v (gridGroupIndex i)-gridWordSign (-σ₂) η (sourceWord (gridGroupSource i))*
      monomial (groupPowers i) X Y Z W*v (gridGroupTarget i)
  | .taylor i => gridSample (gridTaylorQ i) (gridTaylorT i) v-
      ((if 2∣gridTaylorQ i then -σ₂ else 1)*(if 13∣gridTaylorQ i then -σ₁₃ else 1))*η*
        monomial (taylorPowers i) X Y Z W*gridSample (gridTaylorQ i) (gridTaylorPartner i) v
  | .entire i => gridSample (gridEntireQ i) 0 v
  | .hecke i => laurentHecke X Y Z W σ₂ σ₁₃ a b v i
  | .infinity i => v (gridInfinityIndex i)

theorem primeParameter_actual (m : ℕ) (s : ℂ) (i : Fin 96) :
    primeParameter (gridHeckeP i) (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s)=parameter (gridHeckeP i) m s := by
  fin_cases i <;> rfl

theorem primeEigenvalue_actual (f : ℕ→ℂ) (i : Fin 96) :
    primeEigenvalue (gridHeckeP i) (badParameter f 2) (badParameter f 13)
      (badParameter f 3) (badParameter f 5)=(Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i) := by
  fin_cases i <;> rfl

/-- The formal Laurent source system is exactly the original leading system
on the physical exponential curve, for arbitrary original coefficients. -/
theorem leadingRows_laurent (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) (i : GridSource) :
    gridLeadingRows m f ε s v i=
      laurentRows (parameter 2 m s) (parameter 3 m s) (parameter 13 m s) (parameter 5 m s)
        (phase m ε) (badParameter f 2) (badParameter f 13) (badParameter f 3) (badParameter f 5) v i := by
  cases i with
  | word i =>
    simp only [gridLeadingRows,gridGroupLeading,laurentRows,matrixScalar_leading,phase]
  | taylor i =>
    simp only [gridLeadingRows,gridRamanujanLeading,laurentRows,taylorScalar_leading,grid_ramanujan_root]
  | entire i => rfl
  | infinity i => rfl
  | hecke i =>
    simp only [gridLeadingRows,laurentRows,laurentHecke,gridHeckeLeading,
      primeParameter_actual,primeEigenvalue_actual]

#print axioms leadingRows_laurent
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSlopeMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM

def taylorDerivative (i : Fin 53) : ℚ := (gridTaylorL i:ℚ)*(gridTaylorT i:ℚ)/780

theorem matrixScalar_factor (m : ℕ) (f : ℕ→ℂ) (η : ℂ) (i : Fin 235) (n : ℕ) (s : ℂ) :
    gridMatrixScalar m f η i n s = gridMatrixScalar m f η i 0 s *
      I^n*(gridGroupDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one,mul_pow]
  ring

theorem taylorScalar_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 53) (n : ℕ) (s : ℂ) :
    gridTaylorCoefficient m f ε i n s = gridTaylorCoefficient m f ε i 0 s *
      I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar taylorDerivative
  simp only [pow_zero,Ring.choose_zero_right,mul_one,Rat.cast_div,Rat.cast_mul,
    Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,Complex.ofReal_div,
    Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_ofNat,mul_pow,div_pow]
  ring

/-- The rational-slope part of a Taylor source, before its common binomial factor. -/
def slopeRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 780→ℂ) : GridSource→ℂ
  | .word i => gridMatrixScalar m f (ε*I^(2*m)) i 0 s *
      (gridGroupDerivative i:ℂ)^n*w (gridGroupTarget i)
  | .taylor i => gridTaylorCoefficient m f ε i 0 s *
      (taylorDerivative i:ℂ)^n*gridSample (gridTaylorQ i) (gridTaylorPartner i) w
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem shiftRows_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 780→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s w i =
      I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
        slopeRows m f ε (n+1) s w i := by
  cases i with
  | word i =>
    simp only [gridShiftRows,slopeRows]
    rw [matrixScalar_factor m f (ε*I^(2*m)) i (n+1) s]
    ring
  | taylor i =>
    simp only [gridShiftRows,slopeRows]
    rw [taylorScalar_factor m f ε i (n+1) s]
    ring
  | entire i => simp [gridShiftRows,slopeRows]
  | hecke i => simp [gridShiftRows,slopeRows]
  | infinity i => simp [gridShiftRows,slopeRows]

def fullSlopeMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    Matrix GridSource (Fin 320) ℂ :=
  fun i j => slopeRows m f ε n s (extension support (Pi.single j 1)) i

theorem fullShiftMatrix_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (i : GridSource) (j : Fin 320) :
    fullShiftMatrix m f ε n s i j =
      I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
        fullSlopeMatrix m f ε (n+1) s i j := by
  simp only [fullShiftMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,
    shiftLinearMap,fullSlopeMatrix]
  exact shiftRows_factor m f ε n s _ i

#print axioms shiftRows_factor
#print axioms fullShiftMatrix_factor
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermJetLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid Complex SmallLevelPrimeRates

theorem parameter_nat_sub (p m n : ℕ) (hp : p≠0) (s : ℂ) :
    parameter p m (s-(n:ℂ))=parameter p m s/(p:ℂ)^n := by
  unfold parameter
  rw [show s-(n:ℂ)-(m:ℂ)=(s-(m:ℂ))-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_natCast]

def laurentSlopeRows (n : ℕ) (X Y Z W η σ₂ σ₁₃ : ℂ)
    (v : Fin 780→ℂ) : GridSource→ℂ
  | .word i => gridWordSign (-σ₂) η (sourceWord (gridGroupSource i))*
      SmallLevelFourPrimeRates.monomial (groupPowers i) X Y Z W*
      (gridGroupDerivative i:ℂ)^n*v (gridGroupTarget i)
  | .taylor i => ((if 2∣gridTaylorQ i then -σ₂ else 1)*
      (if 13∣gridTaylorQ i then -σ₁₃ else 1))*η*
      SmallLevelFourPrimeRates.monomial (taylorPowers i) X Y Z W*
      (taylorDerivative i:ℂ)^n*gridSample (gridTaylorQ i) (gridTaylorPartner i) v
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem slopeRows_laurent (m n : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    slopeRows m f ε n s v i =
      laurentSlopeRows n (parameter 2 m s) (parameter 3 m s)
        (parameter 13 m s) (parameter 5 m s) (phase m ε)
        (badParameter f 2) (badParameter f 13) v i := by
  cases i <;> simp only [slopeRows,laurentSlopeRows,matrixScalar_leading,
    taylorScalar_leading,grid_ramanujan_root,phase]

/-- The normalized Taylor row, with lower layers kept as independent
coordinates. The factor 1/(n-h)! is the actual Taylor coefficient. -/
def laurentJetRow (n : ℕ) (X Y Z W η σ₂ σ₁₃ a b : ℂ)
    (v : ℕ→Fin 780→ℂ) (i : GridSource) : ℂ :=
  laurentRows (X/2^n) (Y/3^n) (Z/13^n) (W/5^n) η σ₂ σ₁₃ a b (v n) i-
    ∑ h∈Finset.range n,
      laurentSlopeRows (n-h) (X/2^n) (Y/3^n) (Z/13^n) (W/5^n)
        η σ₂ σ₁₃ (v h) i/((n-h).factorial:ℂ)

theorem laurentJetRow_physical (m n : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v : ℕ→Fin 780→ℂ) (i : GridSource) :
    laurentJetRow n (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) (phase m ε)
      (badParameter f 2) (badParameter f 13) (badParameter f 3) (badParameter f 5) v i =
    gridLeadingRows m f ε (s-(n:ℂ)) (v n) i-
      ∑ h∈Finset.range n,slopeRows m f ε (n-h) (s-(n:ℂ)) (v h) i/((n-h).factorial:ℂ) := by
  simp only [laurentJetRow,leadingRows_laurent,slopeRows_laurent,
    parameter_nat_sub 2 m n (by decide),parameter_nat_sub 3 m n (by decide),
    parameter_nat_sub 13 m n (by decide),parameter_nat_sub 5 m n (by decide),Nat.cast_ofNat]

#print axioms parameter_nat_sub
#print axioms slopeRows_laurent
#print axioms laurentJetRow_physical
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermPoleSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Matrix Filter SmallLevelTwentySixUnitMMM
open scoped Topology

/-- The original grid and all original Taylor equations on one half-plane.
This records meromorphic continuation only, with no pole-removability claim. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 320→ℂ
  E : ℕ→ℂ→GridSource→ℂ
  meromorphic : ∀ i x,MeromorphicNFAt (fun z => G z i) x
  agreement : ∀ z,B<z.re → G z=actualGrid m f z
  error : ∀ (n : ℕ) (i : GridSource) (z : ℂ),B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z
  rows : ∀ n z,B<z.re →
    fullLeadingMatrix m f ε z *ᵥ actualGrid m f z=E n z+
      ∑ j∈Finset.range n,fullShiftMatrix m f ε j z *ᵥ actualGrid m f (z+((j:ℂ)+1))

/-- No continuation or Taylor-row hypotheses are assumed: both follow
from the original solution at level26. -/
theorem original_pole_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ Nonempty (PoleSystem m f ε) := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨ε,hε,⟨{
    B := max B BG
    G := G
    E := fun n s i => E i n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n i z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    change fullLeadingMatrix m f ε s *ᵥ (fun j => gridVector (2*m) f s (support j))=
      (fun i => E i n s)+∑ j∈Finset.range n,
        fullShiftMatrix m f ε j s *ᵥ
          (fun i => gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
    rw [fullLeadingMatrix_mulVec]
    simp_rw [fullShiftMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow n s hb i

/-- Every original row persists as a punctured identity wherever its
analytic remainder is defined; this includes arbitrary Taylor orders. -/
theorem PoleSystem.continued_rows {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (n : ℕ) (i : GridSource) (x : ℂ)
    (hx : S.B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j)=ᶠ[𝓝[≠] x]
      (fun z => S.E n z i+∑ a∈Finset.range n,
        ∑ j,fullShiftMatrix m f ε a z i j*S.G (z+((a:ℂ)+1)) j) :=
  SmallLevelContinuation.rectangular_continued_rows S.B (actualGrid m f) S.G
    (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E
    (fun i z => (S.meromorphic i z).meromorphicAt) S.agreement
    (fun z i j => fullLeadingMatrix_analytic m f ε i j z)
    (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
    S.error S.rows n i x hx

#print axioms original_pole_system
#print axioms PoleSystem.continued_rows
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermLowerGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Filter Matrix SmallLevelFiniteShift QuantitativeArithmeticAnalyticGerm
open scoped Topology

/-- Every lower Taylor layer gives an identity modulo analytic germs at
the selected point. This retains arbitrary pole orders at all lower layers. -/
theorem PoleSystem.lower_taylor_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (d : ℕ) (i : GridSource) :
    HasAnalyticGerm (fun z => (∑ j,fullLeadingMatrix m f ε (z-d) i j*S.G (z-d) j)-
      ∑ a∈Finset.range d,∑ j,fullShiftMatrix m f ε a (z-d) i j*
        S.G (z-((d-1-a:ℕ):ℂ)) j) x := by
  obtain ⟨R,hR,he⟩:=continued_regular_shifted_source S.B S.G
    (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E x d S.error
    (fun a ha i j => regular_pole_tail (fullShiftMatrix m f ε)
      (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
      S.G S.meromorphic x d hshift a ha i j)
    (fun n i y hy => S.continued_rows n i y hy)
  exact ⟨fun z => R z i,hR i,he i⟩

#print axioms PoleSystem.lower_taylor_germs
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermNormalizedGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex Filter Matrix QuantitativeArithmeticAnalyticGerm
open scoped Topology

lemma choose_two_complex (z : ℂ) : Ring.choose z 2=z*(z-1)/2 := by
  norm_num [Ring.choose_eq_smul,descPochhammer_succ_right,Polynomial.smeval_mul,
    Polynomial.smeval_sub,Polynomial.smeval_X,Polynomial.smeval_C]
  ring

def firstLayer (m : ℕ) (G : ℂ→Fin 320→ℂ) (s : ℂ) (j : Fin 320) : ℂ :=
  G (s-1) j/(I*(s-((2*m:ℕ):ℂ)))

def secondLayer (m : ℕ) (G : ℂ→Fin 320→ℂ) (s : ℂ) (j : Fin 320) : ℂ :=
  G (s-2) j/(I^2*(s-((2*m:ℕ):ℂ))*(s-((2*m:ℕ):ℂ)-1))

theorem PoleSystem.top_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j) x := by
  simpa using S.lower_taylor_germs x hshift 0 i

/-- Normalization of the first complete Taylor layer, using an analytic
unit at the selected point. No pole-order comparison is used. -/
theorem PoleSystem.first_normalized_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,
      (fullLeadingMatrix m f ε (z-1) i j*firstLayer m S.G z j-
        fullSlopeMatrix m f ε 1 (z-1) i j*S.G z j)) x := by
  have hh := S.lower_taylor_germs x hshift 1 i
  simp only [Nat.cast_one,Finset.sum_range_one,Nat.sub_self,Nat.zero_sub,Nat.cast_zero,
    sub_zero] at hh
  have ha : AnalyticAt ℂ (fun z : ℂ => 1/(I*(z-((2*m:ℕ):ℂ)))) x :=
    analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hx))
  apply (hh.mul_analytic ha).congr
  have he : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ) :=
    (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with z hz
  simp only [mul_sub,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fullShiftMatrix_factor]
  simp only [Nat.zero_add,Nat.cast_one,pow_one,Ring.choose_one_right,sub_add_cancel,
    firstLayer]
  field_simp [I_ne_zero,sub_ne_zero.mpr hz]

/-- The second normalized layer retains both lower germs. Its second
Taylor coefficient is the rational slope squared divided by two. -/
theorem PoleSystem.second_normalized_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1) (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,
      (fullLeadingMatrix m f ε (z-2) i j*secondLayer m S.G z j-
        fullSlopeMatrix m f ε 1 (z-2) i j*firstLayer m S.G z j-
        fullSlopeMatrix m f ε 2 (z-2) i j*S.G z j/2)) x := by
  have hh := S.lower_taylor_germs x hshift 2 i
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceSub,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,sub_zero] at hh
  have hn : x-((2*m:ℕ):ℂ)-1≠0 := by intro h; apply hx1; linear_combination h
  have ha : AnalyticAt ℂ
      (fun z : ℂ => 1/(I^2*(z-((2*m:ℕ):ℂ))*(z-((2*m:ℕ):ℂ)-1))) x :=
    analyticAt_const.div
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).mul
        ((analyticAt_id.sub analyticAt_const).sub analyticAt_const))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) (sub_ne_zero.mpr hx)) hn)
  apply (hh.mul_analytic ha).congr
  have he : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ) :=
    (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds
  have he1 : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ)+1 :=
    (eventually_ne_nhds hx1).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,he1] with z hz hz1
  have hnz : z-((2*m:ℕ):ℂ)-1≠0 := by intro h; apply hz1; linear_combination h
  simp only [mul_sub,mul_add,Finset.mul_sum,←Finset.sum_add_distrib,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [fullShiftMatrix_factor,Nat.reduceAdd,Nat.cast_one,Nat.cast_ofNat,pow_one,
    Ring.choose_one_right,choose_two_complex,firstLayer,secondLayer]
  field_simp [I_ne_zero,sub_ne_zero.mpr hz,hnz]
  ring

#print axioms PoleSystem.top_germ
#print axioms PoleSystem.first_normalized_germ
#print axioms PoleSystem.second_normalized_germ
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermJetGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid SmallLevelTwentySixUnitMMM SmallLevelFiniteGridSupport
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm

def slopeLinearMap (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 780→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := slopeRows m f ε n s
  map_add' v w := by
    funext i
    cases i <;> simp [slopeRows,gridSample_add,mul_add]
  map_smul' c v := by
    funext i
    cases i <;> simp [slopeRows,gridSample_smul,mul_left_comm]

theorem leading_sum_extension (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v : Fin 320→ℂ) (i : GridSource) :
    (∑ j,fullLeadingMatrix m f ε s i j*v j)=
      gridLeadingRows m f ε s (extension support v) i := by
  change (fullLeadingMatrix m f ε s *ᵥ v) i=_
  rw [fullLeadingMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

theorem slope_sum_extension (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 320→ℂ) (i : GridSource) :
    (∑ j,fullSlopeMatrix m f ε n s i j*v j)=
      slopeRows m f ε n s (extension support v) i := by
  change (((slopeLinearMap m f ε n s).comp (extension support)).toMatrix' *ᵥ v) i=_
  rw [LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

def normalizedLayer (m : ℕ) (G : ℂ→Fin 320→ℂ) (z : ℂ) : ℕ→Fin 320→ℂ
  | 0 => G z
  | 1 => firstLayer m G z
  | _+2 => secondLayer m G z

/-- All three original normalized Taylor layers hold modulo analytic
germs, expressed in the same prime-rate Laurent formulas as the replay. -/
theorem PoleSystem.laurent_jet_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (n : Fin 3) (i : GridSource) :
    HasAnalyticGerm (fun z => laurentJetRow n (parameter 2 m z) (parameter 3 m z)
      (parameter 13 m z) (parameter 5 m z) (phase m ε)
      (badParameter f 2) (badParameter f 13) (badParameter f 3) (badParameter f 5)
      (fun h => extension support (normalizedLayer m S.G z h)) i) x := by
  fin_cases n
  · have hh := S.top_germ x hshift i
    simp_rw [leading_sum_extension] at hh
    simpa [laurentJetRow_physical,normalizedLayer] using hh
  · have hh := S.first_normalized_germ x hshift hx i
    simp_rw [Finset.sum_sub_distrib,leading_sum_extension,slope_sum_extension] at hh
    simpa [laurentJetRow_physical,normalizedLayer,Finset.sum_range_succ] using hh
  · have hh := S.second_normalized_germ x hshift hx hx1 i
    simp_rw [Finset.sum_sub_distrib,←Finset.sum_div,leading_sum_extension,slope_sum_extension] at hh
    simpa [laurentJetRow_physical,normalizedLayer,Finset.sum_range_succ,sub_sub,add_comm] using hh

#print axioms leading_sum_extension
#print axioms slope_sum_extension
#print axioms PoleSystem.laurent_jet_germ
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermPoleSystemUniquenessV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open Filter
open scoped Topology

/-- Independently constructed original continuations agree, even if their
row systems use different auxiliary sign witnesses. -/
theorem PoleSystem.germ_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : PoleSystem m f η) (x : ℂ) (i : Fin 320) :
    (fun z => S.G z i)=ᶠ[𝓝[≠] x] (fun z => T.G z i) := by
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max S.B T.B)
  · intro z _
    exact (S.meromorphic i z).meromorphicAt
  · intro z _
    exact (T.meromorphic i z).meromorphicAt
  · intro z hz
    exact congrFun ((S.agreement z (lt_of_le_of_lt (le_max_left _ _) hz)).trans
      (T.agreement z (lt_of_le_of_lt (le_max_right _ _) hz)).symm) i
  · linarith

theorem PoleSystem.G_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : PoleSystem m f η) : S.G=T.G := by
  funext x i
  exact (((S.meromorphic i x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (T.meromorphic i x)).mp (S.germ_eq T x i)).eq_of_nhds

theorem PoleSystem.order_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : PoleSystem m f η) (x : ℂ) (i : Fin 320) :
    meromorphicOrderAt (fun z => S.G z i) x=meromorphicOrderAt (fun z => T.G z i) x :=
  meromorphicOrderAt_congr (S.germ_eq T x i)

/-- The enlarged 397-row system uses the same continued functions as the
earlier grid system. This permits combining their independently checked
rank and Taylor-germ consequences. -/
theorem PoleSystem.grid_germ_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f η)
    (x : ℂ) (i : Fin 320) :
    (fun z => S.G z i)=ᶠ[𝓝[≠] x] (fun z => T.G z i) := by
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max S.B T.B)
  · intro z _
    exact (S.meromorphic i z).meromorphicAt
  · intro z _
    exact (T.meromorphic i z).meromorphicAt
  · intro z hz
    exact congrFun ((S.agreement z (lt_of_le_of_lt (le_max_left _ _) hz)).trans
      (T.agreement z (lt_of_le_of_lt (le_max_right _ _) hz)).symm) i
  · linarith

theorem PoleSystem.grid_G_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f η) : S.G=T.G := by
  funext x i
  exact (((S.meromorphic i x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (T.meromorphic i x)).mp (S.grid_germ_eq T x i)).eq_of_nhds

theorem PoleSystem.grid_order_eq {m : ℕ} {f : ℕ→ℂ} {ε η : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f η)
    (x : ℂ) (i : Fin 320) :
    meromorphicOrderAt (fun z => S.G z i) x=meromorphicOrderAt (fun z => T.G z i) x :=
  meromorphicOrderAt_congr (S.grid_germ_eq T x i)

#print axioms PoleSystem.G_eq
#print axioms PoleSystem.order_eq
#print axioms PoleSystem.grid_G_eq
#print axioms PoleSystem.grid_order_eq
end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSignScalingParityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid

theorem word_scale_sign (i : Fin 235) (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource i))*u^(groupPowers i).1*v^(groupPowers i).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource i)) := by
  fin_cases i
  · exact word_scale_sign_0 u v hu hv
  · exact word_scale_sign_1 u v hu hv
  · exact word_scale_sign_2 u v hu hv
  · exact word_scale_sign_3 u v hu hv
  · exact word_scale_sign_4 u v hu hv
  · exact word_scale_sign_5 u v hu hv
  · exact word_scale_sign_6 u v hu hv
  · exact word_scale_sign_7 u v hu hv
  · exact word_scale_sign_8 u v hu hv
  · exact word_scale_sign_9 u v hu hv
  · exact word_scale_sign_10 u v hu hv
  · exact word_scale_sign_11 u v hu hv
  · exact word_scale_sign_12 u v hu hv
  · exact word_scale_sign_13 u v hu hv
  · exact word_scale_sign_14 u v hu hv
  · exact word_scale_sign_15 u v hu hv
  · exact word_scale_sign_16 u v hu hv
  · exact word_scale_sign_17 u v hu hv
  · exact word_scale_sign_18 u v hu hv
  · exact word_scale_sign_19 u v hu hv
  · exact word_scale_sign_20 u v hu hv
  · exact word_scale_sign_21 u v hu hv
  · exact word_scale_sign_22 u v hu hv
  · exact word_scale_sign_23 u v hu hv
  · exact word_scale_sign_24 u v hu hv
  · exact word_scale_sign_25 u v hu hv
  · exact word_scale_sign_26 u v hu hv
  · exact word_scale_sign_27 u v hu hv
  · exact word_scale_sign_28 u v hu hv
  · exact word_scale_sign_29 u v hu hv
  · exact word_scale_sign_30 u v hu hv
  · exact word_scale_sign_31 u v hu hv
  · exact word_scale_sign_32 u v hu hv
  · exact word_scale_sign_33 u v hu hv
  · exact word_scale_sign_34 u v hu hv
  · exact word_scale_sign_35 u v hu hv
  · exact word_scale_sign_36 u v hu hv
  · exact word_scale_sign_37 u v hu hv
  · exact word_scale_sign_38 u v hu hv
  · exact word_scale_sign_39 u v hu hv
  · exact word_scale_sign_40 u v hu hv
  · exact word_scale_sign_41 u v hu hv
  · exact word_scale_sign_42 u v hu hv
  · exact word_scale_sign_43 u v hu hv
  · exact word_scale_sign_44 u v hu hv
  · exact word_scale_sign_45 u v hu hv
  · exact word_scale_sign_46 u v hu hv
  · exact word_scale_sign_47 u v hu hv
  · exact word_scale_sign_48 u v hu hv
  · exact word_scale_sign_49 u v hu hv
  · exact word_scale_sign_50 u v hu hv
  · exact word_scale_sign_51 u v hu hv
  · exact word_scale_sign_52 u v hu hv
  · exact word_scale_sign_53 u v hu hv
  · exact word_scale_sign_54 u v hu hv
  · exact word_scale_sign_55 u v hu hv
  · exact word_scale_sign_56 u v hu hv
  · exact word_scale_sign_57 u v hu hv
  · exact word_scale_sign_58 u v hu hv
  · exact word_scale_sign_59 u v hu hv
  · exact word_scale_sign_60 u v hu hv
  · exact word_scale_sign_61 u v hu hv
  · exact word_scale_sign_62 u v hu hv
  · exact word_scale_sign_63 u v hu hv
  · exact word_scale_sign_64 u v hu hv
  · exact word_scale_sign_65 u v hu hv
  · exact word_scale_sign_66 u v hu hv
  · exact word_scale_sign_67 u v hu hv
  · exact word_scale_sign_68 u v hu hv
  · exact word_scale_sign_69 u v hu hv
  · exact word_scale_sign_70 u v hu hv
  · exact word_scale_sign_71 u v hu hv
  · exact word_scale_sign_72 u v hu hv
  · exact word_scale_sign_73 u v hu hv
  · exact word_scale_sign_74 u v hu hv
  · exact word_scale_sign_75 u v hu hv
  · exact word_scale_sign_76 u v hu hv
  · exact word_scale_sign_77 u v hu hv
  · exact word_scale_sign_78 u v hu hv
  · exact word_scale_sign_79 u v hu hv
  · exact word_scale_sign_80 u v hu hv
  · exact word_scale_sign_81 u v hu hv
  · exact word_scale_sign_82 u v hu hv
  · exact word_scale_sign_83 u v hu hv
  · exact word_scale_sign_84 u v hu hv
  · exact word_scale_sign_85 u v hu hv
  · exact word_scale_sign_86 u v hu hv
  · exact word_scale_sign_87 u v hu hv
  · exact word_scale_sign_88 u v hu hv
  · exact word_scale_sign_89 u v hu hv
  · exact word_scale_sign_90 u v hu hv
  · exact word_scale_sign_91 u v hu hv
  · exact word_scale_sign_92 u v hu hv
  · exact word_scale_sign_93 u v hu hv
  · exact word_scale_sign_94 u v hu hv
  · exact word_scale_sign_95 u v hu hv
  · exact word_scale_sign_96 u v hu hv
  · exact word_scale_sign_97 u v hu hv
  · exact word_scale_sign_98 u v hu hv
  · exact word_scale_sign_99 u v hu hv
  · exact word_scale_sign_100 u v hu hv
  · exact word_scale_sign_101 u v hu hv
  · exact word_scale_sign_102 u v hu hv
  · exact word_scale_sign_103 u v hu hv
  · exact word_scale_sign_104 u v hu hv
  · exact word_scale_sign_105 u v hu hv
  · exact word_scale_sign_106 u v hu hv
  · exact word_scale_sign_107 u v hu hv
  · exact word_scale_sign_108 u v hu hv
  · exact word_scale_sign_109 u v hu hv
  · exact word_scale_sign_110 u v hu hv
  · exact word_scale_sign_111 u v hu hv
  · exact word_scale_sign_112 u v hu hv
  · exact word_scale_sign_113 u v hu hv
  · exact word_scale_sign_114 u v hu hv
  · exact word_scale_sign_115 u v hu hv
  · exact word_scale_sign_116 u v hu hv
  · exact word_scale_sign_117 u v hu hv
  · exact word_scale_sign_118 u v hu hv
  · exact word_scale_sign_119 u v hu hv
  · exact word_scale_sign_120 u v hu hv
  · exact word_scale_sign_121 u v hu hv
  · exact word_scale_sign_122 u v hu hv
  · exact word_scale_sign_123 u v hu hv
  · exact word_scale_sign_124 u v hu hv
  · exact word_scale_sign_125 u v hu hv
  · exact word_scale_sign_126 u v hu hv
  · exact word_scale_sign_127 u v hu hv
  · exact word_scale_sign_128 u v hu hv
  · exact word_scale_sign_129 u v hu hv
  · exact word_scale_sign_130 u v hu hv
  · exact word_scale_sign_131 u v hu hv
  · exact word_scale_sign_132 u v hu hv
  · exact word_scale_sign_133 u v hu hv
  · exact word_scale_sign_134 u v hu hv
  · exact word_scale_sign_135 u v hu hv
  · exact word_scale_sign_136 u v hu hv
  · exact word_scale_sign_137 u v hu hv
  · exact word_scale_sign_138 u v hu hv
  · exact word_scale_sign_139 u v hu hv
  · exact word_scale_sign_140 u v hu hv
  · exact word_scale_sign_141 u v hu hv
  · exact word_scale_sign_142 u v hu hv
  · exact word_scale_sign_143 u v hu hv
  · exact word_scale_sign_144 u v hu hv
  · exact word_scale_sign_145 u v hu hv
  · exact word_scale_sign_146 u v hu hv
  · exact word_scale_sign_147 u v hu hv
  · exact word_scale_sign_148 u v hu hv
  · exact word_scale_sign_149 u v hu hv
  · exact word_scale_sign_150 u v hu hv
  · exact word_scale_sign_151 u v hu hv
  · exact word_scale_sign_152 u v hu hv
  · exact word_scale_sign_153 u v hu hv
  · exact word_scale_sign_154 u v hu hv
  · exact word_scale_sign_155 u v hu hv
  · exact word_scale_sign_156 u v hu hv
  · exact word_scale_sign_157 u v hu hv
  · exact word_scale_sign_158 u v hu hv
  · exact word_scale_sign_159 u v hu hv
  · exact word_scale_sign_160 u v hu hv
  · exact word_scale_sign_161 u v hu hv
  · exact word_scale_sign_162 u v hu hv
  · exact word_scale_sign_163 u v hu hv
  · exact word_scale_sign_164 u v hu hv
  · exact word_scale_sign_165 u v hu hv
  · exact word_scale_sign_166 u v hu hv
  · exact word_scale_sign_167 u v hu hv
  · exact word_scale_sign_168 u v hu hv
  · exact word_scale_sign_169 u v hu hv
  · exact word_scale_sign_170 u v hu hv
  · exact word_scale_sign_171 u v hu hv
  · exact word_scale_sign_172 u v hu hv
  · exact word_scale_sign_173 u v hu hv
  · exact word_scale_sign_174 u v hu hv
  · exact word_scale_sign_175 u v hu hv
  · exact word_scale_sign_176 u v hu hv
  · exact word_scale_sign_177 u v hu hv
  · exact word_scale_sign_178 u v hu hv
  · exact word_scale_sign_179 u v hu hv
  · exact word_scale_sign_180 u v hu hv
  · exact word_scale_sign_181 u v hu hv
  · exact word_scale_sign_182 u v hu hv
  · exact word_scale_sign_183 u v hu hv
  · exact word_scale_sign_184 u v hu hv
  · exact word_scale_sign_185 u v hu hv
  · exact word_scale_sign_186 u v hu hv
  · exact word_scale_sign_187 u v hu hv
  · exact word_scale_sign_188 u v hu hv
  · exact word_scale_sign_189 u v hu hv
  · exact word_scale_sign_190 u v hu hv
  · exact word_scale_sign_191 u v hu hv
  · exact word_scale_sign_192 u v hu hv
  · exact word_scale_sign_193 u v hu hv
  · exact word_scale_sign_194 u v hu hv
  · exact word_scale_sign_195 u v hu hv
  · exact word_scale_sign_196 u v hu hv
  · exact word_scale_sign_197 u v hu hv
  · exact word_scale_sign_198 u v hu hv
  · exact word_scale_sign_199 u v hu hv
  · exact word_scale_sign_200 u v hu hv
  · exact word_scale_sign_201 u v hu hv
  · exact word_scale_sign_202 u v hu hv
  · exact word_scale_sign_203 u v hu hv
  · exact word_scale_sign_204 u v hu hv
  · exact word_scale_sign_205 u v hu hv
  · exact word_scale_sign_206 u v hu hv
  · exact word_scale_sign_207 u v hu hv
  · exact word_scale_sign_208 u v hu hv
  · exact word_scale_sign_209 u v hu hv
  · exact word_scale_sign_210 u v hu hv
  · exact word_scale_sign_211 u v hu hv
  · exact word_scale_sign_212 u v hu hv
  · exact word_scale_sign_213 u v hu hv
  · exact word_scale_sign_214 u v hu hv
  · exact word_scale_sign_215 u v hu hv
  · exact word_scale_sign_216 u v hu hv
  · exact word_scale_sign_217 u v hu hv
  · exact word_scale_sign_218 u v hu hv
  · exact word_scale_sign_219 u v hu hv
  · exact word_scale_sign_220 u v hu hv
  · exact word_scale_sign_221 u v hu hv
  · exact word_scale_sign_222 u v hu hv
  · exact word_scale_sign_223 u v hu hv
  · exact word_scale_sign_224 u v hu hv
  · exact word_scale_sign_225 u v hu hv
  · exact word_scale_sign_226 u v hu hv
  · exact word_scale_sign_227 u v hu hv
  · exact word_scale_sign_228 u v hu hv
  · exact word_scale_sign_229 u v hu hv
  · exact word_scale_sign_230 u v hu hv
  · exact word_scale_sign_231 u v hu hv
  · exact word_scale_sign_232 u v hu hv
  · exact word_scale_sign_233 u v hu hv
  · exact word_scale_sign_234 u v hu hv

theorem taylor_scale_sign (i : Fin 53) (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ i then -c else 1)*(-1))*u^(taylorPowers i).1*v^(taylorPowers i).2.2.1=
      ((if 2∣gridTaylorQ i then u else 1)*(if 13∣gridTaylorQ i then -(c*v) else 1))*(-u*v) := by
  fin_cases i
  · exact taylor_scale_sign_0 c u v hu hv
  · exact taylor_scale_sign_1 c u v hu hv
  · exact taylor_scale_sign_2 c u v hu hv
  · exact taylor_scale_sign_3 c u v hu hv
  · exact taylor_scale_sign_4 c u v hu hv
  · exact taylor_scale_sign_5 c u v hu hv
  · exact taylor_scale_sign_6 c u v hu hv
  · exact taylor_scale_sign_7 c u v hu hv
  · exact taylor_scale_sign_8 c u v hu hv
  · exact taylor_scale_sign_9 c u v hu hv
  · exact taylor_scale_sign_10 c u v hu hv
  · exact taylor_scale_sign_11 c u v hu hv
  · exact taylor_scale_sign_12 c u v hu hv
  · exact taylor_scale_sign_13 c u v hu hv
  · exact taylor_scale_sign_14 c u v hu hv
  · exact taylor_scale_sign_15 c u v hu hv
  · exact taylor_scale_sign_16 c u v hu hv
  · exact taylor_scale_sign_17 c u v hu hv
  · exact taylor_scale_sign_18 c u v hu hv
  · exact taylor_scale_sign_19 c u v hu hv
  · exact taylor_scale_sign_20 c u v hu hv
  · exact taylor_scale_sign_21 c u v hu hv
  · exact taylor_scale_sign_22 c u v hu hv
  · exact taylor_scale_sign_23 c u v hu hv
  · exact taylor_scale_sign_24 c u v hu hv
  · exact taylor_scale_sign_25 c u v hu hv
  · exact taylor_scale_sign_26 c u v hu hv
  · exact taylor_scale_sign_27 c u v hu hv
  · exact taylor_scale_sign_28 c u v hu hv
  · exact taylor_scale_sign_29 c u v hu hv
  · exact taylor_scale_sign_30 c u v hu hv
  · exact taylor_scale_sign_31 c u v hu hv
  · exact taylor_scale_sign_32 c u v hu hv
  · exact taylor_scale_sign_33 c u v hu hv
  · exact taylor_scale_sign_34 c u v hu hv
  · exact taylor_scale_sign_35 c u v hu hv
  · exact taylor_scale_sign_36 c u v hu hv
  · exact taylor_scale_sign_37 c u v hu hv
  · exact taylor_scale_sign_38 c u v hu hv
  · exact taylor_scale_sign_39 c u v hu hv
  · exact taylor_scale_sign_40 c u v hu hv
  · exact taylor_scale_sign_41 c u v hu hv
  · exact taylor_scale_sign_42 c u v hu hv
  · exact taylor_scale_sign_43 c u v hu hv
  · exact taylor_scale_sign_44 c u v hu hv
  · exact taylor_scale_sign_45 c u v hu hv
  · exact taylor_scale_sign_46 c u v hu hv
  · exact taylor_scale_sign_47 c u v hu hv
  · exact taylor_scale_sign_48 c u v hu hv
  · exact taylor_scale_sign_49 c u v hu hv
  · exact taylor_scale_sign_50 c u v hu hv
  · exact taylor_scale_sign_51 c u v hu hv
  · exact taylor_scale_sign_52 c u v hu hv

#print axioms word_scale_sign
#print axioms taylor_scale_sign

end SmallLevelTwentySixGermSources
end
end

/-! ## SmallLevelTwentySixGermSignScalingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid
open Complex

theorem monomial_scale (e : ℤ×ℤ×ℤ×ℤ) (X Y Z W u v : ℂ) :
    SmallLevelFourPrimeRates.monomial e (u*X) Y (v*Z) W=
      (u^e.1*v^e.2.2.1)*SmallLevelFourPrimeRates.monomial e X Y Z W := by
  simp only [SmallLevelFourPrimeRates.monomial,mul_zpow]
  ring

theorem hecke_scale_sign (X Y Z W c a b u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : Fin 96) :
    laurentHecke (u*X) Y (v*Z) W (-1) c a b w i=
      laurentHecke X Y Z W (-u) (c*v) a b w i := by
  have hp : gridHeckeP i=2 ∨ gridHeckeP i=3 ∨ gridHeckeP i=13 ∨ gridHeckeP i=5 := by
    fin_cases i <;> decide
  rcases hp with hp|hp|hp|hp <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    simp [laurentHecke,hp,primeParameter,primeEigenvalue] <;> ring_nf <;> simp_all

/-- All original leading-row types respect the same sign rescaling.
Taking c=-1 or c=1 reduces the eight physical sign choices to two bases. -/
theorem laurentRows_sign_scale (X Y Z W c a b u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : GridSource) :
    laurentRows (u*X) Y (v*Z) W (-1) (-1) c a b w i=
      laurentRows X Y Z W (-u*v) (-u) (c*v) a b w i := by
  cases i with
  | word i =>
    simp only [laurentRows,neg_neg,monomial_scale]
    rw [←word_scale_sign i u v hu hv]
    ring
  | taylor i =>
    simp only [laurentRows,neg_neg,ite_self,one_mul,monomial_scale]
    rw [←taylor_scale_sign i c u v hu hv]
    ring
  | entire i => rfl
  | infinity i => rfl
  | hecke i => exact hecke_scale_sign X Y Z W c a b u v hu hv w i

/-- Sign covariance also holds for every lower Taylor layer. -/
theorem laurentSlopeRows_sign_scale (n : ℕ) (X Y Z W c u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : GridSource) :
    laurentSlopeRows n (u*X) Y (v*Z) W (-1) (-1) c w i=
      laurentSlopeRows n X Y Z W (-u*v) (-u) (c*v) w i := by
  cases i with
  | word i =>
    simp only [laurentSlopeRows,neg_neg,monomial_scale]
    rw [←word_scale_sign i u v hu hv]
    ring
  | taylor i =>
    simp only [laurentSlopeRows,neg_neg,ite_self,one_mul,monomial_scale]
    rw [←taylor_scale_sign i c u v hu hv]
    ring
  | entire i => rfl
  | hecke i => rfl
  | infinity i => rfl

/-- The same two sign changes transport the entire normalized Taylor row,
including all lower layers, without conditions on their pole orders. -/
theorem laurentJetRow_sign_scale (n : ℕ) (X Y Z W c a b u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (w : ℕ→Fin 780→ℂ) (i : GridSource) :
    laurentJetRow n (u*X) Y (v*Z) W (-1) (-1) c a b w i=
      laurentJetRow n X Y Z W (-u*v) (-u) (c*v) a b w i := by
  simp only [laurentJetRow,mul_div_assoc,
    laurentRows_sign_scale (hu := hu) (hv := hv),
    laurentSlopeRows_sign_scale (hu := hu) (hv := hv)]

#print axioms laurentRows_sign_scale
#print axioms laurentSlopeRows_sign_scale
#print axioms laurentJetRow_sign_scale
end SmallLevelTwentySixGermSources
end
end
end
