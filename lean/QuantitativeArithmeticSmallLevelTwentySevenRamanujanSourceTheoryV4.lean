module

public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenPhysicalPowersV1
public import QuantitativeArithmeticSmallLevelTwentySevenTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSamplesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open FinitenessRamanujanSum SmallLevelAdditive SmallLevelTaylor
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

def sampleEval (q : ℕ) (sample : ℕ → ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ a∈residues q, v (sample a)

/-- A finite, exact coordinate check identifies the sample with the actual
Ramanujan additive sum on the original half-plane of convergence. -/
theorem sample_original (point : ℕ → ℚ) {Q q : ℕ} (hQ : 0<Q) (hq : 0<q)
    (hqQ : q∣Q) (t : ℤ) (sample : ℕ → ℕ)
    (hpoint : ∀ a : Fin q, a.val.Coprime q →
      point (sample a.val)=(((t+(a.val:ℤ)*(Q/q:ℕ))%(Q:ℤ):ℤ):ℚ)/(Q:ℚ))
    (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    sampleEval q sample (fun j => original (2*m) f (point j:ℝ) s)=
      ramanujanAdditive (2*m) f q ((t:ℝ)/(Q:ℝ)) s := by
  rw [ramanujanAdditive_grid (2*m) f hQ hq hqQ]
  unfold sampleEval
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  have hal : a<q := Finset.mem_range.mp ha'.1
  exact point_grid point Q hQ _ _ (hpoint ⟨a,hal⟩ ha'.2) m f s

/-- The leading Taylor coefficient is the exact Laurent monomial occurring
in the source certificate, once its rational dilation has been checked. -/
theorem taylor_zero_physical (L m : ℕ) (r : ℚ) (e₂ e₃ e₅ e₇ : ℤ)
    (hscale : (L:ℚ)*r^2=(2:ℚ)^e₂*3^e₃*5^e₅*7^e₇) (η s : ℂ) :
    taylorRowScalar (2*m) L r η 0 s=
      η*(primeRate 2 m s^e₂*primeRate 3 m s^e₃*
        primeRate 5 m s^e₅*primeRate 7 m s^e₇) := by
  have he : (L:ℝ)*(r:ℝ)^2=(2:ℝ)^e₂*3^e₃*5^e₅*7^e₇ := by
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_zpow] using
      congrArg (fun x : ℚ => (x:ℝ)) hscale
  have hk : (((2*m:ℕ):ℂ)/2)=(m:ℂ) := by push_cast; ring
  simp only [taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hk]
  rw [he]
  exact congrArg (fun z : ℂ => η*z) (by
    simpa only [Complex.ofReal_natCast] using four_prime_power e₂ e₃ e₅ e₇ (m:ℝ) s)
#print axioms sample_original
#print axioms taylor_zero_physical
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory
open FinitenessOriginalFourier FinitenessFourierConstruction FinitenessRamanujanFourier
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

structure Spec where
  source : ℕ
  Q : ℕ
  q : ℕ
  t : ℤ
  u : ℤ
  left : ℕ → ℕ
  right : ℕ → ℕ
  e₂ : ℤ
  e₃ : ℤ
  e₅ : ℤ
  e₇ : ℤ

def Valid (point : ℕ → ℚ) (r : Spec) : Prop :=
  0<r.Q ∧ 0<r.q ∧ r.q∣r.Q ∧ r.t≠0 ∧
  -1/((Nat.lcm 27 (r.q^2):ℚ)*((r.t:ℚ)/r.Q))=(r.u:ℚ)/r.Q ∧
  (Nat.lcm 27 (r.q^2):ℚ)*((r.t:ℚ)/r.Q)^2=(2:ℚ)^r.e₂*3^r.e₃*5^r.e₅*7^r.e₇ ∧
  (∀ a : Fin r.q, a.val.Coprime r.q →
    point (r.left a.val)=(((r.t+(a.val:ℤ)*(r.Q/r.q:ℕ))%(r.Q:ℤ):ℤ):ℚ)/(r.Q:ℚ)) ∧
  (∀ a : Fin r.q, a.val.Coprime r.q →
    point (r.right a.val)=(((r.u+(a.val:ℤ)*(r.Q/r.q:ℕ))%(r.Q:ℤ):ℤ):ℚ)/(r.Q:ℚ))

def leading (r : Spec) (m : ℕ) (η s : ℂ) (v : ℕ → ℂ) : ℂ :=
  sampleEval r.q r.left v-
    taylorRowScalar (2*m) (Nat.lcm 27 (r.q^2)) ((r.t:ℝ)/r.Q) η 0 s*sampleEval r.q r.right v

def shift (r : Spec) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  taylorRowScalar (2*m) (Nat.lcm 27 (r.q^2)) ((r.t:ℝ)/r.Q) η (n+1) s*sampleEval r.q r.right v

def formalLeading (r : Spec) (x y z w η : ℂ) (v : ℕ → ℂ) : ℂ :=
  sampleEval r.q r.left v-η*(x^r.e₂*y^r.e₃*z^r.e₅*w^r.e₇)*sampleEval r.q r.right v

theorem physical_leading (point : ℕ → ℚ) (r : Spec) (hr : Valid point r)
    (m : ℕ) (η s : ℂ) (v : ℕ → ℂ) :
    leading r m η s v=
      formalLeading r (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s) η v := by
  have h := taylor_zero_physical (Nat.lcm 27 (r.q^2)) m ((r.t:ℚ)/r.Q)
    r.e₂ r.e₃ r.e₅ r.e₇ hr.2.2.2.2.2.1 η s
  simp only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] at h
  unfold leading formalLeading
  rw [h]

/-- Every finite coordinate specification satisfying the explicit rational
checks gives a genuine Taylor row, with the same sign for all rows. -/
theorem original_rows (point : ℕ → ℚ) (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ r : Spec, Valid point r →
      ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          leading r m η s (fun j => original (2*m) f (point j:ℝ) s)=
            error M s+∑ n∈Finset.range M,
              shift r m η n s (fun j => original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  obtain ⟨η,hη,hlaw⟩ := QuantitativeArithmeticSmallLevelTwentySeven.original_ramanujan_split m hf
  refine ⟨η,hη,?_⟩
  intro r hr
  rcases hr with ⟨hQ,hq,hqQ,ht,hu,_,hleft,hright⟩
  have hr0 : (r.t:ℝ)/(r.Q:ℝ)≠0 := div_ne_zero (by exact_mod_cast ht) (by exact_mod_cast hQ.ne')
  have hu' : -1/((Nat.lcm 27 (r.q^2):ℝ)*((r.t:ℝ)/r.Q))=(r.u:ℝ)/r.Q := by
    exact_mod_cast hu
  obtain ⟨B,hB⟩ := hlaw r.q hq ((r.t:ℝ)/r.Q) hr0
  refine ⟨B,fun M => mellin (frickeError (2*m) (fullCoefficients (twisted f r.q) (2*m))
    (Nat.lcm 27 (r.q^2)) ((r.t:ℝ)/r.Q) η (M+1)),?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro s hs
  have h := (hB M).2 s hs
  rw [hu'] at h
  simpa only [leading,shift,
    sample_original point hQ hq hqQ r.t r.left hleft,
    sample_original point hQ hq hqQ r.u r.right hright] using h
#print axioms physical_leading
#print axioms original_rows
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourcePart15Slice1V1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def left184 : ℕ → ℕ
  | 1 => 604
  | 2 => 605
  | 3 => 606
  | 4 => 480
  | _ => 0
def right184 : ℕ → ℕ
  | 1 => 135
  | 2 => 19
  | 3 => 37
  | 4 => 96
  | _ => 0
def spec184 : Spec := ⟨531,1890,5,3,-1764,left184,right184,-2,-1,0,-2⟩
theorem valid184 : Valid point spec184 := by
  dsimp only [Valid,spec184]
  decide +kernel
theorem row184 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 531)=formalLeading spec184 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec184,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left184,right184] <;> ring
def left185 : ℕ → ℕ
  | 1 => 40
  | 2 => 222
  | 4 => 223
  | 7 => 224
  | 8 => 44
  | 11 => 225
  | 13 => 71
  | 14 => 226
  | _ => 0
def right185 : ℕ → ℕ
  | 1 => 37
  | 2 => 134
  | 4 => 96
  | 7 => 38
  | 8 => 94
  | 11 => 50
  | 13 => 19
  | 14 => 56
  | _ => 0
def spec185 : Spec := ⟨532,270,15,1,-108,left185,right185,-2,-3,0,0⟩
theorem valid185 : Valid point spec185 := by
  dsimp only [Valid,spec185]
  decide +kernel
theorem row185 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 532)=formalLeading spec185 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec185,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left185,right185] <;> ring
def left186 : ℕ → ℕ
  | 1 => 227
  | 2 => 73
  | 4 => 228
  | 7 => 17
  | 8 => 229
  | 11 => 230
  | 13 => 231
  | 14 => 63
  | _ => 0
def right186 : ℕ → ℕ
  | 1 => 19
  | 2 => 56
  | 4 => 37
  | 7 => 96
  | 8 => 64
  | 11 => 94
  | 13 => 135
  | 14 => 50
  | _ => 0
def spec186 : Spec := ⟨533,270,15,-1,108,left186,right186,-2,-3,0,0⟩
theorem valid186 : Valid point spec186 := by
  dsimp only [Valid,spec186]
  decide +kernel
theorem row186 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 533)=formalLeading spec186 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec186,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left186,right186] <;> ring
def left187 : ℕ → ℕ
  | 1 => 412
  | 2 => 8
  | 3 => 414
  | 4 => 415
  | 5 => 416
  | 6 => 417
  | _ => 0
def right187 : ℕ → ℕ
  | 1 => 318
  | 2 => 413
  | 3 => 356
  | 4 => 3
  | 5 => 359
  | 6 => 418
  | _ => 0
def spec187 : Spec := ⟨535,378,7,4,-27,left187,right187,2,-3,0,0⟩
theorem valid187 : Valid point spec187 := by
  dsimp only [Valid,spec187]
  decide +kernel
theorem row187 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 535)=formalLeading spec187 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec187,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left187,right187] <;> ring
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourcePart15Slice2V1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def left188 : ℕ → ℕ
  | 1 => 402
  | 2 => 403
  | 3 => 404
  | 4 => 405
  | 5 => 95
  | 6 => 406
  | _ => 0
def right188 : ℕ → ℕ
  | 1 => 301
  | 2 => 373
  | 3 => 50
  | 4 => 279
  | 5 => 365
  | 6 => 370
  | _ => 0
def spec188 : Spec := ⟨541,378,7,3,-36,left188,right188,-2,-1,0,0⟩
theorem valid188 : Valid point spec188 := by
  dsimp only [Valid,spec188]
  decide +kernel
theorem row188 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 541)=formalLeading spec188 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec188,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left188,right188] <;> ring
def left189 : ℕ → ℕ
  | 1 => 407
  | 2 => 97
  | 3 => 408
  | 4 => 409
  | 5 => 410
  | 6 => 411
  | _ => 0
def right189 : ℕ → ℕ
  | 1 => 371
  | 2 => 364
  | 3 => 293
  | 4 => 37
  | 5 => 372
  | 6 => 302
  | _ => 0
def spec189 : Spec := ⟨542,378,7,-3,36,left189,right189,-2,-1,0,0⟩
theorem valid189 : Valid point spec189 := by
  dsimp only [Valid,spec189]
  decide +kernel
theorem row189 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 542)=formalLeading spec189 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec189,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left189,right189] <;> ring
def left190 : ℕ → ℕ
  | 1 => 382
  | 2 => 383
  | 3 => 384
  | 4 => 35
  | 5 => 385
  | 6 => 386
  | _ => 0
def right190 : ℕ → ℕ
  | 1 => 333
  | 2 => 2
  | 3 => 332
  | 4 => 331
  | 5 => 335
  | 6 => 334
  | _ => 0
def spec190 : Spec := ⟨546,378,7,1,-108,left190,right190,-2,-3,0,0⟩
theorem valid190 : Valid point spec190 := by
  dsimp only [Valid,spec190]
  decide +kernel
theorem row190 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 546)=formalLeading spec190 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec190,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left190,right190] <;> ring
def left191 : ℕ → ℕ
  | 1 => 387
  | 2 => 388
  | 3 => 66
  | 4 => 389
  | 5 => 390
  | 6 => 391
  | _ => 0
def right191 : ℕ → ℕ
  | 1 => 335
  | 2 => 334
  | 3 => 330
  | 4 => 333
  | 5 => 2
  | 6 => 332
  | _ => 0
def spec191 : Spec := ⟨547,378,7,-1,108,left191,right191,-2,-3,0,0⟩
theorem valid191 : Valid point spec191 := by
  dsimp only [Valid,spec191]
  decide +kernel
theorem row191 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 547)=formalLeading spec191 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec191,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left191,right191] <;> ring
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceUnitIndexDataSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def left180 : ℕ → ℕ
  | 1 => 419
  | 2 => 420
  | 3 => 421
  | 4 => 422
  | 5 => 26
  | 6 => 423
  | _ => 0
def right180 : ℕ → ℕ
  | 1 => 413
  | 2 => 356
  | 3 => 3
  | 4 => 359
  | 5 => 418
  | 6 => 271
  | _ => 0
def spec180 : Spec := ⟨520,378,7,-4,27,left180,right180,2,-3,0,0⟩
theorem valid180 : Valid point spec180 := by
  dsimp only [Valid,spec180]
  decide +kernel

def left181 : ℕ → ℕ
  | 1 => 72
  | 3 => 458
  | 5 => 486
  | 9 => 487
  | 11 => 469
  | 13 => 297
  | _ => 0
def right181 : ℕ → ℕ
  | 1 => 2
  | 3 => 332
  | 5 => 331
  | 9 => 334
  | 11 => 330
  | 13 => 333
  | _ => 0
def spec181 : Spec := ⟨521,378,14,1,-27,left181,right181,0,-3,0,0⟩
theorem valid181 : Valid point spec181 := by
  dsimp only [Valid,spec181]
  decide +kernel

def left182 : ℕ → ℕ
  | 1 => 325
  | 2 => 312
  | 4 => 310
  | 5 => 573
  | 8 => 507
  | 10 => 34
  | 11 => 574
  | 13 => 318
  | 16 => 482
  | 17 => 15
  | 19 => 464
  | 20 => 446
  | 22 => 435
  | 23 => 575
  | 25 => 407
  | 26 => 387
  | 29 => 576
  | 31 => 20
  | 32 => 577
  | 34 => 526
  | 37 => 483
  | 38 => 142
  | 40 => 413
  | 41 => 447
  | 43 => 462
  | 44 => 509
  | 46 => 478
  | 47 => 578
  | 50 => 579
  | 52 => 97
  | 53 => 388
  | 55 => 403
  | 58 => 358
  | 59 => 120
  | 61 => 346
  | 62 => 338
  | 64 => 344
  | 65 => 580
  | 67 => 356
  | 68 => 581
  | 71 => 510
  | 73 => 12
  | 74 => 582
  | 76 => 366
  | 79 => 408
  | 80 => 66
  | 82 => 404
  | 83 => 448
  | 85 => 431
  | 86 => 583
  | 88 => 479
  | 89 => 511
  | 92 => 320
  | 94 => 3
  | 95 => 316
  | 97 => 275
  | 100 => 484
  | 101 => 44
  | 103 => 437
  | 104 => 449
  | 106 => 409
  | 107 => 389
  | 109 => 405
  | 110 => 584
  | 113 => 585
  | 115 => 60
  | 116 => 512
  | 118 => 524
  | 121 => 359
  | 122 => 121
  | 124 => 347
  | 125 => 339
  | 127 => 345
  | 128 => 586
  | 130 => 357
  | 131 => 587
  | 134 => 390
  | 136 => 95
  | 137 => 588
  | 139 => 367
  | 142 => 485
  | 143 => 136
  | 145 => 465
  | 146 => 450
  | 148 => 418
  | 149 => 589
  | 151 => 480
  | 152 => 513
  | 155 => 590
  | 157 => 55
  | 158 => 591
  | 160 => 411
  | 163 => 406
  | 164 => 71
  | 166 => 434
  | 167 => 451
  | 169 => 463
  | 170 => 514
  | 172 => 481
  | 173 => 592
  | 176 => 593
  | 178 => 42
  | 179 => 515
  | 181 => 270
  | 184 => 287
  | 185 => 30
  | 187 => 326
  | 188 => 322
  | _ => 0
def right182 : ℕ → ℕ
  | 1 => 324
  | 2 => 2
  | 4 => 311
  | 5 => 304
  | 8 => 290
  | 10 => 300
  | 11 => 301
  | 13 => 490
  | 16 => 72
  | 17 => 276
  | 19 => 520
  | 20 => 328
  | 22 => 457
  | 23 => 6
  | 25 => 466
  | 26 => 427
  | 29 => 332
  | 31 => 412
  | 32 => 380
  | 34 => 374
  | 37 => 98
  | 38 => 373
  | 40 => 528
  | 41 => 477
  | 43 => 458
  | 44 => 75
  | 46 => 467
  | 47 => 371
  | 50 => 430
  | 52 => 544
  | 53 => 428
  | 55 => 398
  | 58 => 8
  | 59 => 362
  | 61 => 550
  | 62 => 354
  | 64 => 342
  | 65 => 50
  | 67 => 348
  | 68 => 352
  | 71 => 360
  | 73 => 521
  | 74 => 364
  | 76 => 491
  | 79 => 14
  | 80 => 429
  | 82 => 399
  | 83 => 335
  | 85 => 414
  | 86 => 16
  | 88 => 468
  | 89 => 436
  | 92 => 279
  | 94 => 282
  | 95 => 283
  | 97 => 315
  | 100 => 31
  | 101 => 293
  | 103 => 530
  | 104 => 433
  | 106 => 459
  | 107 => 33
  | 109 => 400
  | 110 => 334
  | 113 => 424
  | 115 => 545
  | 116 => 438
  | 118 => 492
  | 121 => 46
  | 122 => 363
  | 124 => 487
  | 125 => 355
  | 127 => 343
  | 128 => 37
  | 130 => 349
  | 131 => 353
  | 134 => 361
  | 136 => 401
  | 137 => 330
  | 139 => 416
  | 142 => 53
  | 143 => 439
  | 145 => 522
  | 146 => 370
  | 148 => 460
  | 149 => 69
  | 151 => 469
  | 152 => 476
  | 155 => 372
  | 157 => 531
  | 158 => 381
  | 160 => 375
  | 163 => 39
  | 164 => 333
  | 166 => 417
  | 167 => 426
  | 169 => 461
  | 170 => 28
  | 172 => 470
  | 173 => 329
  | 176 => 296
  | 178 => 297
  | 179 => 298
  | 181 => 493
  | 184 => 1
  | 185 => 307
  | 187 => 288
  | 188 => 313
  | _ => 0
def spec182 : Spec := ⟨522,378,189,1,-4,left182,right182,-2,0,0,0⟩
theorem valid182 : Valid point spec182 := by
  dsimp only [Valid,spec182]
  decide +kernel

def left183 : ℕ → ℕ
  | 1 => 321
  | 2 => 325
  | 4 => 4
  | 5 => 310
  | 8 => 299
  | 10 => 498
  | 11 => 34
  | 13 => 552
  | 16 => 553
  | 17 => 482
  | 19 => 499
  | 20 => 464
  | 22 => 440
  | 23 => 435
  | 25 => 73
  | 26 => 407
  | 29 => 402
  | 31 => 554
  | 32 => 20
  | 34 => 555
  | 37 => 500
  | 38 => 483
  | 40 => 556
  | 41 => 413
  | 43 => 441
  | 44 => 462
  | 46 => 137
  | 47 => 478
  | 50 => 368
  | 52 => 557
  | 53 => 97
  | 55 => 383
  | 58 => 558
  | 59 => 358
  | 61 => 559
  | 62 => 346
  | 64 => 336
  | 65 => 344
  | 67 => 118
  | 68 => 356
  | 71 => 527
  | 73 => 501
  | 74 => 12
  | 76 => 560
  | 79 => 561
  | 80 => 408
  | 82 => 384
  | 83 => 404
  | 85 => 442
  | 86 => 431
  | 88 => 17
  | 89 => 479
  | 92 => 281
  | 94 => 308
  | 95 => 3
  | 97 => 319
  | 100 => 502
  | 101 => 484
  | 103 => 562
  | 104 => 437
  | 106 => 443
  | 107 => 409
  | 109 => 35
  | 110 => 405
  | 113 => 369
  | 115 => 563
  | 116 => 60
  | 118 => 503
  | 121 => 564
  | 122 => 359
  | 124 => 565
  | 125 => 347
  | 127 => 337
  | 128 => 345
  | 130 => 119
  | 131 => 357
  | 134 => 410
  | 136 => 385
  | 137 => 95
  | 139 => 566
  | 142 => 567
  | 143 => 485
  | 145 => 504
  | 146 => 465
  | 148 => 444
  | 149 => 418
  | 151 => 149
  | 152 => 480
  | 155 => 525
  | 157 => 568
  | 158 => 55
  | 160 => 569
  | 163 => 386
  | 164 => 406
  | 166 => 570
  | 167 => 434
  | 169 => 445
  | 170 => 463
  | 172 => 57
  | 173 => 481
  | 176 => 271
  | 178 => 571
  | 179 => 42
  | 181 => 506
  | 184 => 572
  | 185 => 287
  | 187 => 314
  | 188 => 326
  | _ => 0
def right183 : ℕ → ℕ
  | 1 => 304
  | 2 => 305
  | 4 => 290
  | 5 => 32
  | 8 => 494
  | 10 => 284
  | 11 => 285
  | 13 => 276
  | 16 => 328
  | 17 => 471
  | 19 => 6
  | 20 => 452
  | 22 => 427
  | 23 => 419
  | 25 => 332
  | 26 => 18
  | 29 => 376
  | 31 => 378
  | 32 => 532
  | 34 => 373
  | 37 => 477
  | 38 => 472
  | 40 => 75
  | 41 => 453
  | 43 => 371
  | 44 => 517
  | 46 => 430
  | 47 => 22
  | 50 => 420
  | 52 => 331
  | 53 => 392
  | 55 => 362
  | 58 => 354
  | 59 => 350
  | 61 => 50
  | 62 => 340
  | 64 => 352
  | 65 => 488
  | 67 => 360
  | 68 => 80
  | 71 => 495
  | 73 => 432
  | 74 => 546
  | 76 => 429
  | 79 => 335
  | 80 => 393
  | 82 => 16
  | 83 => 454
  | 85 => 436
  | 86 => 533
  | 88 => 279
  | 89 => 24
  | 92 => 309
  | 94 => 273
  | 95 => 274
  | 97 => 293
  | 100 => 433
  | 101 => 473
  | 103 => 33
  | 104 => 422
  | 106 => 334
  | 107 => 394
  | 109 => 424
  | 110 => 58
  | 113 => 496
  | 115 => 365
  | 116 => 518
  | 118 => 363
  | 121 => 355
  | 122 => 351
  | 124 => 37
  | 125 => 341
  | 127 => 353
  | 128 => 551
  | 130 => 361
  | 131 => 26
  | 134 => 395
  | 136 => 425
  | 137 => 547
  | 139 => 439
  | 142 => 370
  | 143 => 474
  | 145 => 69
  | 146 => 455
  | 148 => 476
  | 149 => 535
  | 151 => 372
  | 152 => 100
  | 155 => 377
  | 157 => 379
  | 158 => 423
  | 160 => 333
  | 163 => 426
  | 164 => 475
  | 166 => 28
  | 167 => 456
  | 169 => 329
  | 170 => 519
  | 172 => 296
  | 173 => 0
  | 176 => 497
  | 178 => 302
  | 179 => 303
  | 181 => 307
  | 184 => 313
  | 185 => 327
  | 187 => 2
  | 188 => 323
  | _ => 0
def spec183 : Spec := ⟨523,378,189,-1,4,left183,right183,-2,0,0,0⟩
theorem valid183 : Valid point spec183 := by
  dsimp only [Valid,spec183]
  decide +kernel
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSparseSampleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum

def samplePoly (ids : List ℕ) (sample : ℕ → ℕ) (r : ℚ) (e : Exponent) : Poly :=
  ids.map (fun j => (r,sample j,e))

theorem eval_samplePoly (x y z w a b c : ℂ) (v : ℕ → ℂ)
    {q : ℕ} (ids : List ℕ) (sample : ℕ → ℕ) (r : ℚ) (e : Exponent)
    (hn : ids.Nodup) (hr : ids.toFinset=residues q) :
    eval x y z w a b c v (samplePoly ids sample r e)=
      (r:ℂ)*monomial x y z w a b c e*sampleEval q sample v := by
  unfold eval samplePoly
  rw [List.map_map]
  change (ids.map (fun j => ((r:ℂ)*monomial x y z w a b c e)*v (sample j))).sum=_
  rw [List.sum_map_mul_left,← List.sum_toFinset (fun j => v (sample j)) hn,hr]
  rfl
#print axioms eval_samplePoly
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceUnitBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

theorem row180 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 520)=formalLeading spec180 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec180,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left180,right180] <;> ring

theorem row181 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 521)=formalLeading spec181 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec181,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left181,right181] <;> ring

def idsL182 : List ℕ := [94,73,17,31,185,10,178,101,157,115,80,164,136,52,59,122,143,38,181,97,184,4,2,95,13,92,188,1,187,62,125,64,127,61,124,67,130,58,121,76,139,26,53,107,134,55,82,109,163,25,79,106,160,40,148,85,166,22,103,20,41,83,104,146,167,43,169,19,145,46,88,151,172,16,37,100,142,8,44,71,89,116,152,170,179,118,34,5,11,23,29,32,47,50,65,68,74,86,110,113,128,131,137,149,155,158,173,176]
def idsR182 : List ℕ := [184,2,23,58,79,86,170,100,107,128,163,121,65,142,149,16,44,37,17,92,94,95,187,8,101,176,178,179,10,11,5,185,4,188,97,1,20,173,137,29,164,110,83,64,127,67,130,68,131,62,125,71,134,59,122,74,146,47,155,38,34,160,32,158,55,82,109,136,31,85,139,166,113,167,26,53,80,50,104,89,116,143,22,43,106,148,169,25,46,88,151,172,152,41,124,13,76,118,181,19,73,145,40,103,157,52,115,61]
theorem row182 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 522)=formalLeading spec182 x y z w 1 v := by
  have hm : mergeFuel 1000 (samplePoly idsL182 left182 1 (0,0,0,0,0,0,0))
      (samplePoly idsR182 right182 (-1) (-2,0,0,0,0,0,0))=inputs 522 := by
    dsimp only [samplePoly,idsL182,idsR182,left182,right182]
    decide +kernel
  rw [← hm,eval_mergeFuel,
    eval_samplePoly (q:=189) x y z w a b c v idsL182 left182 1 (0,0,0,0,0,0,0) (by decide +kernel) (by decide +kernel),
    eval_samplePoly (q:=189) x y z w a b c v idsR182 right182 (-1) (-2,0,0,0,0,0,0) (by decide +kernel) (by decide +kernel)]
  simp [formalLeading,spec182,monomial,sub_eq_add_neg]

def idsL183 : List ℕ := [95,4,74,88,32,11,109,179,158,172,116,25,137,53,67,130,46,151,176,92,185,8,94,5,187,97,1,2,188,64,127,65,128,62,125,68,131,59,122,50,113,55,82,136,163,29,83,110,164,26,80,107,134,41,149,86,167,23,104,22,43,85,106,148,169,44,170,20,146,47,89,152,173,17,38,101,143,10,19,37,73,100,118,145,181,155,71,13,16,31,34,40,52,58,61,76,79,103,115,121,124,139,142,157,160,166,178,184]
def idsR183 : List ℕ := [173,187,19,82,26,47,89,131,166,5,103,124,61,110,145,40,68,152,94,95,13,88,10,11,4,97,172,178,179,1,2,181,92,184,188,185,16,169,52,25,160,106,79,62,125,59,122,64,127,58,121,67,130,55,118,115,142,43,151,34,29,155,31,157,53,80,107,134,23,50,104,158,109,136,163,22,76,46,73,100,85,139,20,41,83,146,167,17,38,101,143,164,148,37,65,8,71,113,176,44,116,170,32,86,149,74,137,128]
theorem row183 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 523)=formalLeading spec183 x y z w 1 v := by
  have hm : mergeFuel 1000 (samplePoly idsL183 left183 1 (0,0,0,0,0,0,0))
      (samplePoly idsR183 right183 (-1) (-2,0,0,0,0,0,0))=inputs 523 := by
    dsimp only [samplePoly,idsL183,idsR183,left183,right183]
    decide +kernel
  rw [← hm,eval_mergeFuel,
    eval_samplePoly (q:=189) x y z w a b c v idsL183 left183 1 (0,0,0,0,0,0,0) (by decide +kernel) (by decide +kernel),
    eval_samplePoly (q:=189) x y z w a b c v idsR183 right183 (-1) (-2,0,0,0,0,0,0) (by decide +kernel) (by decide +kernel)]
  simp [formalLeading,spec183,monomial,sub_eq_add_neg]

end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceCombinedPartsV1 -/
section
/-! One complete certificate family; numbered development parts merged. -/
@[expose] public noncomputable section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
compact_certificate def left0 : ℕ → ℕ
  | 0 => 88
  | _ => 0
compact_certificate def right0 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec0 : Spec := ⟨16,270,1,1,-2700,left0,right0,-2,-3,-2,0⟩
compact_certificate theorem valid0 : Valid point spec0 := by
  dsimp only [Valid,spec0]
  decide +kernel
compact_certificate theorem row0 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 16)=formalLeading spec0 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec0,sampleEval,residues,left0,right0] <;> ring
compact_certificate def left1 : ℕ → ℕ
  | 0 => 89
  | _ => 0
compact_certificate def right1 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec1 : Spec := ⟨17,270,1,-1,2700,left1,right1,-2,-3,-2,0⟩
compact_certificate theorem valid1 : Valid point spec1 := by
  dsimp only [Valid,spec1]
  decide +kernel
compact_certificate theorem row1 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 17)=formalLeading spec1 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec1,sampleEval,residues,left1,right1] <;> ring
compact_certificate def left2 : ℕ → ℕ
  | 0 => 321
  | _ => 0
compact_certificate def right2 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec2 : Spec := ⟨27,378,1,1,-5292,left2,right2,-2,-3,0,-2⟩
compact_certificate theorem valid2 : Valid point spec2 := by
  dsimp only [Valid,spec2]
  decide +kernel
compact_certificate theorem row2 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 27)=formalLeading spec2 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec2,sampleEval,residues,left2,right2] <;> ring
compact_certificate def left3 : ℕ → ℕ
  | 0 => 322
  | _ => 0
compact_certificate def right3 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec3 : Spec := ⟨28,378,1,-1,5292,left3,right3,-2,-3,0,-2⟩
compact_certificate theorem valid3 : Valid point spec3 := by
  dsimp only [Valid,spec3]
  decide +kernel
compact_certificate theorem row3 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 28)=formalLeading spec3 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec3,sampleEval,residues,left3,right3] <;> ring
compact_certificate def left4 : ℕ → ℕ
  | 0 => 323
  | _ => 0
compact_certificate def right4 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec4 : Spec := ⟨29,378,1,2,-2646,left4,right4,0,-3,0,-2⟩
compact_certificate theorem valid4 : Valid point spec4 := by
  dsimp only [Valid,spec4]
  decide +kernel
compact_certificate theorem row4 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 29)=formalLeading spec4 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec4,sampleEval,residues,left4,right4] <;> ring
compact_certificate def left5 : ℕ → ℕ
  | 0 => 324
  | _ => 0
compact_certificate def right5 : ℕ → ℕ
  | 0 => 2
  | _ => 0
compact_certificate def spec5 : Spec := ⟨30,378,1,-2,2646,left5,right5,0,-3,0,-2⟩
compact_certificate theorem valid5 : Valid point spec5 := by
  dsimp only [Valid,spec5]
  decide +kernel
compact_certificate theorem row5 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 30)=formalLeading spec5 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec5,sampleEval,residues,left5,right5] <;> ring
compact_certificate def left6 : ℕ → ℕ
  | 0 => 327
  | _ => 0
compact_certificate def right6 : ℕ → ℕ
  | 0 => 3
  | _ => 0
compact_certificate def spec6 : Spec := ⟨31,378,1,-4,1323,left6,right6,2,-3,0,-2⟩
compact_certificate theorem valid6 : Valid point spec6 := by
  dsimp only [Valid,spec6]
  decide +kernel
compact_certificate theorem row6 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 31)=formalLeading spec6 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec6,sampleEval,residues,left6,right6] <;> ring
compact_certificate def left7 : ℕ → ℕ
  | 0 => 84
  | _ => 0
compact_certificate def right7 : ℕ → ℕ
  | 0 => 37
  | _ => 0
compact_certificate def spec7 : Spec := ⟨81,270,1,3,-900,left7,right7,-2,-1,-2,0⟩
compact_certificate theorem valid7 : Valid point spec7 := by
  dsimp only [Valid,spec7]
  decide +kernel
compact_certificate theorem row7 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 81)=formalLeading spec7 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec7,sampleEval,residues,left7,right7] <;> ring
compact_certificate def left8 : ℕ → ℕ
  | 0 => 86
  | _ => 0
compact_certificate def right8 : ℕ → ℕ
  | 0 => 50
  | _ => 0
compact_certificate def spec8 : Spec := ⟨82,270,1,-3,900,left8,right8,-2,-1,-2,0⟩
compact_certificate theorem valid8 : Valid point spec8 := by
  dsimp only [Valid,spec8]
  decide +kernel
compact_certificate theorem row8 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 82)=formalLeading spec8 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec8,sampleEval,residues,left8,right8] <;> ring
compact_certificate def left9 : ℕ → ℕ
  | 0 => 68
  | _ => 0
compact_certificate def right9 : ℕ → ℕ
  | 0 => 20
  | _ => 0
compact_certificate def spec9 : Spec := ⟨83,270,1,12,-225,left9,right9,2,-1,-2,0⟩
compact_certificate theorem valid9 : Valid point spec9 := by
  dsimp only [Valid,spec9]
  decide +kernel
compact_certificate theorem row9 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 83)=formalLeading spec9 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec9,sampleEval,residues,left9,right9] <;> ring
compact_certificate def left10 : ℕ → ℕ
  | 0 => 76
  | _ => 0
compact_certificate def right10 : ℕ → ℕ
  | 0 => 55
  | _ => 0
compact_certificate def spec10 : Spec := ⟨84,270,1,-12,225,left10,right10,2,-1,-2,0⟩
compact_certificate theorem valid10 : Valid point spec10 := by
  dsimp only [Valid,spec10]
  decide +kernel
compact_certificate theorem row10 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 84)=formalLeading spec10 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec10,sampleEval,residues,left10,right10] <;> ring
compact_certificate def left11 : ℕ → ℕ
  | 0 => 15
  | _ => 0
compact_certificate def right11 : ℕ → ℕ
  | 0 => 90
  | _ => 0
compact_certificate def spec11 : Spec := ⟨85,270,1,25,-108,left11,right11,-2,-3,2,0⟩
compact_certificate theorem valid11 : Valid point spec11 := by
  dsimp only [Valid,spec11]
  decide +kernel
compact_certificate theorem row11 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 85)=formalLeading spec11 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec11,sampleEval,residues,left11,right11] <;> ring

compact_certificate def left12 : ℕ → ℕ
  | 0 => 57
  | _ => 0
compact_certificate def right12 : ℕ → ℕ
  | 0 => 91
  | _ => 0
compact_certificate def spec12 : Spec := ⟨86,270,1,-25,108,left12,right12,-2,-3,2,0⟩
compact_certificate theorem valid12 : Valid point spec12 := by
  dsimp only [Valid,spec12]
  decide +kernel
compact_certificate theorem row12 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 86)=formalLeading spec12 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec12,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left12,right12] <;> ring
compact_certificate def left13 : ℕ → ℕ
  | 0 => 92
  | _ => 0
compact_certificate def right13 : ℕ → ℕ
  | 0 => 46
  | _ => 0
compact_certificate def spec13 : Spec := ⟨87,270,1,27,-100,left13,right13,-2,3,-2,0⟩
compact_certificate theorem valid13 : Valid point spec13 := by
  dsimp only [Valid,spec13]
  decide +kernel
compact_certificate theorem row13 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 87)=formalLeading spec13 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec13,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left13,right13] <;> ring
compact_certificate def left14 : ℕ → ℕ
  | 0 => 93
  | _ => 0
compact_certificate def right14 : ℕ → ℕ
  | 0 => 80
  | _ => 0
compact_certificate def spec14 : Spec := ⟨88,270,1,-27,100,left14,right14,-2,3,-2,0⟩
compact_certificate theorem valid14 : Valid point spec14 := by
  dsimp only [Valid,spec14]
  decide +kernel
compact_certificate theorem row14 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 88)=formalLeading spec14 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec14,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left14,right14] <;> ring
compact_certificate def left15 : ℕ → ℕ
  | 0 => 94
  | _ => 0
compact_certificate def right15 : ℕ → ℕ
  | 0 => 95
  | _ => 0
compact_certificate def spec15 : Spec := ⟨89,270,1,36,-75,left15,right15,2,1,-2,0⟩
compact_certificate theorem valid15 : Valid point spec15 := by
  dsimp only [Valid,spec15]
  decide +kernel
compact_certificate theorem row15 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 89)=formalLeading spec15 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec15,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left15,right15] <;> ring
compact_certificate def left16 : ℕ → ℕ
  | 0 => 96
  | _ => 0
compact_certificate def right16 : ℕ → ℕ
  | 0 => 97
  | _ => 0
compact_certificate def spec16 : Spec := ⟨90,270,1,-36,75,left16,right16,2,1,-2,0⟩
compact_certificate theorem valid16 : Valid point spec16 := by
  dsimp only [Valid,spec16]
  decide +kernel
compact_certificate theorem row16 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 90)=formalLeading spec16 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec16,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left16,right16] <;> ring
compact_certificate def left17 : ℕ → ℕ
  | 0 => 98
  | _ => 0
compact_certificate def right17 : ℕ → ℕ
  | 0 => 99
  | _ => 0
compact_certificate def spec17 : Spec := ⟨91,270,1,50,-54,left17,right17,0,-3,2,0⟩
compact_certificate theorem valid17 : Valid point spec17 := by
  dsimp only [Valid,spec17]
  decide +kernel
compact_certificate theorem row17 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 91)=formalLeading spec17 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec17,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left17,right17] <;> ring
compact_certificate def left18 : ℕ → ℕ
  | 0 => 100
  | _ => 0
compact_certificate def right18 : ℕ → ℕ
  | 0 => 101
  | _ => 0
compact_certificate def spec18 : Spec := ⟨92,270,1,-50,54,left18,right18,0,-3,2,0⟩
compact_certificate theorem valid18 : Valid point spec18 := by
  dsimp only [Valid,spec18]
  decide +kernel
compact_certificate theorem row18 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 92)=formalLeading spec18 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec18,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left18,right18] <;> ring
compact_certificate def left19 : ℕ → ℕ
  | 1 => 102
  | 2 => 103
  | _ => 0
compact_certificate def right19 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec19 : Spec := ⟨94,270,3,1,-2700,left19,right19,-2,-3,-2,0⟩
compact_certificate theorem valid19 : Valid point spec19 := by
  dsimp only [Valid,spec19]
  decide +kernel
compact_certificate theorem row19 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 94)=formalLeading spec19 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec19,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left19,right19] <;> ring
compact_certificate def left20 : ℕ → ℕ
  | 1 => 104
  | 2 => 105
  | _ => 0
compact_certificate def right20 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec20 : Spec := ⟨95,270,3,-1,2700,left20,right20,-2,-3,-2,0⟩
compact_certificate theorem valid20 : Valid point spec20 := by
  dsimp only [Valid,spec20]
  decide +kernel
compact_certificate theorem row20 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 95)=formalLeading spec20 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec20,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left20,right20] <;> ring
compact_certificate def left21 : ℕ → ℕ
  | 1 => 106
  | 2 => 107
  | _ => 0
compact_certificate def right21 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec21 : Spec := ⟨96,270,3,2,-1350,left21,right21,0,-3,-2,0⟩
compact_certificate theorem valid21 : Valid point spec21 := by
  dsimp only [Valid,spec21]
  decide +kernel
compact_certificate theorem row21 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 96)=formalLeading spec21 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec21,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left21,right21] <;> ring
compact_certificate def left22 : ℕ → ℕ
  | 1 => 108
  | 2 => 109
  | _ => 0
compact_certificate def right22 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec22 : Spec := ⟨97,270,3,-2,1350,left22,right22,0,-3,-2,0⟩
compact_certificate theorem valid22 : Valid point spec22 := by
  dsimp only [Valid,spec22]
  decide +kernel
compact_certificate theorem row22 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 97)=formalLeading spec22 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec22,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left22,right22] <;> ring
compact_certificate def left23 : ℕ → ℕ
  | 1 => 118
  | 2 => 119
  | _ => 0
compact_certificate def right23 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec23 : Spec := ⟨98,270,3,5,-540,left23,right23,-2,-3,0,0⟩
compact_certificate theorem valid23 : Valid point spec23 := by
  dsimp only [Valid,spec23]
  decide +kernel
compact_certificate theorem row23 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 98)=formalLeading spec23 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec23,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left23,right23] <;> ring

compact_certificate def left24 : ℕ → ℕ
  | 1 => 120
  | 2 => 121
  | _ => 0
compact_certificate def right24 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec24 : Spec := ⟨99,270,3,-5,540,left24,right24,-2,-3,0,0⟩
compact_certificate theorem valid24 : Valid point spec24 := by
  dsimp only [Valid,spec24]
  decide +kernel
compact_certificate theorem row24 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 99)=formalLeading spec24 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec24,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left24,right24] <;> ring
compact_certificate def left25 : ℕ → ℕ
  | 1 => 80
  | 2 => 26
  | _ => 0
compact_certificate def right25 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec25 : Spec := ⟨100,270,3,10,-270,left25,right25,0,-3,0,0⟩
compact_certificate theorem valid25 : Valid point spec25 := by
  dsimp only [Valid,spec25]
  decide +kernel
compact_certificate theorem row25 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 100)=formalLeading spec25 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec25,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left25,right25] <;> ring
compact_certificate def left26 : ℕ → ℕ
  | 1 => 8
  | 2 => 46
  | _ => 0
compact_certificate def right26 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec26 : Spec := ⟨101,270,3,-10,270,left26,right26,0,-3,0,0⟩
compact_certificate theorem valid26 : Valid point spec26 := by
  dsimp only [Valid,spec26]
  decide +kernel
compact_certificate theorem row26 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 101)=formalLeading spec26 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec26,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left26,right26] <;> ring
compact_certificate def left27 : ℕ → ℕ
  | 1 => 16
  | 2 => 69
  | _ => 0
compact_certificate def right27 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec27 : Spec := ⟨102,270,3,30,-90,left27,right27,0,-1,0,0⟩
compact_certificate theorem valid27 : Valid point spec27 := by
  dsimp only [Valid,spec27]
  decide +kernel
compact_certificate theorem row27 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 102)=formalLeading spec27 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec27,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left27,right27] <;> ring
compact_certificate def left28 : ℕ → ℕ
  | 1 => 75
  | 2 => 33
  | _ => 0
compact_certificate def right28 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec28 : Spec := ⟨104,270,3,-30,90,left28,right28,0,-1,0,0⟩
compact_certificate theorem valid28 : Valid point spec28 := by
  dsimp only [Valid,spec28]
  decide +kernel
compact_certificate theorem row28 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 104)=formalLeading spec28 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec28,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left28,right28] <;> ring
compact_certificate def left29 : ℕ → ℕ
  | 1 => 12
  | 2 => 95
  | _ => 0
compact_certificate def right29 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec29 : Spec := ⟨106,270,3,15,-180,left29,right29,-2,-1,0,0⟩
compact_certificate theorem valid29 : Valid point spec29 := by
  dsimp only [Valid,spec29]
  decide +kernel
compact_certificate theorem row29 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 106)=formalLeading spec29 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec29,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left29,right29] <;> ring
compact_certificate def left30 : ℕ → ℕ
  | 1 => 19
  | 2 => 99
  | _ => 0
compact_certificate def right30 : ℕ → ℕ
  | 1 => 34
  | 2 => 12
  | _ => 0
compact_certificate def spec30 : Spec := ⟨107,270,3,36,-75,left30,right30,2,1,-2,0⟩
compact_certificate theorem valid30 : Valid point spec30 := by
  dsimp only [Valid,spec30]
  decide +kernel
compact_certificate theorem row30 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 107)=formalLeading spec30 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec30,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left30,right30] <;> ring
compact_certificate def left31 : ℕ → ℕ
  | 1 => 31
  | 2 => 39
  | _ => 0
compact_certificate def right31 : ℕ → ℕ
  | 1 => 94
  | 2 => 19
  | _ => 0
compact_certificate def spec31 : Spec := ⟨108,270,3,50,-54,left31,right31,0,-3,2,0⟩
compact_certificate theorem valid31 : Valid point spec31 := by
  dsimp only [Valid,spec31]
  decide +kernel
compact_certificate theorem row31 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 108)=formalLeading spec31 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec31,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left31,right31] <;> ring
compact_certificate def left32 : ℕ → ℕ
  | 1 => 18
  | 2 => 24
  | _ => 0
compact_certificate def right32 : ℕ → ℕ
  | 1 => 56
  | 2 => 96
  | _ => 0
compact_certificate def spec32 : Spec := ⟨110,270,3,-50,54,left32,right32,0,-3,2,0⟩
compact_certificate theorem valid32 : Valid point spec32 := by
  dsimp only [Valid,spec32]
  decide +kernel
compact_certificate theorem row32 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 110)=formalLeading spec32 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec32,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left32,right32] <;> ring
compact_certificate def left33 : ℕ → ℕ
  | 1 => 97
  | 2 => 60
  | _ => 0
compact_certificate def right33 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec33 : Spec := ⟨111,270,3,-15,180,left33,right33,-2,-1,0,0⟩
compact_certificate theorem valid33 : Valid point spec33 := by
  dsimp only [Valid,spec33]
  decide +kernel
compact_certificate theorem row33 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 111)=formalLeading spec33 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec33,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left33,right33] <;> ring
compact_certificate def left34 : ℕ → ℕ
  | 1 => 101
  | 2 => 56
  | _ => 0
compact_certificate def right34 : ℕ → ℕ
  | 1 => 60
  | 2 => 42
  | _ => 0
compact_certificate def spec34 : Spec := ⟨112,270,3,-36,75,left34,right34,2,1,-2,0⟩
compact_certificate theorem valid34 : Valid point spec34 := by
  dsimp only [Valid,spec34]
  decide +kernel
compact_certificate theorem row34 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 112)=formalLeading spec34 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec34,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left34,right34] <;> ring
compact_certificate def left35 : ℕ → ℕ
  | 1 => 135
  | 2 => 90
  | _ => 0
compact_certificate def right35 : ℕ → ℕ
  | 1 => 28
  | 2 => 75
  | _ => 0
compact_certificate def spec35 : Spec := ⟨114,270,3,-18,150,left35,right35,0,1,-2,0⟩
compact_certificate theorem valid35 : Valid point spec35 := by
  dsimp only [Valid,spec35]
  decide +kernel
compact_certificate theorem row35 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 114)=formalLeading spec35 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec35,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left35,right35] <;> ring

compact_certificate def left36 : ℕ → ℕ
  | 1 => 14
  | 2 => 53
  | _ => 0
compact_certificate def right36 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec36 : Spec := ⟨115,270,3,20,-135,left36,right36,2,-3,0,0⟩
compact_certificate theorem valid36 : Valid point spec36 := by
  dsimp only [Valid,spec36]
  decide +kernel
compact_certificate theorem row36 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 115)=formalLeading spec36 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec36,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left36,right36] <;> ring
compact_certificate def left37 : ℕ → ℕ
  | 1 => 91
  | 2 => 134
  | _ => 0
compact_certificate def right37 : ℕ → ℕ
  | 1 => 69
  | 2 => 6
  | _ => 0
compact_certificate def spec37 : Spec := ⟨117,270,3,18,-150,left37,right37,0,1,-2,0⟩
compact_certificate theorem valid37 : Valid point spec37 := by
  dsimp only [Valid,spec37]
  decide +kernel
compact_certificate theorem row37 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 117)=formalLeading spec37 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec37,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left37,right37] <;> ring
compact_certificate def left38 : ℕ → ℕ
  | 1 => 22
  | 2 => 58
  | _ => 0
compact_certificate def right38 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec38 : Spec := ⟨118,270,3,-20,135,left38,right38,2,-3,0,0⟩
compact_certificate theorem valid38 : Valid point spec38 := by
  dsimp only [Valid,spec38]
  decide +kernel
compact_certificate theorem row38 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 118)=formalLeading spec38 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec38,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left38,right38] <;> ring
compact_certificate def left39 : ℕ → ℕ
  | 1 => 140
  | 2 => 141
  | _ => 0
compact_certificate def right39 : ℕ → ℕ
  | 1 => 26
  | 2 => 32
  | _ => 0
compact_certificate def spec39 : Spec := ⟨121,270,3,-27,100,left39,right39,-2,3,-2,0⟩
compact_certificate theorem valid39 : Valid point spec39 := by
  dsimp only [Valid,spec39]
  decide +kernel
compact_certificate theorem row39 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 121)=formalLeading spec39 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec39,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left39,right39] <;> ring
compact_certificate def left40 : ℕ → ℕ
  | 1 => 137
  | 2 => 35
  | _ => 0
compact_certificate def right40 : ℕ → ℕ
  | 1 => 134
  | 2 => 38
  | _ => 0
compact_certificate def spec40 : Spec := ⟨124,270,3,-25,108,left40,right40,-2,-3,2,0⟩
compact_certificate theorem valid40 : Valid point spec40 := by
  dsimp only [Valid,spec40]
  decide +kernel
compact_certificate theorem row40 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 124)=formalLeading spec40 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec40,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left40,right40] <;> ring
compact_certificate def left41 : ℕ → ℕ
  | 1 => 73
  | 2 => 137
  | 4 => 17
  | 5 => 35
  | 7 => 149
  | 8 => 57
  | _ => 0
compact_certificate def right41 : ℕ → ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
compact_certificate def spec41 : Spec := ⟨126,270,9,5,-180,left41,right41,-2,-2,0,0⟩
compact_certificate theorem valid41 : Valid point spec41 := by
  dsimp only [Valid,spec41]
  decide +kernel
compact_certificate theorem row41 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 126)=formalLeading spec41 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec41,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left41,right41] <;> ring
compact_certificate def left42 : ℕ → ℕ
  | 1 => 128
  | 2 => 129
  | _ => 0
compact_certificate def right42 : ℕ → ℕ
  | 1 => 16
  | 2 => 69
  | _ => 0
compact_certificate def spec42 : Spec := ⟨128,270,3,-9,300,left42,right42,-2,1,-2,0⟩
compact_certificate theorem valid42 : Valid point spec42 := by
  dsimp only [Valid,spec42]
  decide +kernel
compact_certificate theorem row42 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 128)=formalLeading spec42 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec42,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left42,right42] <;> ring
compact_certificate def left43 : ℕ → ℕ
  | 1 => 126
  | 2 => 127
  | _ => 0
compact_certificate def right43 : ℕ → ℕ
  | 1 => 75
  | 2 => 33
  | _ => 0
compact_certificate def spec43 : Spec := ⟨130,270,3,9,-300,left43,right43,-2,1,-2,0⟩
compact_certificate theorem valid43 : Valid point spec43 := by
  dsimp only [Valid,spec43]
  decide +kernel
compact_certificate theorem row43 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 130)=formalLeading spec43 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec43,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left43,right43] <;> ring
compact_certificate def left44 : ℕ → ℕ
  | 1 => 66
  | 2 => 136
  | _ => 0
compact_certificate def right44 : ℕ → ℕ
  | 1 => 64
  | 2 => 135
  | _ => 0
compact_certificate def spec44 : Spec := ⟨135,270,3,25,-108,left44,right44,-2,-3,2,0⟩
compact_certificate theorem valid44 : Valid point spec44 := by
  dsimp only [Valid,spec44]
  decide +kernel
compact_certificate theorem row44 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 135)=formalLeading spec44 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec44,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left44,right44] <;> ring
compact_certificate def left45 : ℕ → ℕ
  | 1 => 15
  | 2 => 142
  | 4 => 66
  | 5 => 44
  | 7 => 136
  | 8 => 71
  | _ => 0
compact_certificate def right45 : ℕ → ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
compact_certificate def spec45 : Spec := ⟨136,270,9,-5,180,left45,right45,-2,-2,0,0⟩
compact_certificate theorem valid45 : Valid point spec45 := by
  dsimp only [Valid,spec45]
  decide +kernel
compact_certificate theorem row45 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 136)=formalLeading spec45 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec45,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left45,right45] <;> ring
compact_certificate def left46 : ℕ → ℕ
  | 1 => 138
  | 2 => 139
  | _ => 0
compact_certificate def right46 : ℕ → ℕ
  | 1 => 1
  | 2 => 8
  | _ => 0
compact_certificate def spec46 : Spec := ⟨139,270,3,27,-100,left46,right46,-2,3,-2,0⟩
compact_certificate theorem valid46 : Valid point spec46 := by
  dsimp only [Valid,spec46]
  decide +kernel
compact_certificate theorem row46 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 139)=formalLeading spec46 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec46,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left46,right46] <;> ring
compact_certificate def left47 : ℕ → ℕ
  | 0 => 325
  | _ => 0
compact_certificate def right47 : ℕ → ℕ
  | 0 => 50
  | _ => 0
compact_certificate def spec47 : Spec := ⟨183,378,1,3,-1764,left47,right47,-2,-1,0,-2⟩
compact_certificate theorem valid47 : Valid point spec47 := by
  dsimp only [Valid,spec47]
  decide +kernel
compact_certificate theorem row47 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 183)=formalLeading spec47 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec47,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left47,right47] <;> ring

compact_certificate def left48 : ℕ → ℕ
  | 0 => 326
  | _ => 0
compact_certificate def right48 : ℕ → ℕ
  | 0 => 37
  | _ => 0
compact_certificate def spec48 : Spec := ⟨184,378,1,-3,1764,left48,right48,-2,-1,0,-2⟩
compact_certificate theorem valid48 : Valid point spec48 := by
  dsimp only [Valid,spec48]
  decide +kernel
compact_certificate theorem row48 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 184)=formalLeading spec48 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec48,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left48,right48] <;> ring
compact_certificate def left49 : ℕ → ℕ
  | 0 => 328
  | _ => 0
compact_certificate def right49 : ℕ → ℕ
  | 0 => 60
  | _ => 0
compact_certificate def spec49 : Spec := ⟨185,378,1,36,-147,left49,right49,2,1,0,-2⟩
compact_certificate theorem valid49 : Valid point spec49 := by
  dsimp only [Valid,spec49]
  decide +kernel
compact_certificate theorem row49 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 185)=formalLeading spec49 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec49,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left49,right49] <;> ring
compact_certificate def left50 : ℕ → ℕ
  | 0 => 329
  | _ => 0
compact_certificate def right50 : ℕ → ℕ
  | 0 => 12
  | _ => 0
compact_certificate def spec50 : Spec := ⟨186,378,1,-36,147,left50,right50,2,1,0,-2⟩
compact_certificate theorem valid50 : Valid point spec50 := by
  dsimp only [Valid,spec50]
  decide +kernel
compact_certificate theorem row50 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 186)=formalLeading spec50 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec50,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left50,right50] <;> ring
compact_certificate def left51 : ℕ → ℕ
  | 0 => 73
  | _ => 0
compact_certificate def right51 : ℕ → ℕ
  | 0 => 330
  | _ => 0
compact_certificate def spec51 : Spec := ⟨187,378,1,49,-108,left51,right51,-2,-3,0,2⟩
compact_certificate theorem valid51 : Valid point spec51 := by
  dsimp only [Valid,spec51]
  decide +kernel
compact_certificate theorem row51 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 187)=formalLeading spec51 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec51,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left51,right51] <;> ring
compact_certificate def left52 : ℕ → ℕ
  | 0 => 71
  | _ => 0
compact_certificate def right52 : ℕ → ℕ
  | 0 => 331
  | _ => 0
compact_certificate def spec52 : Spec := ⟨188,378,1,-49,108,left52,right52,-2,-3,0,2⟩
compact_certificate theorem valid52 : Valid point spec52 := by
  dsimp only [Valid,spec52]
  decide +kernel
compact_certificate theorem row52 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 188)=formalLeading spec52 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec52,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left52,right52] <;> ring
compact_certificate def left53 : ℕ → ℕ
  | 0 => 332
  | _ => 0
compact_certificate def right53 : ℕ → ℕ
  | 0 => 53
  | _ => 0
compact_certificate def spec53 : Spec := ⟨189,378,1,54,-98,left53,right53,0,3,0,-2⟩
compact_certificate theorem valid53 : Valid point spec53 := by
  dsimp only [Valid,spec53]
  decide +kernel
compact_certificate theorem row53 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 189)=formalLeading spec53 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec53,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left53,right53] <;> ring
compact_certificate def left54 : ℕ → ℕ
  | 0 => 333
  | _ => 0
compact_certificate def right54 : ℕ → ℕ
  | 0 => 22
  | _ => 0
compact_certificate def spec54 : Spec := ⟨190,378,1,-54,98,left54,right54,0,3,0,-2⟩
compact_certificate theorem valid54 : Valid point spec54 := by
  dsimp only [Valid,spec54]
  decide +kernel
compact_certificate theorem row54 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 190)=formalLeading spec54 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec54,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left54,right54] <;> ring
compact_certificate def left55 : ℕ → ℕ
  | 1 => 334
  | _ => 0
compact_certificate def right55 : ℕ → ℕ
  | 1 => 80
  | _ => 0
compact_certificate def spec55 : Spec := ⟨191,378,2,27,-49,left55,right55,0,3,0,-2⟩
compact_certificate theorem valid55 : Valid point spec55 := by
  dsimp only [Valid,spec55]
  decide +kernel
compact_certificate theorem row55 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 191)=formalLeading spec55 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec55,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left55,right55] <;> ring
compact_certificate def left56 : ℕ → ℕ
  | 1 => 335
  | _ => 0
compact_certificate def right56 : ℕ → ℕ
  | 1 => 46
  | _ => 0
compact_certificate def spec56 : Spec := ⟨192,378,2,-27,49,left56,right56,0,3,0,-2⟩
compact_certificate theorem valid56 : Valid point spec56 := by
  dsimp only [Valid,spec56]
  decide +kernel
compact_certificate theorem row56 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 192)=formalLeading spec56 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec56,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left56,right56] <;> ring
compact_certificate def left57 : ℕ → ℕ
  | 1 => 364
  | 2 => 330
  | _ => 0
compact_certificate def right57 : ℕ → ℕ
  | 1 => 33
  | 2 => 28
  | _ => 0
compact_certificate def spec57 : Spec := ⟨193,378,3,18,-294,left57,right57,0,1,0,-2⟩
compact_certificate theorem valid57 : Valid point spec57 := by
  dsimp only [Valid,spec57]
  decide +kernel
compact_certificate theorem row57 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 193)=formalLeading spec57 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec57,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left57,right57] <;> ring
compact_certificate def left58 : ℕ → ℕ
  | 1 => 331
  | 2 => 365
  | _ => 0
compact_certificate def right58 : ℕ → ℕ
  | 1 => 6
  | 2 => 16
  | _ => 0
compact_certificate def spec58 : Spec := ⟨194,378,3,-18,294,left58,right58,0,1,0,-2⟩
compact_certificate theorem valid58 : Valid point spec58 := by
  dsimp only [Valid,spec58]
  decide +kernel
compact_certificate theorem row58 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 194)=formalLeading spec58 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec58,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left58,right58] <;> ring
compact_certificate def left59 : ℕ → ℕ
  | 1 => 335
  | 2 => 370
  | _ => 0
compact_certificate def right59 : ℕ → ℕ
  | 1 => 42
  | 2 => 97
  | _ => 0
compact_certificate def spec59 : Spec := ⟨195,378,3,36,-147,left59,right59,2,1,0,-2⟩
compact_certificate theorem valid59 : Valid point spec59 := by
  dsimp only [Valid,spec59]
  decide +kernel
compact_certificate theorem row59 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 195)=formalLeading spec59 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec59,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left59,right59] <;> ring

compact_certificate def left60 : ℕ → ℕ
  | 1 => 371
  | 2 => 334
  | _ => 0
compact_certificate def right60 : ℕ → ℕ
  | 1 => 95
  | 2 => 34
  | _ => 0
compact_certificate def spec60 : Spec := ⟨196,378,3,-36,147,left60,right60,2,1,0,-2⟩
compact_certificate theorem valid60 : Valid point spec60 := by
  dsimp only [Valid,spec60]
  decide +kernel
compact_certificate theorem row60 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 196)=formalLeading spec60 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec60,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left60,right60] <;> ring
compact_certificate def left61 : ℕ → ℕ
  | 1 => 279
  | 2 => 372
  | _ => 0
compact_certificate def right61 : ℕ → ℕ
  | 1 => 72
  | 2 => 14
  | _ => 0
compact_certificate def spec61 : Spec := ⟨197,378,3,54,-98,left61,right61,0,3,0,-2⟩
compact_certificate theorem valid61 : Valid point spec61 := by
  dsimp only [Valid,spec61]
  decide +kernel
compact_certificate theorem row61 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 197)=formalLeading spec61 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec61,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left61,right61] <;> ring
compact_certificate def left62 : ℕ → ℕ
  | 1 => 373
  | 2 => 293
  | _ => 0
compact_certificate def right62 : ℕ → ℕ
  | 1 => 58
  | 2 => 0
  | _ => 0
compact_certificate def spec62 : Spec := ⟨198,378,3,-54,98,left62,right62,0,3,0,-2⟩
compact_certificate theorem valid62 : Valid point spec62 := by
  dsimp only [Valid,spec62]
  decide +kernel
compact_certificate theorem row62 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 198)=formalLeading spec62 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec62,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left62,right62] <;> ring
compact_certificate def left63 : ℕ → ℕ
  | 1 => 368
  | 2 => 369
  | _ => 0
compact_certificate def right63 : ℕ → ℕ
  | 1 => 39
  | 2 => 98
  | _ => 0
compact_certificate def spec63 : Spec := ⟨202,378,3,-27,196,left63,right63,-2,3,0,-2⟩
compact_certificate theorem valid63 : Valid point spec63 := by
  dsimp only [Valid,spec63]
  decide +kernel
compact_certificate theorem row63 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 202)=formalLeading spec63 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec63,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left63,right63] <;> ring
compact_certificate def left64 : ℕ → ℕ
  | 1 => 358
  | 2 => 359
  | _ => 0
compact_certificate def right64 : ℕ → ℕ
  | 1 => 28
  | 2 => 75
  | _ => 0
compact_certificate def spec64 : Spec := ⟨205,378,3,-9,588,left64,right64,-2,1,0,-2⟩
compact_certificate theorem valid64 : Valid point spec64 := by
  dsimp only [Valid,spec64]
  decide +kernel
compact_certificate theorem row64 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 205)=formalLeading spec64 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec64,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left64,right64] <;> ring
compact_certificate def left65 : ℕ → ℕ
  | 1 => 356
  | 2 => 357
  | _ => 0
compact_certificate def right65 : ℕ → ℕ
  | 1 => 69
  | 2 => 6
  | _ => 0
compact_certificate def spec65 : Spec := ⟨207,378,3,9,-588,left65,right65,-2,1,0,-2⟩
compact_certificate theorem valid65 : Valid point spec65 := by
  dsimp only [Valid,spec65]
  decide +kernel
compact_certificate theorem row65 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 207)=formalLeading spec65 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec65,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left65,right65] <;> ring
compact_certificate def left66 : ℕ → ℕ
  | 1 => 366
  | 2 => 367
  | _ => 0
compact_certificate def right66 : ℕ → ℕ
  | 1 => 100
  | 2 => 18
  | _ => 0
compact_certificate def spec66 : Spec := ⟨211,378,3,27,-196,left66,right66,-2,3,0,-2⟩
compact_certificate theorem valid66 : Valid point spec66 := by
  dsimp only [Valid,spec66]
  decide +kernel
compact_certificate theorem row66 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 211)=formalLeading spec66 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec66,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left66,right66] <;> ring
compact_certificate def left67 : ℕ → ℕ
  | 0 => 601
  | _ => 0
compact_certificate def right67 : ℕ → ℕ
  | 0 => 37
  | _ => 0
compact_certificate def spec67 : Spec := ⟨221,1890,1,3,-44100,left67,right67,-2,-1,-2,-2⟩
compact_certificate theorem valid67 : Valid point spec67 := by
  dsimp only [Valid,spec67]
  decide +kernel
compact_certificate theorem row67 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 221)=formalLeading spec67 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec67,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left67,right67] <;> ring
compact_certificate def left68 : ℕ → ℕ
  | 0 => 602
  | _ => 0
compact_certificate def right68 : ℕ → ℕ
  | 0 => 50
  | _ => 0
compact_certificate def spec68 : Spec := ⟨222,1890,1,6,-22050,left68,right68,0,-1,-2,-2⟩
compact_certificate theorem valid68 : Valid point spec68 := by
  dsimp only [Valid,spec68]
  decide +kernel
compact_certificate theorem row68 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 222)=formalLeading spec68 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec68,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left68,right68] <;> ring
compact_certificate def left69 : ℕ → ℕ
  | 0 => 603
  | _ => 0
compact_certificate def right69 : ℕ → ℕ
  | 0 => 20
  | _ => 0
compact_certificate def spec69 : Spec := ⟨223,1890,1,12,-11025,left69,right69,2,-1,-2,-2⟩
compact_certificate theorem valid69 : Valid point spec69 := by
  dsimp only [Valid,spec69]
  decide +kernel
compact_certificate theorem row69 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 223)=formalLeading spec69 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec69,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left69,right69] <;> ring
compact_certificate def left70 : ℕ → ℕ
  | 0 => 172
  | _ => 0
compact_certificate def right70 : ℕ → ℕ
  | 0 => 370
  | _ => 0
compact_certificate def spec70 : Spec := ⟨224,1890,1,294,-450,left70,right70,0,-1,-2,2⟩
compact_certificate theorem valid70 : Valid point spec70 := by
  dsimp only [Valid,spec70]
  decide +kernel
compact_certificate theorem row70 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 224)=formalLeading spec70 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec70,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left70,right70] <;> ring
compact_certificate def left71 : ℕ → ℕ
  | 1 => 172
  | 5 => 169
  | _ => 0
compact_certificate def right71 : ℕ → ℕ
  | 1 => 2
  | 5 => 37
  | _ => 0
compact_certificate def spec71 : Spec := ⟨225,270,6,-3,225,left71,right71,0,-1,-2,0⟩
compact_certificate theorem valid71 : Valid point spec71 := by
  dsimp only [Valid,spec71]
  decide +kernel
compact_certificate theorem row71 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 225)=formalLeading spec71 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec71,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left71,right71] <;> ring

compact_certificate def left72 : ℕ → ℕ
  | 0 => 175
  | _ => 0
compact_certificate def right72 : ℕ → ℕ
  | 0 => 371
  | _ => 0
compact_certificate def spec72 : Spec := ⟨227,1890,1,-294,450,left72,right72,0,-1,-2,2⟩
compact_certificate theorem valid72 : Valid point spec72 := by
  dsimp only [Valid,spec72]
  decide +kernel
compact_certificate theorem row72 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 227)=formalLeading spec72 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec72,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left72,right72] <;> ring
compact_certificate def left73 : ℕ → ℕ
  | 1 => 170
  | 5 => 175
  | _ => 0
compact_certificate def right73 : ℕ → ℕ
  | 1 => 50
  | 5 => 2
  | _ => 0
compact_certificate def spec73 : Spec := ⟨228,270,6,3,-225,left73,right73,0,-1,-2,0⟩
compact_certificate theorem valid73 : Valid point spec73 := by
  dsimp only [Valid,spec73]
  decide +kernel
compact_certificate theorem row73 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 228)=formalLeading spec73 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec73,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left73,right73] <;> ring
compact_certificate def left74 : ℕ → ℕ
  | 0 => 380
  | _ => 0
compact_certificate def right74 : ℕ → ℕ
  | 0 => 139
  | _ => 0
compact_certificate def spec74 : Spec := ⟨230,1890,1,300,-441,left74,right74,2,-1,2,-2⟩
compact_certificate theorem valid74 : Valid point spec74 := by
  dsimp only [Valid,spec74]
  decide +kernel
compact_certificate theorem row74 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 230)=formalLeading spec74 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec74,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left74,right74] <;> ring
compact_certificate def left75 : ℕ → ℕ
  | 1 => 380
  | 5 => 381
  | _ => 0
compact_certificate def right75 : ℕ → ℕ
  | 1 => 50
  | 5 => 2
  | _ => 0
compact_certificate def spec75 : Spec := ⟨231,378,6,-3,441,left75,right75,0,-1,0,-2⟩
compact_certificate theorem valid75 : Valid point spec75 := by
  dsimp only [Valid,spec75]
  decide +kernel
compact_certificate theorem row75 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 231)=formalLeading spec75 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec75,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left75,right75] <;> ring
compact_certificate def left76 : ℕ → ℕ
  | 1 => 171
  | _ => 0
compact_certificate def right76 : ℕ → ℕ
  | 1 => 364
  | _ => 0
compact_certificate def spec76 : Spec := ⟨233,1890,2,147,-225,left76,right76,0,-1,-2,2⟩
compact_certificate theorem valid76 : Valid point spec76 := by
  dsimp only [Valid,spec76]
  decide +kernel
compact_certificate theorem row76 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 233)=formalLeading spec76 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec76,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left76,right76] <;> ring
compact_certificate def left77 : ℕ → ℕ
  | 1 => 170
  | 2 => 130
  | 3 => 171
  | 4 => 69
  | _ => 0
compact_certificate def right77 : ℕ → ℕ
  | 1 => 135
  | 2 => 19
  | 3 => 37
  | 4 => 96
  | _ => 0
compact_certificate def spec77 : Spec := ⟨234,270,5,-6,18,left77,right77,0,-1,0,0⟩
compact_certificate theorem valid77 : Valid point spec77 := by
  dsimp only [Valid,spec77]
  decide +kernel
compact_certificate theorem row77 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 234)=formalLeading spec77 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec77,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left77,right77] <;> ring
compact_certificate def left78 : ℕ → ℕ
  | 1 => 130
  | 2 => 131
  | _ => 0
compact_certificate def right78 : ℕ → ℕ
  | 1 => 3
  | 2 => 55
  | _ => 0
compact_certificate def spec78 : Spec := ⟨235,270,3,12,-225,left78,right78,2,-1,-2,0⟩
compact_certificate theorem valid78 : Valid point spec78 := by
  dsimp only [Valid,spec78]
  decide +kernel
compact_certificate theorem row78 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 235)=formalLeading spec78 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec78,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left78,right78] <;> ring
compact_certificate def left79 : ℕ → ℕ
  | 1 => 94
  | 2 => 174
  | 4 => 19
  | 5 => 171
  | 7 => 99
  | 8 => 59
  | _ => 0
compact_certificate def right79 : ℕ → ℕ
  | 1 => 33
  | 2 => 37
  | 4 => 28
  | 5 => 2
  | 7 => 75
  | 8 => 50
  | _ => 0
compact_certificate def spec79 : Spec := ⟨236,270,9,6,-150,left79,right79,0,0,-2,0⟩
compact_certificate theorem valid79 : Valid point spec79 := by
  dsimp only [Valid,spec79]
  decide +kernel
compact_certificate theorem row79 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 236)=formalLeading spec79 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec79,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left79,right79] <;> ring
compact_certificate def left80 : ℕ → ℕ
  | 1 => 20
  | 2 => 126
  | 3 => 141
  | 4 => 139
  | _ => 0
compact_certificate def right80 : ℕ → ℕ
  | 1 => 174
  | 2 => 16
  | 3 => 125
  | 4 => 175
  | _ => 0
compact_certificate def spec80 : Spec := ⟨237,270,5,-9,12,left80,right80,-2,1,0,0⟩
compact_certificate theorem valid80 : Valid point spec80 := by
  dsimp only [Valid,spec80]
  decide +kernel
compact_certificate theorem row80 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 237)=formalLeading spec80 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec80,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left80,right80] <;> ring
compact_certificate def left81 : ℕ → ℕ
  | 1 => 124
  | 2 => 125
  | _ => 0
compact_certificate def right81 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec81 : Spec := ⟨238,270,3,-6,450,left81,right81,0,-1,-2,0⟩
compact_certificate theorem valid81 : Valid point spec81 := by
  dsimp only [Valid,spec81]
  decide +kernel
compact_certificate theorem row81 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 238)=formalLeading spec81 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec81,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left81,right81] <;> ring
compact_certificate def left82 : ℕ → ℕ
  | 1 => 110
  | 2 => 111
  | _ => 0
compact_certificate def right82 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec82 : Spec := ⟨241,270,3,3,-900,left82,right82,-2,-1,-2,0⟩
compact_certificate theorem valid82 : Valid point spec82 := by
  dsimp only [Valid,spec82]
  decide +kernel
compact_certificate theorem row82 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 241)=formalLeading spec82 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec82,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left82,right82] <;> ring
compact_certificate def left83 : ℕ → ℕ
  | 1 => 112
  | 2 => 113
  | _ => 0
compact_certificate def right83 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec83 : Spec := ⟨242,270,3,-3,900,left83,right83,-2,-1,-2,0⟩
compact_certificate theorem valid83 : Valid point spec83 := by
  dsimp only [Valid,spec83]
  decide +kernel
compact_certificate theorem row83 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 242)=formalLeading spec83 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec83,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left83,right83] <;> ring

compact_certificate def left84 : ℕ → ℕ
  | 1 => 114
  | 2 => 115
  | _ => 0
compact_certificate def right84 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec84 : Spec := ⟨243,270,3,4,-675,left84,right84,2,-3,-2,0⟩
compact_certificate theorem valid84 : Valid point spec84 := by
  dsimp only [Valid,spec84]
  decide +kernel
compact_certificate theorem row84 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 243)=formalLeading spec84 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec84,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left84,right84] <;> ring
compact_certificate def left85 : ℕ → ℕ
  | 1 => 116
  | 2 => 117
  | _ => 0
compact_certificate def right85 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec85 : Spec := ⟨244,270,3,-4,675,left85,right85,2,-3,-2,0⟩
compact_certificate theorem valid85 : Valid point spec85 := by
  dsimp only [Valid,spec85]
  decide +kernel
compact_certificate theorem row85 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 244)=formalLeading spec85 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec85,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left85,right85] <;> ring
compact_certificate def left86 : ℕ → ℕ
  | 1 => 122
  | 2 => 123
  | _ => 0
compact_certificate def right86 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec86 : Spec := ⟨245,270,3,6,-450,left86,right86,0,-1,-2,0⟩
compact_certificate theorem valid86 : Valid point spec86 := by
  dsimp only [Valid,spec86]
  decide +kernel
compact_certificate theorem row86 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 245)=formalLeading spec86 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec86,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left86,right86] <;> ring
compact_certificate def left87 : ℕ → ℕ
  | 1 => 132
  | 2 => 133
  | _ => 0
compact_certificate def right87 : ℕ → ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
compact_certificate def spec87 : Spec := ⟨246,270,3,-12,225,left87,right87,2,-1,-2,0⟩
compact_certificate theorem valid87 : Valid point spec87 := by
  dsimp only [Valid,spec87]
  decide +kernel
compact_certificate theorem row87 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 246)=formalLeading spec87 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec87,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left87,right87] <;> ring
compact_certificate def left88 : ℕ → ℕ
  | 1 => 156
  | 2 => 157
  | 3 => 60
  | 4 => 158
  | _ => 0
compact_certificate def right88 : ℕ → ℕ
  | 1 => 38
  | 2 => 135
  | 3 => 19
  | 4 => 37
  | _ => 0
compact_certificate def spec88 : Spec := ⟨247,270,5,3,-36,left88,right88,-2,-1,0,0⟩
compact_certificate theorem valid88 : Valid point spec88 := by
  dsimp only [Valid,spec88]
  decide +kernel
compact_certificate theorem row88 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 247)=formalLeading spec88 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec88,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left88,right88] <;> ring
compact_certificate def left89 : ℕ → ℕ
  | 1 => 75
  | 2 => 168
  | 3 => 133
  | 4 => 169
  | _ => 0
compact_certificate def right89 : ℕ → ℕ
  | 1 => 94
  | 2 => 50
  | 3 => 56
  | 4 => 134
  | _ => 0
compact_certificate def spec89 : Spec := ⟨248,270,5,6,-18,left89,right89,0,-1,0,0⟩
compact_certificate theorem valid89 : Valid point spec89 := by
  dsimp only [Valid,spec89]
  decide +kernel
compact_certificate theorem row89 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 248)=formalLeading spec89 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec89,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left89,right89] <;> ring
compact_certificate def left90 : ℕ → ℕ
  | 1 => 140
  | 2 => 138
  | 3 => 129
  | 4 => 55
  | _ => 0
compact_certificate def right90 : ℕ → ℕ
  | 1 => 172
  | 2 => 122
  | 3 => 33
  | 4 => 173
  | _ => 0
compact_certificate def spec90 : Spec := ⟨249,270,5,9,-12,left90,right90,-2,1,0,0⟩
compact_certificate theorem valid90 : Valid point spec90 := by
  dsimp only [Valid,spec90]
  decide +kernel
compact_certificate theorem row90 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 249)=formalLeading spec90 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec90,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left90,right90] <;> ring
compact_certificate def left91 : ℕ → ℕ
  | 1 => 176
  | 5 => 177
  | _ => 0
compact_certificate def right91 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
compact_certificate def spec91 : Spec := ⟨250,270,6,1,-675,left91,right91,0,-3,-2,0⟩
compact_certificate theorem valid91 : Valid point spec91 := by
  dsimp only [Valid,spec91]
  decide +kernel
compact_certificate theorem row91 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 250)=formalLeading spec91 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec91,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left91,right91] <;> ring
compact_certificate def left92 : ℕ → ℕ
  | 1 => 178
  | 5 => 179
  | _ => 0
compact_certificate def right92 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
compact_certificate def spec92 : Spec := ⟨251,270,6,-1,675,left92,right92,0,-3,-2,0⟩
compact_certificate theorem valid92 : Valid point spec92 := by
  dsimp only [Valid,spec92]
  decide +kernel
compact_certificate theorem row92 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 251)=formalLeading spec92 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec92,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left92,right92] <;> ring
compact_certificate def left93 : ℕ → ℕ
  | 1 => 202
  | 2 => 140
  | 4 => 203
  | 5 => 141
  | 7 => 161
  | 8 => 93
  | _ => 0
compact_certificate def right93 : ℕ → ℕ
  | 1 => 2
  | 2 => 6
  | 4 => 50
  | 5 => 16
  | 7 => 37
  | 8 => 69
  | _ => 0
compact_certificate def spec93 : Spec := ⟨252,270,9,3,-300,left93,right93,-2,0,-2,0⟩
compact_certificate theorem valid93 : Valid point spec93 := by
  dsimp only [Valid,spec93]
  decide +kernel
compact_certificate theorem row93 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 252)=formalLeading spec93 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec93,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left93,right93] <;> ring
compact_certificate def left94 : ℕ → ℕ
  | 1 => 92
  | 2 => 156
  | 4 => 138
  | 5 => 204
  | 7 => 139
  | 8 => 205
  | _ => 0
compact_certificate def right94 : ℕ → ℕ
  | 1 => 75
  | 2 => 50
  | 4 => 33
  | 5 => 37
  | 7 => 28
  | 8 => 2
  | _ => 0
compact_certificate def spec94 : Spec := ⟨253,270,9,-3,300,left94,right94,-2,0,-2,0⟩
compact_certificate theorem valid94 : Valid point spec94 := by
  dsimp only [Valid,spec94]
  decide +kernel
compact_certificate theorem row94 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 253)=formalLeading spec94 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec94,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left94,right94] <;> ring
compact_certificate def left95 : ℕ → ℕ
  | 1 => 13
  | 2 => 101
  | 4 => 168
  | 5 => 56
  | 7 => 173
  | 8 => 96
  | _ => 0
compact_certificate def right95 : ℕ → ℕ
  | 1 => 37
  | 2 => 69
  | 4 => 2
  | 5 => 6
  | 7 => 50
  | 8 => 16
  | _ => 0
compact_certificate def spec95 : Spec := ⟨254,270,9,-6,150,left95,right95,0,0,-2,0⟩
compact_certificate theorem valid95 : Valid point spec95 := by
  dsimp only [Valid,spec95]
  decide +kernel
compact_certificate theorem row95 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 254)=formalLeading spec95 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec95,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left95,right95] <;> ring

compact_certificate def left96 : ℕ → ℕ
  | 1 => 159
  | 2 => 12
  | 3 => 160
  | 4 => 161
  | _ => 0
compact_certificate def right96 : ℕ → ℕ
  | 1 => 50
  | 2 => 56
  | 3 => 134
  | 4 => 64
  | _ => 0
compact_certificate def spec96 : Spec := ⟨258,270,5,-3,36,left96,right96,-2,-1,0,0⟩
compact_certificate theorem valid96 : Valid point spec96 := by
  dsimp only [Valid,spec96]
  decide +kernel
compact_certificate theorem row96 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 258)=formalLeading spec96 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec96,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left96,right96] <;> ring
compact_certificate def left97 : ℕ → ℕ
  | 1 => 10
  | 2 => 159
  | 4 => 157
  | 5 => 52
  | 7 => 218
  | 8 => 219
  | _ => 0
compact_certificate def right97 : ℕ → ℕ
  | 1 => 24
  | 2 => 58
  | 4 => 100
  | 5 => 0
  | 7 => 18
  | 8 => 22
  | _ => 0
compact_certificate def spec97 : Spec := ⟨259,270,9,-9,100,left97,right97,-2,2,-2,0⟩
compact_certificate theorem valid97 : Valid point spec97 := by
  dsimp only [Valid,spec97]
  decide +kernel
compact_certificate theorem row97 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 259)=formalLeading spec97 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec97,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left97,right97] <;> ring
compact_certificate def left98 : ℕ → ℕ
  | 1 => 34
  | 2 => 202
  | 4 => 217
  | 7 => 203
  | 8 => 52
  | 11 => 95
  | 13 => 219
  | 14 => 62
  | _ => 0
compact_certificate def right98 : ℕ → ℕ
  | 1 => 101
  | 2 => 135
  | 4 => 91
  | 7 => 90
  | 8 => 37
  | 11 => 96
  | 13 => 2
  | 14 => 38
  | _ => 0
compact_certificate def spec98 : Spec := ⟨260,270,15,-3,36,left98,right98,-2,-1,0,0⟩
compact_certificate theorem valid98 : Valid point spec98 := by
  dsimp only [Valid,spec98]
  decide +kernel
compact_certificate theorem row98 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 260)=formalLeading spec98 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec98,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left98,right98] <;> ring
compact_certificate def left99 : ℕ → ℕ
  | 1 => 216
  | 2 => 217
  | 4 => 23
  | 5 => 160
  | 7 => 158
  | 8 => 62
  | _ => 0
compact_certificate def right99 : ℕ → ℕ
  | 1 => 53
  | 2 => 39
  | 4 => 72
  | 5 => 98
  | 7 => 14
  | 8 => 31
  | _ => 0
compact_certificate def spec99 : Spec := ⟨262,270,9,9,-100,left99,right99,-2,2,-2,0⟩
compact_certificate theorem valid99 : Valid point spec99 := by
  dsimp only [Valid,spec99]
  decide +kernel
compact_certificate theorem row99 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 262)=formalLeading spec99 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec99,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left99,right99] <;> ring
compact_certificate def left100 : ℕ → ℕ
  | 1 => 197
  | 3 => 220
  | 7 => 26
  | 9 => 210
  | _ => 0
compact_certificate def right100 : ℕ → ℕ
  | 1 => 2
  | 3 => 101
  | 7 => 90
  | 9 => 99
  | _ => 0
compact_certificate def spec100 : Spec := ⟨265,270,10,1,-27,left100,right100,0,-3,0,0⟩
compact_certificate theorem valid100 : Valid point spec100 := by
  dsimp only [Valid,spec100]
  decide +kernel
compact_certificate theorem row100 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 265)=formalLeading spec100 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec100,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left100,right100] <;> ring
compact_certificate def left101 : ℕ → ℕ
  | 1 => 211
  | 3 => 8
  | 7 => 221
  | 9 => 196
  | _ => 0
compact_certificate def right101 : ℕ → ℕ
  | 1 => 101
  | 3 => 91
  | 7 => 99
  | 9 => 2
  | _ => 0
compact_certificate def spec101 : Spec := ⟨266,270,10,-1,27,left101,right101,0,-3,0,0⟩
compact_certificate theorem valid101 : Valid point spec101 := by
  dsimp only [Valid,spec101]
  decide +kernel
compact_certificate theorem row101 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 266)=formalLeading spec101 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec101,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left101,right101] <;> ring
compact_certificate def left102 : ℕ → ℕ
  | 1 => 70
  | 5 => 233
  | 7 => 165
  | 11 => 151
  | 13 => 239
  | 17 => 65
  | _ => 0
compact_certificate def right102 : ℕ → ℕ
  | 1 => 28
  | 5 => 6
  | 7 => 75
  | 11 => 16
  | 13 => 33
  | 17 => 69
  | _ => 0
compact_certificate def spec102 : Spec := ⟨281,270,18,-1,225,left102,right102,0,-2,-2,0⟩
compact_certificate theorem valid102 : Valid point spec102 := by
  dsimp only [Valid,spec102]
  decide +kernel
compact_certificate theorem row102 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 281)=formalLeading spec102 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec102,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left102,right102] <;> ring
compact_certificate def left103 : ℕ → ℕ
  | 1 => 36
  | 5 => 236
  | 7 => 154
  | 11 => 164
  | 13 => 234
  | 17 => 74
  | _ => 0
compact_certificate def right103 : ℕ → ℕ
  | 1 => 75
  | 5 => 16
  | 7 => 33
  | 11 => 69
  | 13 => 28
  | 17 => 6
  | _ => 0
compact_certificate def spec103 : Spec := ⟨283,270,18,1,-225,left103,right103,0,-2,-2,0⟩
compact_certificate theorem valid103 : Valid point spec103 := by
  dsimp only [Valid,spec103]
  decide +kernel
compact_certificate theorem row103 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 283)=formalLeading spec103 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec103,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left103,right103] <;> ring
compact_certificate def left104 : ℕ → ℕ
  | 1 => 49
  | 2 => 38
  | 4 => 232
  | 5 => 170
  | 7 => 238
  | 8 => 132
  | 10 => 249
  | 11 => 91
  | 13 => 21
  | 14 => 7
  | 16 => 166
  | 17 => 133
  | 19 => 221
  | 20 => 134
  | 22 => 152
  | 23 => 175
  | 25 => 61
  | 26 => 76
  | _ => 0
compact_certificate def right104 : ℕ → ℕ
  | 1 => 75
  | 2 => 22
  | 4 => 50
  | 5 => 80
  | 7 => 16
  | 8 => 24
  | 10 => 33
  | 11 => 58
  | 13 => 37
  | 14 => 26
  | 16 => 69
  | 17 => 100
  | 19 => 28
  | 20 => 0
  | 22 => 2
  | 23 => 32
  | 25 => 6
  | 26 => 18
  | _ => 0
compact_certificate def spec104 : Spec := ⟨288,270,27,-2,50,left104,right104,0,0,-2,0⟩
compact_certificate theorem valid104 : Valid point spec104 := by
  dsimp only [Valid,spec104]
  decide +kernel
compact_certificate theorem row104 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 288)=formalLeading spec104 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec104,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left104,right104] <;> ring
compact_certificate def left105 : ℕ → ℕ
  | 1 => 83
  | 2 => 49
  | 4 => 72
  | 7 => 232
  | 8 => 178
  | 11 => 193
  | 13 => 233
  | 14 => 8
  | 16 => 106
  | 17 => 249
  | 19 => 14
  | 22 => 21
  | 23 => 29
  | 26 => 195
  | 28 => 151
  | 29 => 46
  | 31 => 107
  | 32 => 221
  | 34 => 53
  | 37 => 152
  | 38 => 179
  | 41 => 196
  | 43 => 65
  | 44 => 1
  | _ => 0
compact_certificate def right105 : ℕ → ℕ
  | 1 => 34
  | 2 => 10
  | 4 => 202
  | 7 => 159
  | 8 => 156
  | 11 => 97
  | 13 => 112
  | 14 => 110
  | 16 => 12
  | 17 => 157
  | 19 => 203
  | 22 => 52
  | 23 => 204
  | 26 => 60
  | 28 => 113
  | 29 => 111
  | 31 => 95
  | 32 => 218
  | 34 => 161
  | 37 => 219
  | 38 => 205
  | 41 => 42
  | 43 => 86
  | 44 => 84
  | _ => 0
compact_certificate def spec105 : Spec := ⟨289,270,45,-4,9,left105,right105,2,-2,0,0⟩
compact_certificate theorem valid105 : Valid point spec105 := by
  dsimp only [Valid,spec105]
  decide +kernel
compact_certificate theorem row105 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 289)=formalLeading spec105 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec105,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left105,right105] <;> ring
compact_certificate def left106 : ℕ → ℕ
  | 1 => 67
  | 2 => 10
  | 4 => 240
  | 5 => 159
  | 7 => 228
  | 8 => 128
  | 10 => 241
  | 11 => 157
  | 13 => 25
  | 14 => 52
  | 16 => 148
  | 17 => 129
  | 19 => 242
  | 20 => 218
  | 22 => 243
  | 23 => 219
  | 25 => 63
  | 26 => 79
  | _ => 0
compact_certificate def right106 : ℕ → ℕ
  | 1 => 37
  | 2 => 26
  | 4 => 69
  | 5 => 100
  | 7 => 28
  | 8 => 0
  | 10 => 2
  | 11 => 32
  | 13 => 6
  | 14 => 18
  | 16 => 75
  | 17 => 22
  | 19 => 50
  | 20 => 80
  | 22 => 16
  | 23 => 24
  | 25 => 33
  | 26 => 58
  | _ => 0
compact_certificate def spec106 : Spec := ⟨291,270,27,1,-100,left106,right106,-2,0,-2,0⟩
compact_certificate theorem valid106 : Valid point spec106 := by
  dsimp only [Valid,spec106]
  decide +kernel
compact_certificate theorem row106 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 291)=formalLeading spec106 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec106,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left106,right106] <;> ring
compact_certificate def left107 : ℕ → ℕ
  | 1 => 51
  | 2 => 40
  | 4 => 216
  | 5 => 244
  | 7 => 217
  | 8 => 245
  | 10 => 126
  | 11 => 143
  | 13 => 23
  | 14 => 9
  | 16 => 160
  | 17 => 246
  | 19 => 127
  | 20 => 225
  | 22 => 158
  | 23 => 247
  | 25 => 62
  | 26 => 77
  | _ => 0
compact_certificate def right107 : ℕ → ℕ
  | 1 => 14
  | 2 => 16
  | 4 => 31
  | 5 => 33
  | 7 => 46
  | 8 => 37
  | 10 => 53
  | 11 => 69
  | 13 => 39
  | 14 => 28
  | 16 => 1
  | 17 => 2
  | 19 => 72
  | 20 => 6
  | 22 => 98
  | 23 => 75
  | 25 => 8
  | 26 => 50
  | _ => 0
compact_certificate def spec107 : Spec := ⟨295,270,27,-1,100,left107,right107,-2,0,-2,0⟩
compact_certificate theorem valid107 : Valid point spec107 := by
  dsimp only [Valid,spec107]
  decide +kernel
compact_certificate theorem row107 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 295)=formalLeading spec107 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec107,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left107,right107] <;> ring

compact_certificate def left108 : ℕ → ℕ
  | 1 => 68
  | 2 => 11
  | 4 => 172
  | 5 => 153
  | 7 => 135
  | 8 => 220
  | 10 => 130
  | 11 => 163
  | 13 => 27
  | 14 => 54
  | 16 => 90
  | 17 => 248
  | 19 => 131
  | 20 => 237
  | 22 => 169
  | 23 => 235
  | 25 => 64
  | 26 => 43
  | _ => 0
compact_certificate def right108 : ℕ → ℕ
  | 1 => 39
  | 2 => 28
  | 4 => 1
  | 5 => 2
  | 7 => 72
  | 8 => 6
  | 10 => 98
  | 11 => 75
  | 13 => 8
  | 14 => 50
  | 16 => 14
  | 17 => 16
  | 19 => 31
  | 20 => 33
  | 22 => 46
  | 23 => 37
  | 25 => 53
  | 26 => 69
  | _ => 0
compact_certificate def spec108 : Spec := ⟨297,270,27,2,-50,left108,right108,0,0,-2,0⟩
compact_certificate theorem valid108 : Valid point spec108 := by
  dsimp only [Valid,spec108]
  decide +kernel
compact_certificate theorem row108 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 297)=formalLeading spec108 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec108,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left108,right108] <;> ring
compact_certificate def left109 : ℕ → ℕ
  | 1 => 336
  | 2 => 337
  | _ => 0
compact_certificate def right109 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec109 : Spec := ⟨299,378,3,1,-5292,left109,right109,-2,-3,0,-2⟩
compact_certificate theorem valid109 : Valid point spec109 := by
  dsimp only [Valid,spec109]
  decide +kernel
compact_certificate theorem row109 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 299)=formalLeading spec109 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec109,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left109,right109] <;> ring
compact_certificate def left110 : ℕ → ℕ
  | 1 => 338
  | 2 => 339
  | _ => 0
compact_certificate def right110 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec110 : Spec := ⟨300,378,3,-1,5292,left110,right110,-2,-3,0,-2⟩
compact_certificate theorem valid110 : Valid point spec110 := by
  dsimp only [Valid,spec110]
  decide +kernel
compact_certificate theorem row110 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 300)=formalLeading spec110 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec110,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left110,right110] <;> ring
compact_certificate def left111 : ℕ → ℕ
  | 1 => 340
  | 2 => 341
  | _ => 0
compact_certificate def right111 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec111 : Spec := ⟨301,378,3,2,-2646,left111,right111,0,-3,0,-2⟩
compact_certificate theorem valid111 : Valid point spec111 := by
  dsimp only [Valid,spec111]
  decide +kernel
compact_certificate theorem row111 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 301)=formalLeading spec111 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec111,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left111,right111] <;> ring
compact_certificate def left112 : ℕ → ℕ
  | 1 => 342
  | 2 => 343
  | _ => 0
compact_certificate def right112 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
compact_certificate def spec112 : Spec := ⟨302,378,3,-2,2646,left112,right112,0,-3,0,-2⟩
compact_certificate theorem valid112 : Valid point spec112 := by
  dsimp only [Valid,spec112]
  decide +kernel
compact_certificate theorem row112 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 302)=formalLeading spec112 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec112,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left112,right112] <;> ring
compact_certificate def left113 : ℕ → ℕ
  | 1 => 344
  | 2 => 345
  | _ => 0
compact_certificate def right113 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec113 : Spec := ⟨303,378,3,3,-1764,left113,right113,-2,-1,0,-2⟩
compact_certificate theorem valid113 : Valid point spec113 := by
  dsimp only [Valid,spec113]
  decide +kernel
compact_certificate theorem row113 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 303)=formalLeading spec113 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec113,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left113,right113] <;> ring
compact_certificate def left114 : ℕ → ℕ
  | 1 => 346
  | 2 => 347
  | _ => 0
compact_certificate def right114 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec114 : Spec := ⟨304,378,3,-3,1764,left114,right114,-2,-1,0,-2⟩
compact_certificate theorem valid114 : Valid point spec114 := by
  dsimp only [Valid,spec114]
  decide +kernel
compact_certificate theorem row114 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 304)=formalLeading spec114 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec114,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left114,right114] <;> ring
compact_certificate def left115 : ℕ → ℕ
  | 1 => 348
  | 2 => 349
  | _ => 0
compact_certificate def right115 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec115 : Spec := ⟨305,378,3,4,-1323,left115,right115,2,-3,0,-2⟩
compact_certificate theorem valid115 : Valid point spec115 := by
  dsimp only [Valid,spec115]
  decide +kernel
compact_certificate theorem row115 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 305)=formalLeading spec115 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec115,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left115,right115] <;> ring
compact_certificate def left116 : ℕ → ℕ
  | 1 => 350
  | 2 => 351
  | _ => 0
compact_certificate def right116 : ℕ → ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
compact_certificate def spec116 : Spec := ⟨306,378,3,-4,1323,left116,right116,2,-3,0,-2⟩
compact_certificate theorem valid116 : Valid point spec116 := by
  dsimp only [Valid,spec116]
  decide +kernel
compact_certificate theorem row116 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 306)=formalLeading spec116 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec116,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left116,right116] <;> ring
compact_certificate def left117 : ℕ → ℕ
  | 1 => 352
  | 2 => 353
  | _ => 0
compact_certificate def right117 : ℕ → ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
compact_certificate def spec117 : Spec := ⟨307,378,3,6,-882,left117,right117,0,-1,0,-2⟩
compact_certificate theorem valid117 : Valid point spec117 := by
  dsimp only [Valid,spec117]
  decide +kernel
compact_certificate theorem row117 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 307)=formalLeading spec117 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec117,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left117,right117] <;> ring
compact_certificate def left118 : ℕ → ℕ
  | 1 => 354
  | 2 => 355
  | _ => 0
compact_certificate def right118 : ℕ → ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
compact_certificate def spec118 : Spec := ⟨308,378,3,-6,882,left118,right118,0,-1,0,-2⟩
compact_certificate theorem valid118 : Valid point spec118 := by
  dsimp only [Valid,spec118]
  decide +kernel
compact_certificate theorem row118 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 308)=formalLeading spec118 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec118,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left118,right118] <;> ring
compact_certificate def left119 : ℕ → ℕ
  | 1 => 360
  | 2 => 361
  | _ => 0
compact_certificate def right119 : ℕ → ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
compact_certificate def spec119 : Spec := ⟨309,378,3,12,-441,left119,right119,2,-1,0,-2⟩
compact_certificate theorem valid119 : Valid point spec119 := by
  dsimp only [Valid,spec119]
  decide +kernel
compact_certificate theorem row119 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 309)=formalLeading spec119 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec119,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left119,right119] <;> ring

compact_certificate def left120 : ℕ → ℕ
  | 1 => 362
  | 2 => 363
  | _ => 0
compact_certificate def right120 : ℕ → ℕ
  | 1 => 3
  | 2 => 55
  | _ => 0
compact_certificate def spec120 : Spec := ⟨310,378,3,-12,441,left120,right120,2,-1,0,-2⟩
compact_certificate theorem valid120 : Valid point spec120 := by
  dsimp only [Valid,spec120]
  decide +kernel
compact_certificate theorem row120 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 310)=formalLeading spec120 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec120,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left120,right120] <;> ring
compact_certificate def left121 : ℕ → ℕ
  | 1 => 374
  | 5 => 375
  | _ => 0
compact_certificate def right121 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
compact_certificate def spec121 : Spec := ⟨311,378,6,1,-1323,left121,right121,0,-3,0,-2⟩
compact_certificate theorem valid121 : Valid point spec121 := by
  dsimp only [Valid,spec121]
  decide +kernel
compact_certificate theorem row121 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 311)=formalLeading spec121 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec121,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left121,right121] <;> ring
compact_certificate def left122 : ℕ → ℕ
  | 1 => 376
  | 5 => 377
  | _ => 0
compact_certificate def right122 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
compact_certificate def spec122 : Spec := ⟨312,378,6,-1,1323,left122,right122,0,-3,0,-2⟩
compact_certificate theorem valid122 : Valid point spec122 := by
  dsimp only [Valid,spec122]
  decide +kernel
compact_certificate theorem row122 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 312)=formalLeading spec122 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec122,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left122,right122] <;> ring
compact_certificate def left123 : ℕ → ℕ
  | 1 => 378
  | 5 => 379
  | _ => 0
compact_certificate def right123 : ℕ → ℕ
  | 1 => 2
  | 5 => 37
  | _ => 0
compact_certificate def spec123 : Spec := ⟨313,378,6,3,-441,left123,right123,0,-1,0,-2⟩
compact_certificate theorem valid123 : Valid point spec123 := by
  dsimp only [Valid,spec123]
  decide +kernel
compact_certificate theorem row123 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 313)=formalLeading spec123 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec123,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left123,right123] <;> ring
compact_certificate def left124 : ℕ → ℕ
  | 1 => 328
  | 2 => 477
  | 4 => 335
  | 5 => 433
  | 7 => 370
  | 8 => 426
  | _ => 0
compact_certificate def right124 : ℕ → ℕ
  | 1 => 28
  | 2 => 2
  | 4 => 75
  | 5 => 50
  | 7 => 33
  | 8 => 37
  | _ => 0
compact_certificate def spec124 : Spec := ⟨314,378,9,-6,294,left124,right124,0,0,0,-2⟩
compact_certificate theorem valid124 : Valid point spec124 := by
  dsimp only [Valid,spec124]
  decide +kernel
compact_certificate theorem row124 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 314)=formalLeading spec124 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec124,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left124,right124] <;> ring
compact_certificate def left125 : ℕ → ℕ
  | 1 => 332
  | 2 => 430
  | 4 => 279
  | 5 => 424
  | 7 => 372
  | 8 => 296
  | _ => 0
compact_certificate def right125 : ℕ → ℕ
  | 1 => 95
  | 2 => 55
  | 4 => 34
  | 5 => 20
  | 7 => 12
  | 8 => 3
  | _ => 0
compact_certificate def spec125 : Spec := ⟨315,378,9,12,-147,left125,right125,2,0,0,-2⟩
compact_certificate theorem valid125 : Valid point spec125 := by
  dsimp only [Valid,spec125]
  decide +kernel
compact_certificate theorem row125 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 315)=formalLeading spec125 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec125,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left125,right125] <;> ring
compact_certificate def left126 : ℕ → ℕ
  | 1 => 276
  | 2 => 373
  | 4 => 429
  | 5 => 293
  | 7 => 439
  | 8 => 333
  | _ => 0
compact_certificate def right126 : ℕ → ℕ
  | 1 => 3
  | 2 => 60
  | 4 => 55
  | 5 => 42
  | 7 => 20
  | 8 => 97
  | _ => 0
compact_certificate def spec126 : Spec := ⟨316,378,9,-12,147,left126,right126,2,0,0,-2⟩
compact_certificate theorem valid126 : Valid point spec126 := by
  dsimp only [Valid,spec126]
  decide +kernel
compact_certificate theorem row126 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 316)=formalLeading spec126 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec126,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left126,right126] <;> ring
compact_certificate def left127 : ℕ → ℕ
  | 1 => 380
  | 2 => 428
  | 4 => 283
  | 5 => 438
  | 7 => 381
  | 8 => 298
  | _ => 0
compact_certificate def right127 : ℕ → ℕ
  | 1 => 39
  | 2 => 1
  | 4 => 98
  | 5 => 8
  | 7 => 31
  | 8 => 46
  | _ => 0
compact_certificate def spec127 : Spec := ⟨317,378,9,18,-98,left127,right127,0,2,0,-2⟩
compact_certificate theorem valid127 : Valid point spec127 := by
  dsimp only [Valid,spec127]
  decide +kernel
compact_certificate theorem row127 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 317)=formalLeading spec127 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec127,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left127,right127] <;> ring
compact_certificate def left128 : ℕ → ℕ
  | 1 => 284
  | 2 => 378
  | 4 => 432
  | 5 => 273
  | 7 => 425
  | 8 => 379
  | _ => 0
compact_certificate def right128 : ℕ → ℕ
  | 1 => 80
  | 2 => 24
  | 4 => 26
  | 5 => 100
  | 7 => 32
  | 8 => 18
  | _ => 0
compact_certificate def spec128 : Spec := ⟨318,378,9,-18,98,left128,right128,0,2,0,-2⟩
compact_certificate theorem valid128 : Valid point spec128 := by
  dsimp only [Valid,spec128]
  decide +kernel
compact_certificate theorem row128 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 318)=formalLeading spec128 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec128,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left128,right128] <;> ring
compact_certificate def left129 : ℕ → ℕ
  | 1 => 289
  | 2 => 284
  | 4 => 397
  | 5 => 378
  | 7 => 529
  | 8 => 331
  | 10 => 486
  | 11 => 432
  | 13 => 278
  | 14 => 273
  | 16 => 415
  | 17 => 365
  | 19 => 549
  | 20 => 425
  | 22 => 523
  | 23 => 379
  | 25 => 295
  | 26 => 302
  | _ => 0
compact_certificate def right129 : ℕ → ℕ
  | 1 => 20
  | 2 => 142
  | 4 => 97
  | 5 => 120
  | 7 => 12
  | 8 => 66
  | 10 => 3
  | 11 => 44
  | 13 => 60
  | 14 => 121
  | 16 => 95
  | 17 => 136
  | 19 => 55
  | 20 => 71
  | 22 => 42
  | 23 => 30
  | 25 => 34
  | 26 => 15
  | _ => 0
compact_certificate def spec129 : Spec := ⟨347,378,27,-4,49,left129,right129,2,0,0,-2⟩
compact_certificate theorem valid129 : Valid point spec129 := by
  dsimp only [Valid,spec129]
  decide +kernel
compact_certificate theorem row129 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 347)=formalLeading spec129 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec129,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left129,right129] <;> ring
compact_certificate def left130 : ℕ → ℕ
  | 1 => 300
  | 2 => 276
  | 4 => 412
  | 5 => 373
  | 7 => 544
  | 8 => 362
  | 10 => 521
  | 11 => 429
  | 13 => 282
  | 14 => 293
  | 16 => 545
  | 17 => 363
  | 19 => 401
  | 20 => 439
  | 22 => 531
  | 23 => 333
  | 25 => 297
  | 26 => 307
  | _ => 0
compact_certificate def right130 : ℕ → ℕ
  | 1 => 69
  | 2 => 100
  | 4 => 28
  | 5 => 0
  | 7 => 2
  | 8 => 32
  | 10 => 6
  | 11 => 18
  | 13 => 75
  | 14 => 22
  | 16 => 50
  | 17 => 80
  | 19 => 16
  | 20 => 24
  | 22 => 33
  | 23 => 58
  | 25 => 37
  | 26 => 26
  | _ => 0
compact_certificate def spec130 : Spec := ⟨351,378,27,2,-98,left130,right130,0,0,0,-2⟩
compact_certificate theorem valid130 : Valid point spec130 := by
  dsimp only [Valid,spec130]
  decide +kernel
compact_certificate theorem row130 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 351)=formalLeading spec130 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec130,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left130,right130] <;> ring
compact_certificate def left131 : ℕ → ℕ
  | 1 => 290
  | 2 => 285
  | 4 => 332
  | 5 => 532
  | 7 => 430
  | 8 => 392
  | 10 => 360
  | 11 => 546
  | 13 => 279
  | 14 => 274
  | 16 => 424
  | 17 => 518
  | 19 => 361
  | 20 => 547
  | 22 => 372
  | 23 => 423
  | 25 => 296
  | 26 => 303
  | _ => 0
compact_certificate def right131 : ℕ → ℕ
  | 1 => 8
  | 2 => 50
  | 4 => 14
  | 5 => 16
  | 7 => 31
  | 8 => 33
  | 10 => 46
  | 11 => 37
  | 13 => 53
  | 14 => 69
  | 16 => 39
  | 17 => 28
  | 19 => 1
  | 20 => 2
  | 22 => 72
  | 23 => 6
  | 25 => 98
  | 26 => 75
  | _ => 0
compact_certificate def spec131 : Spec := ⟨357,378,27,-2,98,left131,right131,0,0,0,-2⟩
compact_certificate theorem valid131 : Valid point spec131 := by
  dsimp only [Valid,spec131]
  decide +kernel
compact_certificate theorem row131 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 357)=formalLeading spec131 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec131,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left131,right131] <;> ring

compact_certificate def left132 : ℕ → ℕ
  | 1 => 299
  | 2 => 317
  | 4 => 402
  | 5 => 508
  | 7 => 368
  | 8 => 536
  | 10 => 527
  | 11 => 537
  | 13 => 281
  | 14 => 292
  | 16 => 369
  | 17 => 538
  | 19 => 410
  | 20 => 539
  | 22 => 525
  | 23 => 391
  | 25 => 271
  | 26 => 306
  | _ => 0
compact_certificate def right132 : ℕ → ℕ
  | 1 => 31
  | 2 => 33
  | 4 => 46
  | 5 => 37
  | 7 => 53
  | 8 => 69
  | 10 => 39
  | 11 => 28
  | 13 => 1
  | 14 => 2
  | 16 => 72
  | 17 => 6
  | 19 => 98
  | 20 => 75
  | 22 => 8
  | 23 => 50
  | 25 => 14
  | 26 => 16
  | _ => 0
compact_certificate def spec132 : Spec := ⟨360,378,27,1,-196,left132,right132,-2,0,0,-2⟩
compact_certificate theorem valid132 : Valid point spec132 := by
  dsimp only [Valid,spec132]
  decide +kernel
compact_certificate theorem row132 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 360)=formalLeading spec132 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec132,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left132,right132] <;> ring
compact_certificate def left133 : ℕ → ℕ
  | 1 => 301
  | 2 => 277
  | 4 => 380
  | 5 => 516
  | 7 => 428
  | 8 => 548
  | 10 => 364
  | 11 => 421
  | 13 => 283
  | 14 => 294
  | 16 => 438
  | 17 => 489
  | 19 => 330
  | 20 => 534
  | 22 => 381
  | 23 => 396
  | 25 => 298
  | 26 => 286
  | _ => 0
compact_certificate def right133 : ℕ → ℕ
  | 1 => 57
  | 2 => 42
  | 4 => 4
  | 5 => 34
  | 7 => 73
  | 8 => 20
  | 10 => 137
  | 11 => 97
  | 13 => 118
  | 14 => 12
  | 16 => 17
  | 17 => 3
  | 19 => 35
  | 20 => 60
  | 22 => 119
  | 23 => 95
  | 25 => 149
  | 26 => 55
  | _ => 0
compact_certificate def spec133 : Spec := ⟨362,378,27,4,-49,left133,right133,2,0,0,-2⟩
compact_certificate theorem valid133 : Valid point spec133 := by
  dsimp only [Valid,spec133]
  decide +kernel
compact_certificate theorem row133 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 362)=formalLeading spec133 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec133,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left133,right133] <;> ring
compact_certificate def left134 : ℕ → ℕ
  | 1 => 291
  | 2 => 318
  | 4 => 382
  | 5 => 526
  | 7 => 540
  | 8 => 403
  | 10 => 541
  | 11 => 366
  | 13 => 280
  | 14 => 275
  | 16 => 542
  | 17 => 524
  | 19 => 543
  | 20 => 367
  | 22 => 505
  | 23 => 411
  | 25 => 272
  | 26 => 270
  | _ => 0
compact_certificate def right134 : ℕ → ℕ
  | 1 => 33
  | 2 => 58
  | 4 => 37
  | 5 => 26
  | 7 => 69
  | 8 => 100
  | 10 => 28
  | 11 => 0
  | 13 => 2
  | 14 => 32
  | 16 => 6
  | 17 => 18
  | 19 => 75
  | 20 => 22
  | 22 => 50
  | 23 => 80
  | 25 => 16
  | 26 => 24
  | _ => 0
compact_certificate def spec134 : Spec := ⟨364,378,27,-1,196,left134,right134,-2,0,0,-2⟩
compact_certificate theorem valid134 : Valid point spec134 := by
  dsimp only [Valid,spec134]
  decide +kernel
compact_certificate theorem row134 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 364)=formalLeading spec134 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec134,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left134,right134] <;> ring
compact_certificate def left135 : ℕ → ℕ
  | 1 => 142
  | 2 => 143
  | 3 => 144
  | 4 => 145
  | _ => 0
compact_certificate def right135 : ℕ → ℕ
  | 1 => 99
  | 2 => 2
  | 3 => 101
  | 4 => 91
  | _ => 0
compact_certificate def spec135 : Spec := ⟨368,270,5,1,-108,left135,right135,-2,-3,0,0⟩
compact_certificate theorem valid135 : Valid point spec135 := by
  dsimp only [Valid,spec135]
  decide +kernel
compact_certificate theorem row135 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 368)=formalLeading spec135 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec135,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left135,right135] <;> ring
compact_certificate def left136 : ℕ → ℕ
  | 1 => 146
  | 2 => 147
  | 3 => 148
  | 4 => 149
  | _ => 0
compact_certificate def right136 : ℕ → ℕ
  | 1 => 90
  | 2 => 99
  | 3 => 2
  | 4 => 101
  | _ => 0
compact_certificate def spec136 : Spec := ⟨369,270,5,-1,108,left136,right136,-2,-3,0,0⟩
compact_certificate theorem valid136 : Valid point spec136 := by
  dsimp only [Valid,spec136]
  decide +kernel
compact_certificate theorem row136 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 369)=formalLeading spec136 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec136,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left136,right136] <;> ring
compact_certificate def left137 : ℕ → ℕ
  | 1 => 150
  | 2 => 14
  | 3 => 151
  | 4 => 152
  | _ => 0
compact_certificate def right137 : ℕ → ℕ
  | 1 => 2
  | 2 => 101
  | 3 => 91
  | 4 => 90
  | _ => 0
compact_certificate def spec137 : Spec := ⟨370,270,5,2,-54,left137,right137,0,-3,0,0⟩
compact_certificate theorem valid137 : Valid point spec137 := by
  dsimp only [Valid,spec137]
  decide +kernel
compact_certificate theorem row137 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 370)=formalLeading spec137 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec137,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left137,right137] <;> ring
compact_certificate def left138 : ℕ → ℕ
  | 1 => 153
  | 2 => 154
  | 3 => 58
  | 4 => 155
  | _ => 0
compact_certificate def right138 : ℕ → ℕ
  | 1 => 91
  | 2 => 90
  | 3 => 99
  | 4 => 2
  | _ => 0
compact_certificate def spec138 : Spec := ⟨371,270,5,-2,54,left138,right138,0,-3,0,0⟩
compact_certificate theorem valid138 : Valid point spec138 := by
  dsimp only [Valid,spec138]
  decide +kernel
compact_certificate theorem row138 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 371)=formalLeading spec138 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec138,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left138,right138] <;> ring
compact_certificate def left139 : ℕ → ℕ
  | 1 => 162
  | 2 => 163
  | 3 => 164
  | 4 => 100
  | _ => 0
compact_certificate def right139 : ℕ → ℕ
  | 1 => 92
  | 2 => 128
  | 3 => 3
  | 4 => 127
  | _ => 0
compact_certificate def spec139 : Spec := ⟨372,270,5,4,-27,left139,right139,2,-3,0,0⟩
compact_certificate theorem valid139 : Valid point spec139 := by
  dsimp only [Valid,spec139]
  decide +kernel
compact_certificate theorem row139 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 372)=formalLeading spec139 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec139,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left139,right139] <;> ring
compact_certificate def left140 : ℕ → ℕ
  | 1 => 98
  | 2 => 165
  | 3 => 166
  | 4 => 167
  | _ => 0
compact_certificate def right140 : ℕ → ℕ
  | 1 => 128
  | 2 => 3
  | 3 => 127
  | 4 => 93
  | _ => 0
compact_certificate def spec140 : Spec := ⟨373,270,5,-4,27,left140,right140,2,-3,0,0⟩
compact_certificate theorem valid140 : Valid point spec140 := by
  dsimp only [Valid,spec140]
  decide +kernel
compact_certificate theorem row140 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 373)=formalLeading spec140 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec140,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left140,right140] <;> ring
compact_certificate def left141 : ℕ → ℕ
  | 1 => 192
  | 2 => 193
  | 4 => 194
  | 5 => 195
  | 7 => 167
  | 8 => 196
  | _ => 0
compact_certificate def right141 : ℕ → ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
compact_certificate def spec141 : Spec := ⟨374,270,9,2,-450,left141,right141,0,-2,-2,0⟩
compact_certificate theorem valid141 : Valid point spec141 := by
  dsimp only [Valid,spec141]
  decide +kernel
compact_certificate theorem row141 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 374)=formalLeading spec141 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec141,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left141,right141] <;> ring
compact_certificate def left142 : ℕ → ℕ
  | 1 => 197
  | 2 => 162
  | 4 => 198
  | 5 => 199
  | 7 => 200
  | 8 => 201
  | _ => 0
compact_certificate def right142 : ℕ → ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
compact_certificate def spec142 : Spec := ⟨375,270,9,-2,450,left142,right142,0,-2,-2,0⟩
compact_certificate theorem valid142 : Valid point spec142 := by
  dsimp only [Valid,spec142]
  decide +kernel
compact_certificate theorem row142 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 375)=formalLeading spec142 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec142,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left142,right142] <;> ring
compact_certificate def left143 : ℕ → ℕ
  | 1 => 72
  | 2 => 232
  | 4 => 233
  | 7 => 21
  | 8 => 213
  | 11 => 53
  | 13 => 215
  | 14 => 65
  | _ => 0
compact_certificate def right143 : ℕ → ℕ
  | 1 => 96
  | 2 => 64
  | 4 => 38
  | 7 => 135
  | 8 => 50
  | 11 => 56
  | 13 => 37
  | 14 => 134
  | _ => 0
compact_certificate def spec143 : Spec := ⟨376,270,15,2,-54,left143,right143,0,-3,0,0⟩
compact_certificate theorem valid143 : Valid point spec143 := by
  dsimp only [Valid,spec143]
  decide +kernel
compact_certificate theorem row143 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 376)=formalLeading spec143 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec143,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left143,right143] <;> ring

compact_certificate def left144 : ℕ → ℕ
  | 1 => 211
  | 2 => 150
  | 4 => 212
  | 5 => 213
  | 7 => 214
  | 8 => 215
  | _ => 0
compact_certificate def right144 : ℕ → ℕ
  | 1 => 42
  | 2 => 34
  | 4 => 97
  | 5 => 12
  | 7 => 60
  | 8 => 95
  | _ => 0
compact_certificate def spec144 : Spec := ⟨377,270,9,-4,225,left144,right144,2,-2,-2,0⟩
compact_certificate theorem valid144 : Valid point spec144 := by
  dsimp only [Valid,spec144]
  decide +kernel
compact_certificate theorem row144 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 377)=formalLeading spec144 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec144,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left144,right144] <;> ring
compact_certificate def left145 : ℕ → ℕ
  | 1 => 36
  | 2 => 206
  | 4 => 22
  | 7 => 208
  | 8 => 54
  | 11 => 234
  | 13 => 235
  | 14 => 0
  | _ => 0
compact_certificate def right145 : ℕ → ℕ
  | 1 => 135
  | 2 => 50
  | 4 => 19
  | 7 => 37
  | 8 => 134
  | 11 => 64
  | 13 => 38
  | 14 => 94
  | _ => 0
compact_certificate def spec145 : Spec := ⟨378,270,15,-2,54,left145,right145,0,-3,0,0⟩
compact_certificate theorem valid145 : Valid point spec145 := by
  dsimp only [Valid,spec145]
  decide +kernel
compact_certificate theorem row145 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 378)=formalLeading spec145 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec145,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left145,right145] <;> ring
compact_certificate def left146 : ℕ → ℕ
  | 1 => 206
  | 2 => 207
  | 4 => 208
  | 5 => 209
  | 7 => 155
  | 8 => 210
  | _ => 0
compact_certificate def right146 : ℕ → ℕ
  | 1 => 97
  | 2 => 12
  | 4 => 60
  | 5 => 95
  | 7 => 42
  | 8 => 34
  | _ => 0
compact_certificate def spec146 : Spec := ⟨379,270,9,4,-225,left146,right146,2,-2,-2,0⟩
compact_certificate theorem valid146 : Valid point spec146 := by
  dsimp only [Valid,spec146]
  decide +kernel
compact_certificate theorem row146 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 379)=formalLeading spec146 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec146,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left146,right146] <;> ring
compact_certificate def left147 : ℕ → ℕ
  | 1 => 20
  | 2 => 358
  | 3 => 431
  | 4 => 369
  | 5 => 367
  | 6 => 434
  | _ => 0
compact_certificate def right147 : ℕ → ℕ
  | 1 => 6
  | 2 => 430
  | 3 => 432
  | 4 => 433
  | 5 => 353
  | 6 => 381
  | _ => 0
compact_certificate def spec147 : Spec := ⟨397,378,7,9,-12,left147,right147,-2,1,0,0⟩
compact_certificate theorem valid147 : Valid point spec147 := by
  dsimp only [Valid,spec147]
  decide +kernel
compact_certificate theorem row147 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 397)=formalLeading spec147 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec147,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left147,right147] <;> ring
compact_certificate def left148 : ℕ → ℕ
  | 1 => 435
  | 2 => 462
  | 4 => 431
  | 5 => 409
  | 7 => 418
  | 8 => 463
  | _ => 0
compact_certificate def right148 : ℕ → ℕ
  | 1 => 33
  | 2 => 37
  | 4 => 28
  | 5 => 2
  | 7 => 75
  | 8 => 50
  | _ => 0
compact_certificate def spec148 : Spec := ⟨398,378,9,3,-588,left148,right148,-2,0,0,-2⟩
compact_certificate theorem valid148 : Valid point spec148 := by
  dsimp only [Valid,spec148]
  decide +kernel
compact_certificate theorem row148 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 398)=formalLeading spec148 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec148,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left148,right148] <;> ring
compact_certificate def left149 : ℕ → ℕ
  | 1 => 464
  | 2 => 413
  | 4 => 404
  | 5 => 437
  | 7 => 465
  | 8 => 434
  | _ => 0
compact_certificate def right149 : ℕ → ℕ
  | 1 => 37
  | 2 => 69
  | 4 => 2
  | 5 => 6
  | 7 => 50
  | 8 => 16
  | _ => 0
compact_certificate def spec149 : Spec := ⟨399,378,9,-3,588,left149,right149,-2,0,0,-2⟩
compact_certificate theorem valid149 : Valid point spec149 := by
  dsimp only [Valid,spec149]
  decide +kernel
compact_certificate theorem row149 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 399)=formalLeading spec149 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec149,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left149,right149] <;> ring
compact_certificate def left150 : ℕ → ℕ
  | 1 => 427
  | 2 => 371
  | 4 => 436
  | 5 => 334
  | 7 => 476
  | 8 => 329
  | _ => 0
compact_certificate def right150 : ℕ → ℕ
  | 1 => 50
  | 2 => 16
  | 4 => 37
  | 5 => 69
  | 7 => 2
  | 8 => 6
  | _ => 0
compact_certificate def spec150 : Spec := ⟨400,378,9,6,-294,left150,right150,0,0,0,-2⟩
compact_certificate theorem valid150 : Valid point spec150 := by
  dsimp only [Valid,spec150]
  decide +kernel
compact_certificate theorem row150 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 400)=formalLeading spec150 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec150,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left150,right150] <;> ring
compact_certificate def left151 : ℕ → ℕ
  | 1 => 490
  | 5 => 398
  | 7 => 491
  | 11 => 492
  | 13 => 416
  | 17 => 493
  | _ => 0
compact_certificate def right151 : ℕ → ℕ
  | 1 => 28
  | 5 => 6
  | 7 => 75
  | 11 => 16
  | 13 => 33
  | 17 => 69
  | _ => 0
compact_certificate def spec151 : Spec := ⟨401,378,18,1,-441,left151,right151,0,-2,0,-2⟩
compact_certificate theorem valid151 : Valid point spec151 := by
  dsimp only [Valid,spec151]
  decide +kernel
compact_certificate theorem row151 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 401)=formalLeading spec151 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec151,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left151,right151] <;> ring
compact_certificate def left152 : ℕ → ℕ
  | 1 => 494
  | 5 => 420
  | 7 => 495
  | 11 => 496
  | 13 => 395
  | 17 => 497
  | _ => 0
compact_certificate def right152 : ℕ → ℕ
  | 1 => 75
  | 5 => 16
  | 7 => 33
  | 11 => 69
  | 13 => 28
  | 17 => 6
  | _ => 0
compact_certificate def spec152 : Spec := ⟨402,378,18,-1,441,left152,right152,0,-2,0,-2⟩
compact_certificate theorem valid152 : Valid point spec152 := by
  dsimp only [Valid,spec152]
  decide +kernel
compact_certificate theorem row152 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 402)=formalLeading spec152 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec152,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left152,right152] <;> ring
compact_certificate def left153 : ℕ → ℕ
  | 1 => 305
  | 5 => 328
  | 7 => 419
  | 11 => 477
  | 13 => 517
  | 17 => 354
  | 19 => 488
  | 23 => 335
  | 25 => 533
  | 29 => 433
  | 31 => 394
  | 35 => 355
  | 37 => 551
  | 41 => 370
  | 43 => 535
  | 47 => 426
  | 49 => 519
  | 53 => 313
  | _ => 0
compact_certificate def right153 : ℕ → ℕ
  | 1 => 28
  | 5 => 1
  | 7 => 2
  | 11 => 72
  | 13 => 6
  | 17 => 98
  | 19 => 75
  | 23 => 8
  | 25 => 50
  | 29 => 14
  | 31 => 16
  | 35 => 31
  | 37 => 33
  | 41 => 46
  | 43 => 37
  | 47 => 53
  | 49 => 69
  | 53 => 39
  | _ => 0
compact_certificate def spec153 : Spec := ⟨419,378,54,1,-49,left153,right153,0,0,0,-2⟩
compact_certificate theorem valid153 : Valid point spec153 := by
  dsimp only [Valid,spec153]
  decide +kernel
compact_certificate theorem row153 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 419)=formalLeading spec153 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec153,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left153,right153] <;> ring
compact_certificate def left154 : ℕ → ℕ
  | 1 => 305
  | 2 => 32
  | 4 => 285
  | 5 => 277
  | 8 => 419
  | 10 => 376
  | 11 => 532
  | 13 => 472
  | 16 => 22
  | 17 => 420
  | 19 => 548
  | 20 => 350
  | 22 => 488
  | 23 => 80
  | 25 => 546
  | 26 => 421
  | 29 => 533
  | 31 => 309
  | 32 => 274
  | 34 => 473
  | 37 => 58
  | 38 => 496
  | 40 => 489
  | 41 => 351
  | 43 => 551
  | 44 => 26
  | 46 => 547
  | 47 => 534
  | 50 => 535
  | 52 => 377
  | 53 => 423
  | 55 => 475
  | 58 => 0
  | 59 => 497
  | 61 => 286
  | 62 => 327
  | _ => 0
compact_certificate def right154 : ℕ → ℕ
  | 1 => 307
  | 2 => 313
  | 4 => 304
  | 5 => 290
  | 8 => 276
  | 10 => 6
  | 11 => 427
  | 13 => 380
  | 16 => 477
  | 17 => 75
  | 19 => 430
  | 20 => 428
  | 22 => 362
  | 23 => 354
  | 25 => 352
  | 26 => 360
  | 29 => 429
  | 31 => 16
  | 32 => 436
  | 34 => 283
  | 37 => 433
  | 38 => 33
  | 40 => 424
  | 41 => 438
  | 43 => 363
  | 44 => 355
  | 46 => 353
  | 47 => 361
  | 50 => 439
  | 52 => 69
  | 53 => 476
  | 55 => 381
  | 58 => 426
  | 59 => 28
  | 61 => 296
  | 62 => 298
  | _ => 0
compact_certificate def spec154 : Spec := ⟨420,378,63,2,-18,left154,right154,0,-2,0,0⟩
compact_certificate theorem valid154 : Valid point spec154 := by
  dsimp only [Valid,spec154]
  decide +kernel
compact_certificate theorem row154 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 420)=formalLeading spec154 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec154,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left154,right154] <;> ring
compact_certificate def left155 : ℕ → ℕ
  | 1 => 471
  | 2 => 472
  | 4 => 393
  | 5 => 473
  | 7 => 474
  | 8 => 475
  | _ => 0
compact_certificate def right155 : ℕ → ℕ
  | 1 => 97
  | 2 => 12
  | 4 => 60
  | 5 => 95
  | 7 => 42
  | 8 => 34
  | _ => 0
compact_certificate def spec155 : Spec := ⟨421,378,9,-4,441,left155,right155,2,-2,0,-2⟩
compact_certificate theorem valid155 : Valid point spec155 := by
  dsimp only [Valid,spec155]
  decide +kernel
compact_certificate theorem row155 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 421)=formalLeading spec155 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec155,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left155,right155] <;> ring

compact_certificate def left156 : ℕ → ℕ
  | 1 => 323
  | 5 => 32
  | 11 => 277
  | 13 => 471
  | 17 => 419
  | 19 => 18
  | 23 => 532
  | 25 => 516
  | 29 => 453
  | 31 => 517
  | 37 => 392
  | 41 => 350
  | 43 => 340
  | 47 => 80
  | 53 => 421
  | 55 => 393
  | 59 => 533
  | 61 => 24
  | 65 => 274
  | 67 => 294
  | 71 => 422
  | 73 => 394
  | 79 => 518
  | 83 => 351
  | 85 => 341
  | 89 => 26
  | 95 => 534
  | 97 => 474
  | 101 => 535
  | 103 => 100
  | 107 => 423
  | 109 => 396
  | 113 => 456
  | 115 => 519
  | 121 => 303
  | 125 => 327
  | _ => 0
compact_certificate def right156 : ℕ → ℕ
  | 1 => 290
  | 5 => 284
  | 11 => 6
  | 13 => 427
  | 17 => 380
  | 19 => 378
  | 23 => 477
  | 25 => 75
  | 29 => 430
  | 31 => 428
  | 37 => 354
  | 41 => 352
  | 43 => 360
  | 47 => 432
  | 53 => 16
  | 55 => 436
  | 59 => 283
  | 61 => 273
  | 65 => 433
  | 67 => 33
  | 71 => 424
  | 73 => 438
  | 79 => 355
  | 83 => 353
  | 85 => 361
  | 89 => 425
  | 95 => 69
  | 97 => 476
  | 101 => 381
  | 103 => 379
  | 107 => 426
  | 109 => 28
  | 113 => 296
  | 115 => 298
  | 121 => 313
  | 125 => 304
  | _ => 0
compact_certificate def spec156 : Spec := ⟨422,378,126,-1,9,left156,right156,0,-2,0,0⟩
compact_certificate theorem valid156 : Valid point spec156 := by
  dsimp only [Valid,spec156]
  decide +kernel
compact_certificate theorem row156 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 422)=formalLeading spec156 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec156,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left156,right156] <;> ring
compact_certificate def left157 : ℕ → ℕ
  | 1 => 452
  | 2 => 453
  | 4 => 454
  | 5 => 422
  | 7 => 455
  | 8 => 456
  | _ => 0
compact_certificate def right157 : ℕ → ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
compact_certificate def spec157 : Spec := ⟨423,378,9,2,-882,left157,right157,0,-2,0,-2⟩
compact_certificate theorem valid157 : Valid point spec157 := by
  dsimp only [Valid,spec157]
  decide +kernel
compact_certificate theorem row157 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 423)=formalLeading spec157 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec157,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left157,right157] <;> ring
compact_certificate def left158 : ℕ → ℕ
  | 1 => 304
  | 5 => 520
  | 7 => 427
  | 11 => 528
  | 13 => 371
  | 17 => 550
  | 19 => 352
  | 23 => 399
  | 25 => 436
  | 29 => 530
  | 31 => 334
  | 35 => 487
  | 37 => 353
  | 41 => 522
  | 43 => 476
  | 47 => 417
  | 49 => 329
  | 53 => 288
  | _ => 0
compact_certificate def right158 : ℕ → ℕ
  | 1 => 18
  | 5 => 75
  | 7 => 22
  | 11 => 50
  | 13 => 80
  | 17 => 16
  | 19 => 24
  | 23 => 33
  | 25 => 58
  | 29 => 37
  | 31 => 26
  | 35 => 69
  | 37 => 100
  | 41 => 28
  | 43 => 0
  | 47 => 2
  | 49 => 32
  | 53 => 6
  | _ => 0
compact_certificate def spec158 : Spec := ⟨426,378,54,-1,49,left158,right158,0,0,0,-2⟩
compact_certificate theorem valid158 : Valid point spec158 := by
  dsimp only [Valid,spec158]
  decide +kernel
compact_certificate theorem row158 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 426)=formalLeading spec158 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec158,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left158,right158] <;> ring
compact_certificate def left159 : ℕ → ℕ
  | 1 => 311
  | 2 => 289
  | 4 => 490
  | 5 => 72
  | 8 => 466
  | 10 => 412
  | 11 => 374
  | 13 => 528
  | 16 => 529
  | 17 => 544
  | 19 => 8
  | 20 => 550
  | 22 => 348
  | 23 => 486
  | 25 => 491
  | 26 => 14
  | 29 => 468
  | 31 => 282
  | 32 => 315
  | 34 => 530
  | 37 => 415
  | 38 => 545
  | 40 => 46
  | 41 => 487
  | 43 => 349
  | 44 => 549
  | 46 => 416
  | 47 => 53
  | 50 => 469
  | 52 => 531
  | 53 => 375
  | 55 => 417
  | 58 => 295
  | 59 => 297
  | 61 => 1
  | 62 => 288
  | _ => 0
compact_certificate def right159 : ℕ → ℕ
  | 1 => 284
  | 2 => 276
  | 4 => 6
  | 5 => 427
  | 8 => 378
  | 10 => 477
  | 11 => 75
  | 13 => 430
  | 16 => 362
  | 17 => 354
  | 19 => 352
  | 20 => 360
  | 22 => 432
  | 23 => 429
  | 25 => 16
  | 26 => 436
  | 29 => 273
  | 31 => 433
  | 32 => 33
  | 34 => 424
  | 37 => 363
  | 38 => 355
  | 40 => 353
  | 41 => 361
  | 43 => 425
  | 44 => 439
  | 46 => 69
  | 47 => 476
  | 50 => 379
  | 52 => 426
  | 53 => 28
  | 55 => 296
  | 58 => 307
  | 59 => 313
  | 61 => 304
  | 62 => 290
  | _ => 0
compact_certificate def spec159 : Spec := ⟨427,378,63,-2,18,left159,right159,0,-2,0,0⟩
compact_certificate theorem valid159 : Valid point spec159 := by
  dsimp only [Valid,spec159]
  decide +kernel
compact_certificate theorem row159 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 427)=formalLeading spec159 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec159,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left159,right159] <;> ring
compact_certificate def left160 : ℕ → ℕ
  | 1 => 466
  | 2 => 467
  | 4 => 468
  | 5 => 400
  | 7 => 469
  | 8 => 470
  | _ => 0
compact_certificate def right160 : ℕ → ℕ
  | 1 => 42
  | 2 => 34
  | 4 => 97
  | 5 => 12
  | 7 => 60
  | 8 => 95
  | _ => 0
compact_certificate def spec160 : Spec := ⟨428,378,9,4,-441,left160,right160,2,-2,0,-2⟩
compact_certificate theorem valid160 : Valid point spec160 := by
  dsimp only [Valid,spec160]
  decide +kernel
compact_certificate theorem row160 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 428)=formalLeading spec160 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec160,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left160,right160] <;> ring
compact_certificate def left161 : ℕ → ℕ
  | 1 => 311
  | 5 => 300
  | 11 => 520
  | 13 => 457
  | 17 => 397
  | 19 => 412
  | 23 => 98
  | 25 => 528
  | 29 => 467
  | 31 => 529
  | 37 => 8
  | 41 => 342
  | 43 => 348
  | 47 => 521
  | 53 => 399
  | 55 => 414
  | 59 => 278
  | 61 => 282
  | 65 => 31
  | 67 => 530
  | 71 => 400
  | 73 => 415
  | 79 => 46
  | 83 => 343
  | 85 => 349
  | 89 => 401
  | 95 => 522
  | 97 => 460
  | 101 => 523
  | 103 => 531
  | 107 => 39
  | 109 => 417
  | 113 => 470
  | 115 => 295
  | 121 => 1
  | 125 => 324
  | _ => 0
compact_certificate def right161 : ℕ → ℕ
  | 1 => 313
  | 5 => 304
  | 11 => 284
  | 13 => 276
  | 17 => 6
  | 19 => 427
  | 23 => 380
  | 25 => 378
  | 29 => 477
  | 31 => 75
  | 37 => 428
  | 41 => 362
  | 43 => 354
  | 47 => 352
  | 53 => 432
  | 55 => 429
  | 59 => 16
  | 61 => 436
  | 65 => 283
  | 67 => 273
  | 71 => 433
  | 73 => 33
  | 79 => 438
  | 83 => 363
  | 85 => 355
  | 89 => 353
  | 95 => 425
  | 97 => 439
  | 101 => 69
  | 103 => 476
  | 107 => 381
  | 109 => 379
  | 113 => 426
  | 115 => 28
  | 121 => 298
  | 125 => 307
  | _ => 0
compact_certificate def spec161 : Spec := ⟨429,378,126,1,-9,left161,right161,0,-2,0,0⟩
compact_certificate theorem valid161 : Valid point spec161 := by
  dsimp only [Valid,spec161]
  decide +kernel
compact_certificate theorem row161 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 429)=formalLeading spec161 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec161,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left161,right161] <;> ring
compact_certificate def left162 : ℕ → ℕ
  | 1 => 457
  | 2 => 458
  | 4 => 414
  | 5 => 459
  | 7 => 460
  | 8 => 461
  | _ => 0
compact_certificate def right162 : ℕ → ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
compact_certificate def spec162 : Spec := ⟨430,378,9,-2,882,left162,right162,0,-2,0,-2⟩
compact_certificate theorem valid162 : Valid point spec162 := by
  dsimp only [Valid,spec162]
  decide +kernel
compact_certificate theorem row162 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 430)=formalLeading spec162 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec162,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left162,right162] <;> ring
compact_certificate def left163 : ℕ → ℕ
  | 1 => 325
  | 2 => 310
  | 4 => 34
  | 5 => 318
  | 8 => 435
  | 10 => 402
  | 11 => 20
  | 13 => 483
  | 16 => 478
  | 17 => 368
  | 19 => 403
  | 20 => 358
  | 22 => 344
  | 23 => 356
  | 25 => 12
  | 26 => 366
  | 29 => 431
  | 31 => 281
  | 32 => 3
  | 34 => 484
  | 37 => 405
  | 38 => 369
  | 40 => 524
  | 41 => 359
  | 43 => 345
  | 44 => 357
  | 46 => 95
  | 47 => 367
  | 50 => 418
  | 52 => 525
  | 53 => 55
  | 55 => 406
  | 58 => 481
  | 59 => 271
  | 61 => 270
  | 62 => 287
  | _ => 0
compact_certificate def right163 : ℕ → ℕ
  | 1 => 301
  | 2 => 284
  | 4 => 328
  | 5 => 6
  | 8 => 380
  | 10 => 373
  | 11 => 477
  | 13 => 371
  | 16 => 331
  | 17 => 362
  | 19 => 50
  | 20 => 352
  | 22 => 364
  | 23 => 432
  | 25 => 335
  | 26 => 16
  | 29 => 283
  | 31 => 293
  | 32 => 433
  | 34 => 334
  | 37 => 365
  | 38 => 363
  | 40 => 37
  | 41 => 353
  | 43 => 330
  | 44 => 425
  | 46 => 370
  | 47 => 69
  | 50 => 381
  | 52 => 333
  | 53 => 426
  | 55 => 329
  | 58 => 302
  | 59 => 307
  | 61 => 2
  | 62 => 304
  | _ => 0
compact_certificate def spec163 : Spec := ⟨435,378,63,-3,12,left163,right163,-2,0,0,0⟩
compact_certificate theorem valid163 : Valid point spec163 := by
  dsimp only [Valid,spec163]
  decide +kernel
compact_certificate theorem row163 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 435)=formalLeading spec163 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec163,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left163,right163] <;> ring
compact_certificate def left164 : ℕ → ℕ
  | 1 => 482
  | 2 => 483
  | 4 => 408
  | 5 => 484
  | 7 => 485
  | 8 => 406
  | _ => 0
compact_certificate def right164 : ℕ → ℕ
  | 1 => 46
  | 2 => 53
  | 4 => 1
  | 5 => 72
  | 7 => 8
  | 8 => 14
  | _ => 0
compact_certificate def spec164 : Spec := ⟨436,378,9,-9,196,left164,right164,-2,2,0,-2⟩
compact_certificate theorem valid164 : Valid point spec164 := by
  dsimp only [Valid,spec164]
  decide +kernel
compact_certificate theorem row164 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 436)=formalLeading spec164 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec164,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left164,right164] <;> ring
compact_certificate def left165 : ℕ → ℕ
  | 1 => 180
  | 2 => 181
  | 4 => 182
  | 5 => 183
  | 7 => 184
  | 8 => 185
  | _ => 0
compact_certificate def right165 : ℕ → ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
compact_certificate def spec165 : Spec := ⟨450,270,9,1,-900,left165,right165,-2,-2,-2,0⟩
compact_certificate theorem valid165 : Valid point spec165 := by
  dsimp only [Valid,spec165]
  decide +kernel
compact_certificate theorem row165 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 450)=formalLeading spec165 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec165,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left165,right165] <;> ring
compact_certificate def left166 : ℕ → ℕ
  | 1 => 186
  | 2 => 187
  | 4 => 188
  | 5 => 189
  | 7 => 190
  | 8 => 191
  | _ => 0
compact_certificate def right166 : ℕ → ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
compact_certificate def spec166 : Spec := ⟨451,270,9,-1,900,left166,right166,-2,-2,-2,0⟩
compact_certificate theorem valid166 : Valid point spec166 := by
  dsimp only [Valid,spec166]
  decide +kernel
compact_certificate theorem row166 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 451)=formalLeading spec166 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec166,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left166,right166] <;> ring
compact_certificate def left167 : ℕ → ℕ
  | 1 => 380
  | 2 => 362
  | 3 => 16
  | 4 => 424
  | 5 => 425
  | 6 => 426
  | _ => 0
compact_certificate def right167 : ℕ → ℕ
  | 1 => 328
  | 2 => 371
  | 3 => 364
  | 4 => 293
  | 5 => 37
  | 6 => 372
  | _ => 0
compact_certificate def spec167 : Spec := ⟨463,378,7,6,-18,left167,right167,0,-1,0,0⟩
compact_certificate theorem valid167 : Valid point spec167 := by
  dsimp only [Valid,spec167]
  decide +kernel
compact_certificate theorem row167 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 463)=formalLeading spec167 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec167,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left167,right167] <;> ring

compact_certificate def left168 : ℕ → ℕ
  | 1 => 435
  | 2 => 368
  | 3 => 366
  | 4 => 437
  | 5 => 357
  | 6 => 55
  | _ => 0
compact_certificate def right168 : ℕ → ℕ
  | 1 => 378
  | 2 => 354
  | 3 => 436
  | 4 => 438
  | 5 => 439
  | 6 => 28
  | _ => 0
compact_certificate def spec168 : Spec := ⟨464,378,7,-9,12,left168,right168,-2,1,0,0⟩
compact_certificate theorem valid168 : Valid point spec168 := by
  dsimp only [Valid,spec168]
  decide +kernel
compact_certificate theorem row168 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 464)=formalLeading spec168 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec168,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left168,right168] <;> ring
compact_certificate def left169 : ℕ → ℕ
  | 1 => 440
  | 2 => 441
  | 4 => 442
  | 5 => 443
  | 7 => 444
  | 8 => 445
  | _ => 0
compact_certificate def right169 : ℕ → ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
compact_certificate def spec169 : Spec := ⟨465,378,9,1,-1764,left169,right169,-2,-2,0,-2⟩
compact_certificate theorem valid169 : Valid point spec169 := by
  dsimp only [Valid,spec169]
  decide +kernel
compact_certificate theorem row169 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 465)=formalLeading spec169 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec169,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left169,right169] <;> ring
compact_certificate def left170 : ℕ → ℕ
  | 1 => 446
  | 2 => 447
  | 4 => 448
  | 5 => 449
  | 7 => 450
  | 8 => 451
  | _ => 0
compact_certificate def right170 : ℕ → ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
compact_certificate def spec170 : Spec := ⟨466,378,9,-1,1764,left170,right170,-2,-2,0,-2⟩
compact_certificate theorem valid170 : Valid point spec170 := by
  dsimp only [Valid,spec170]
  decide +kernel
compact_certificate theorem row170 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 466)=formalLeading spec170 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec170,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left170,right170] <;> ring
compact_certificate def left171 : ℕ → ℕ
  | 1 => 407
  | 2 => 478
  | 4 => 479
  | 5 => 405
  | 7 => 480
  | 8 => 481
  | _ => 0
compact_certificate def right171 : ℕ → ℕ
  | 1 => 58
  | 2 => 26
  | 4 => 0
  | 5 => 32
  | 7 => 22
  | 8 => 80
  | _ => 0
compact_certificate def spec171 : Spec := ⟨467,378,9,9,-196,left171,right171,-2,2,0,-2⟩
compact_certificate theorem valid171 : Valid point spec171 := by
  dsimp only [Valid,spec171]
  decide +kernel
compact_certificate theorem row171 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 467)=formalLeading spec171 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec171,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left171,right171] <;> ring
compact_certificate def left172 : ℕ → ℕ
  | 1 => 285
  | 3 => 472
  | 5 => 488
  | 9 => 489
  | 11 => 455
  | 13 => 0
  | _ => 0
compact_certificate def right172 : ℕ → ℕ
  | 1 => 332
  | 3 => 331
  | 5 => 335
  | 9 => 330
  | 11 => 333
  | 13 => 2
  | _ => 0
compact_certificate def spec172 : Spec := ⟨468,378,14,-1,27,left172,right172,0,-3,0,0⟩
compact_certificate theorem valid172 : Valid point spec172 := by
  dsimp only [Valid,spec172]
  decide +kernel
compact_certificate theorem row172 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 468)=formalLeading spec172 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec172,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left172,right172] <;> ring
compact_certificate def left173 : ℕ → ℕ
  | 1 => 312
  | 2 => 573
  | 4 => 574
  | 5 => 317
  | 8 => 575
  | 10 => 576
  | 11 => 577
  | 13 => 142
  | 16 => 578
  | 17 => 579
  | 19 => 536
  | 20 => 120
  | 22 => 580
  | 23 => 581
  | 25 => 582
  | 26 => 537
  | 29 => 583
  | 31 => 320
  | 32 => 316
  | 34 => 44
  | 37 => 584
  | 38 => 585
  | 40 => 538
  | 41 => 121
  | 43 => 586
  | 44 => 587
  | 46 => 588
  | 47 => 539
  | 50 => 589
  | 52 => 590
  | 53 => 591
  | 55 => 71
  | 58 => 592
  | 59 => 593
  | 61 => 306
  | 62 => 30
  | _ => 0
compact_certificate def right173 : ℕ → ℕ
  | 1 => 6
  | 2 => 427
  | 4 => 380
  | 5 => 378
  | 8 => 75
  | 10 => 430
  | 11 => 428
  | 13 => 362
  | 16 => 352
  | 17 => 360
  | 19 => 432
  | 20 => 429
  | 22 => 16
  | 23 => 436
  | 25 => 283
  | 26 => 273
  | 29 => 33
  | 31 => 424
  | 32 => 438
  | 34 => 363
  | 37 => 353
  | 38 => 361
  | 40 => 425
  | 41 => 439
  | 43 => 69
  | 44 => 476
  | 46 => 381
  | 47 => 379
  | 50 => 28
  | 52 => 296
  | 53 => 298
  | 55 => 307
  | 58 => 304
  | 59 => 290
  | 61 => 284
  | 62 => 276
  | _ => 0
compact_certificate def spec173 : Spec := ⟨495,378,63,-1,36,left173,right173,-2,-2,0,0⟩
compact_certificate theorem valid173 : Valid point spec173 := by
  dsimp only [Valid,spec173]
  decide +kernel
compact_certificate theorem row173 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 495)=formalLeading spec173 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec173,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left173,right173] <;> ring
compact_certificate def left174 : ℕ → ℕ
  | 1 => 4
  | 2 => 291
  | 4 => 552
  | 5 => 553
  | 8 => 73
  | 10 => 554
  | 11 => 555
  | 13 => 556
  | 16 => 540
  | 17 => 557
  | 19 => 558
  | 20 => 559
  | 22 => 118
  | 23 => 541
  | 25 => 560
  | 26 => 561
  | 29 => 17
  | 31 => 308
  | 32 => 319
  | 34 => 562
  | 37 => 542
  | 38 => 563
  | 40 => 564
  | 41 => 565
  | 43 => 119
  | 44 => 543
  | 46 => 566
  | 47 => 567
  | 50 => 149
  | 52 => 568
  | 53 => 569
  | 55 => 570
  | 58 => 272
  | 59 => 571
  | 61 => 572
  | 62 => 314
  | _ => 0
compact_certificate def right174 : ℕ → ℕ
  | 1 => 296
  | 2 => 298
  | 4 => 307
  | 5 => 313
  | 8 => 290
  | 10 => 284
  | 11 => 276
  | 13 => 6
  | 16 => 380
  | 17 => 378
  | 19 => 477
  | 20 => 75
  | 22 => 430
  | 23 => 428
  | 25 => 362
  | 26 => 354
  | 29 => 360
  | 31 => 432
  | 32 => 429
  | 34 => 16
  | 37 => 283
  | 38 => 273
  | 40 => 433
  | 41 => 33
  | 43 => 424
  | 44 => 438
  | 46 => 363
  | 47 => 355
  | 50 => 361
  | 52 => 425
  | 53 => 439
  | 55 => 69
  | 58 => 381
  | 59 => 379
  | 61 => 426
  | 62 => 28
  | _ => 0
compact_certificate def spec174 : Spec := ⟨499,378,63,1,-36,left174,right174,-2,-2,0,0⟩
compact_certificate theorem valid174 : Valid point spec174 := by
  dsimp only [Valid,spec174]
  decide +kernel
compact_certificate theorem row174 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 499)=formalLeading spec174 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec174,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left174,right174] <;> ring
compact_certificate def left175 : ℕ → ℕ
  | 1 => 81
  | 2 => 250
  | 4 => 15
  | 7 => 251
  | 8 => 244
  | 11 => 252
  | 13 => 245
  | 14 => 120
  | 16 => 253
  | 17 => 254
  | 19 => 66
  | 22 => 82
  | 23 => 9
  | 26 => 255
  | 28 => 246
  | 29 => 121
  | 31 => 256
  | 32 => 257
  | 34 => 136
  | 37 => 258
  | 38 => 247
  | 41 => 259
  | 43 => 77
  | 44 => 30
  | _ => 0
compact_certificate def right175 : ℕ → ℕ
  | 1 => 28
  | 2 => 59
  | 4 => 76
  | 7 => 48
  | 8 => 68
  | 11 => 6
  | 13 => 172
  | 14 => 170
  | 16 => 75
  | 17 => 174
  | 19 => 132
  | 22 => 122
  | 23 => 130
  | 26 => 16
  | 28 => 27
  | 29 => 7
  | 31 => 33
  | 32 => 171
  | 34 => 133
  | 37 => 123
  | 38 => 131
  | 41 => 69
  | 43 => 169
  | 44 => 175
  | _ => 0
compact_certificate def spec175 : Spec := ⟨501,270,45,1,-36,left175,right175,-2,-2,0,0⟩
compact_certificate theorem valid175 : Valid point spec175 := by
  dsimp only [Valid,spec175]
  decide +kernel
compact_certificate theorem row175 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 501)=formalLeading spec175 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec175,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left175,right175] <;> ring
compact_certificate def left176 : ℕ → ℕ
  | 1 => 4
  | 2 => 67
  | 4 => 260
  | 7 => 240
  | 8 => 261
  | 11 => 137
  | 13 => 262
  | 14 => 263
  | 16 => 118
  | 17 => 241
  | 19 => 264
  | 22 => 25
  | 23 => 41
  | 26 => 35
  | 28 => 265
  | 29 => 266
  | 31 => 119
  | 32 => 242
  | 34 => 267
  | 37 => 243
  | 38 => 268
  | 41 => 57
  | 43 => 269
  | 44 => 45
  | _ => 0
compact_certificate def right176 : ℕ → ℕ
  | 1 => 172
  | 2 => 170
  | 4 => 75
  | 7 => 132
  | 8 => 124
  | 11 => 130
  | 13 => 168
  | 14 => 16
  | 16 => 27
  | 17 => 7
  | 19 => 33
  | 22 => 133
  | 23 => 125
  | 26 => 131
  | 28 => 173
  | 29 => 69
  | 31 => 169
  | 32 => 175
  | 34 => 28
  | 37 => 76
  | 38 => 47
  | 41 => 68
  | 43 => 13
  | 44 => 6
  | _ => 0
compact_certificate def spec176 : Spec := ⟨502,270,45,-1,36,left176,right176,-2,-2,0,0⟩
compact_certificate theorem valid176 : Valid point spec176 := by
  dsimp only [Valid,spec176]
  decide +kernel
compact_certificate theorem row176 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 502)=formalLeading spec176 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec176,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left176,right176] <;> ring
compact_certificate def left177 : ℕ → ℕ
  | 1 => 18
  | 2 => 392
  | 3 => 393
  | 4 => 394
  | 5 => 395
  | 6 => 396
  | _ => 0
compact_certificate def right177 : ℕ → ℕ
  | 1 => 2
  | 2 => 332
  | 3 => 331
  | 4 => 335
  | 5 => 334
  | 6 => 330
  | _ => 0
compact_certificate def spec177 : Spec := ⟨508,378,7,2,-54,left177,right177,0,-3,0,0⟩
compact_certificate theorem valid177 : Valid point spec177 := by
  dsimp only [Valid,spec177]
  decide +kernel
compact_certificate theorem row177 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 508)=formalLeading spec177 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec177,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left177,right177] <;> ring
compact_certificate def left178 : ℕ → ℕ
  | 1 => 427
  | 2 => 428
  | 3 => 429
  | 4 => 33
  | 5 => 361
  | 6 => 379
  | _ => 0
compact_certificate def right178 : ℕ → ℕ
  | 1 => 373
  | 2 => 50
  | 3 => 279
  | 4 => 365
  | 5 => 370
  | 6 => 329
  | _ => 0
compact_certificate def spec178 : Spec := ⟨509,378,7,-6,18,left178,right178,0,-1,0,0⟩
compact_certificate theorem valid178 : Valid point spec178 := by
  dsimp only [Valid,spec178]
  decide +kernel
compact_certificate theorem row178 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 509)=formalLeading spec178 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec178,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left178,right178] <;> ring
compact_certificate def left179 : ℕ → ℕ
  | 1 => 397
  | 2 => 398
  | 3 => 399
  | 4 => 400
  | 5 => 401
  | 6 => 39
  | _ => 0
compact_certificate def right179 : ℕ → ℕ
  | 1 => 331
  | 2 => 335
  | 3 => 334
  | 4 => 330
  | 5 => 333
  | 6 => 2
  | _ => 0
compact_certificate def spec179 : Spec := ⟨519,378,7,-2,54,left179,right179,0,-3,0,0⟩
compact_certificate theorem valid179 : Valid point spec179 := by
  dsimp only [Valid,spec179]
  decide +kernel
compact_certificate theorem row179 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 519)=formalLeading spec179 x y z w 1 v := by
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec179,sampleEval,residues,Finset.sum_filter,Finset.sum_range_succ,left179,right179] <;> ring
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def specsPart0 : List Spec := [spec0,spec1,spec2,spec3,spec4,spec5,spec6,spec7,spec8,spec9,spec10,spec11]
theorem valid_part0 : ∀ r∈specsPart0, Valid point r := by
  intro r hr
  simp only [specsPart0,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
theorem row_part0 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart0, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart0,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0 x y z w a b c v
  · exact row1 x y z w a b c v
  · exact row2 x y z w a b c v
  · exact row3 x y z w a b c v
  · exact row4 x y z w a b c v
  · exact row5 x y z w a b c v
  · exact row6 x y z w a b c v
  · exact row7 x y z w a b c v
  · exact row8 x y z w a b c v
  · exact row9 x y z w a b c v
  · exact row10 x y z w a b c v
  · exact row11 x y z w a b c v

def specsPart1 : List Spec := [spec12,spec13,spec14,spec15,spec16,spec17,spec18,spec19,spec20,spec21,spec22,spec23]
theorem valid_part1 : ∀ r∈specsPart1, Valid point r := by
  intro r hr
  simp only [specsPart1,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
  · exact valid23
theorem row_part1 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart1, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart1,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row12 x y z w a b c v
  · exact row13 x y z w a b c v
  · exact row14 x y z w a b c v
  · exact row15 x y z w a b c v
  · exact row16 x y z w a b c v
  · exact row17 x y z w a b c v
  · exact row18 x y z w a b c v
  · exact row19 x y z w a b c v
  · exact row20 x y z w a b c v
  · exact row21 x y z w a b c v
  · exact row22 x y z w a b c v
  · exact row23 x y z w a b c v

def specsPart2 : List Spec := [spec24,spec25,spec26,spec27,spec28,spec29,spec30,spec31,spec32,spec33,spec34,spec35]
theorem valid_part2 : ∀ r∈specsPart2, Valid point r := by
  intro r hr
  simp only [specsPart2,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid24
  · exact valid25
  · exact valid26
  · exact valid27
  · exact valid28
  · exact valid29
  · exact valid30
  · exact valid31
  · exact valid32
  · exact valid33
  · exact valid34
  · exact valid35
theorem row_part2 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart2, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart2,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row24 x y z w a b c v
  · exact row25 x y z w a b c v
  · exact row26 x y z w a b c v
  · exact row27 x y z w a b c v
  · exact row28 x y z w a b c v
  · exact row29 x y z w a b c v
  · exact row30 x y z w a b c v
  · exact row31 x y z w a b c v
  · exact row32 x y z w a b c v
  · exact row33 x y z w a b c v
  · exact row34 x y z w a b c v
  · exact row35 x y z w a b c v

def specsPart3 : List Spec := [spec36,spec37,spec38,spec39,spec40,spec41,spec42,spec43,spec44,spec45,spec46,spec47]
theorem valid_part3 : ∀ r∈specsPart3, Valid point r := by
  intro r hr
  simp only [specsPart3,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid36
  · exact valid37
  · exact valid38
  · exact valid39
  · exact valid40
  · exact valid41
  · exact valid42
  · exact valid43
  · exact valid44
  · exact valid45
  · exact valid46
  · exact valid47
theorem row_part3 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart3, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart3,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row36 x y z w a b c v
  · exact row37 x y z w a b c v
  · exact row38 x y z w a b c v
  · exact row39 x y z w a b c v
  · exact row40 x y z w a b c v
  · exact row41 x y z w a b c v
  · exact row42 x y z w a b c v
  · exact row43 x y z w a b c v
  · exact row44 x y z w a b c v
  · exact row45 x y z w a b c v
  · exact row46 x y z w a b c v
  · exact row47 x y z w a b c v

def specsPart4 : List Spec := [spec48,spec49,spec50,spec51,spec52,spec53,spec54,spec55,spec56,spec57,spec58,spec59]
theorem valid_part4 : ∀ r∈specsPart4, Valid point r := by
  intro r hr
  simp only [specsPart4,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid48
  · exact valid49
  · exact valid50
  · exact valid51
  · exact valid52
  · exact valid53
  · exact valid54
  · exact valid55
  · exact valid56
  · exact valid57
  · exact valid58
  · exact valid59
theorem row_part4 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart4, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart4,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row48 x y z w a b c v
  · exact row49 x y z w a b c v
  · exact row50 x y z w a b c v
  · exact row51 x y z w a b c v
  · exact row52 x y z w a b c v
  · exact row53 x y z w a b c v
  · exact row54 x y z w a b c v
  · exact row55 x y z w a b c v
  · exact row56 x y z w a b c v
  · exact row57 x y z w a b c v
  · exact row58 x y z w a b c v
  · exact row59 x y z w a b c v

def specsPart5 : List Spec := [spec60,spec61,spec62,spec63,spec64,spec65,spec66,spec67,spec68,spec69,spec70,spec71]
theorem valid_part5 : ∀ r∈specsPart5, Valid point r := by
  intro r hr
  simp only [specsPart5,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid60
  · exact valid61
  · exact valid62
  · exact valid63
  · exact valid64
  · exact valid65
  · exact valid66
  · exact valid67
  · exact valid68
  · exact valid69
  · exact valid70
  · exact valid71
theorem row_part5 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart5, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart5,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row60 x y z w a b c v
  · exact row61 x y z w a b c v
  · exact row62 x y z w a b c v
  · exact row63 x y z w a b c v
  · exact row64 x y z w a b c v
  · exact row65 x y z w a b c v
  · exact row66 x y z w a b c v
  · exact row67 x y z w a b c v
  · exact row68 x y z w a b c v
  · exact row69 x y z w a b c v
  · exact row70 x y z w a b c v
  · exact row71 x y z w a b c v

def specsPart6 : List Spec := [spec72,spec73,spec74,spec75,spec76,spec77,spec78,spec79,spec80,spec81,spec82,spec83]
theorem valid_part6 : ∀ r∈specsPart6, Valid point r := by
  intro r hr
  simp only [specsPart6,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid72
  · exact valid73
  · exact valid74
  · exact valid75
  · exact valid76
  · exact valid77
  · exact valid78
  · exact valid79
  · exact valid80
  · exact valid81
  · exact valid82
  · exact valid83
theorem row_part6 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart6, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart6,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row72 x y z w a b c v
  · exact row73 x y z w a b c v
  · exact row74 x y z w a b c v
  · exact row75 x y z w a b c v
  · exact row76 x y z w a b c v
  · exact row77 x y z w a b c v
  · exact row78 x y z w a b c v
  · exact row79 x y z w a b c v
  · exact row80 x y z w a b c v
  · exact row81 x y z w a b c v
  · exact row82 x y z w a b c v
  · exact row83 x y z w a b c v

def specsPart7 : List Spec := [spec84,spec85,spec86,spec87,spec88,spec89,spec90,spec91,spec92,spec93,spec94,spec95]
theorem valid_part7 : ∀ r∈specsPart7, Valid point r := by
  intro r hr
  simp only [specsPart7,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid84
  · exact valid85
  · exact valid86
  · exact valid87
  · exact valid88
  · exact valid89
  · exact valid90
  · exact valid91
  · exact valid92
  · exact valid93
  · exact valid94
  · exact valid95
theorem row_part7 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart7, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart7,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row84 x y z w a b c v
  · exact row85 x y z w a b c v
  · exact row86 x y z w a b c v
  · exact row87 x y z w a b c v
  · exact row88 x y z w a b c v
  · exact row89 x y z w a b c v
  · exact row90 x y z w a b c v
  · exact row91 x y z w a b c v
  · exact row92 x y z w a b c v
  · exact row93 x y z w a b c v
  · exact row94 x y z w a b c v
  · exact row95 x y z w a b c v

def specsPart8 : List Spec := [spec96,spec97,spec98,spec99,spec100,spec101,spec102,spec103,spec104,spec105,spec106,spec107]
theorem valid_part8 : ∀ r∈specsPart8, Valid point r := by
  intro r hr
  simp only [specsPart8,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid96
  · exact valid97
  · exact valid98
  · exact valid99
  · exact valid100
  · exact valid101
  · exact valid102
  · exact valid103
  · exact valid104
  · exact valid105
  · exact valid106
  · exact valid107
theorem row_part8 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart8, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart8,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row96 x y z w a b c v
  · exact row97 x y z w a b c v
  · exact row98 x y z w a b c v
  · exact row99 x y z w a b c v
  · exact row100 x y z w a b c v
  · exact row101 x y z w a b c v
  · exact row102 x y z w a b c v
  · exact row103 x y z w a b c v
  · exact row104 x y z w a b c v
  · exact row105 x y z w a b c v
  · exact row106 x y z w a b c v
  · exact row107 x y z w a b c v

def specsPart9 : List Spec := [spec108,spec109,spec110,spec111,spec112,spec113,spec114,spec115,spec116,spec117,spec118,spec119]
theorem valid_part9 : ∀ r∈specsPart9, Valid point r := by
  intro r hr
  simp only [specsPart9,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid108
  · exact valid109
  · exact valid110
  · exact valid111
  · exact valid112
  · exact valid113
  · exact valid114
  · exact valid115
  · exact valid116
  · exact valid117
  · exact valid118
  · exact valid119
theorem row_part9 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart9, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart9,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row108 x y z w a b c v
  · exact row109 x y z w a b c v
  · exact row110 x y z w a b c v
  · exact row111 x y z w a b c v
  · exact row112 x y z w a b c v
  · exact row113 x y z w a b c v
  · exact row114 x y z w a b c v
  · exact row115 x y z w a b c v
  · exact row116 x y z w a b c v
  · exact row117 x y z w a b c v
  · exact row118 x y z w a b c v
  · exact row119 x y z w a b c v

def specsPart10 : List Spec := [spec120,spec121,spec122,spec123,spec124,spec125,spec126,spec127,spec128,spec129,spec130,spec131]
theorem valid_part10 : ∀ r∈specsPart10, Valid point r := by
  intro r hr
  simp only [specsPart10,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid120
  · exact valid121
  · exact valid122
  · exact valid123
  · exact valid124
  · exact valid125
  · exact valid126
  · exact valid127
  · exact valid128
  · exact valid129
  · exact valid130
  · exact valid131
theorem row_part10 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart10, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart10,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row120 x y z w a b c v
  · exact row121 x y z w a b c v
  · exact row122 x y z w a b c v
  · exact row123 x y z w a b c v
  · exact row124 x y z w a b c v
  · exact row125 x y z w a b c v
  · exact row126 x y z w a b c v
  · exact row127 x y z w a b c v
  · exact row128 x y z w a b c v
  · exact row129 x y z w a b c v
  · exact row130 x y z w a b c v
  · exact row131 x y z w a b c v

def specsPart11 : List Spec := [spec132,spec133,spec134,spec135,spec136,spec137,spec138,spec139,spec140,spec141,spec142,spec143]
theorem valid_part11 : ∀ r∈specsPart11, Valid point r := by
  intro r hr
  simp only [specsPart11,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid132
  · exact valid133
  · exact valid134
  · exact valid135
  · exact valid136
  · exact valid137
  · exact valid138
  · exact valid139
  · exact valid140
  · exact valid141
  · exact valid142
  · exact valid143
theorem row_part11 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart11, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart11,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row132 x y z w a b c v
  · exact row133 x y z w a b c v
  · exact row134 x y z w a b c v
  · exact row135 x y z w a b c v
  · exact row136 x y z w a b c v
  · exact row137 x y z w a b c v
  · exact row138 x y z w a b c v
  · exact row139 x y z w a b c v
  · exact row140 x y z w a b c v
  · exact row141 x y z w a b c v
  · exact row142 x y z w a b c v
  · exact row143 x y z w a b c v

def specsPart12 : List Spec := [spec144,spec145,spec146,spec147,spec148,spec149,spec150,spec151,spec152,spec153,spec154,spec155]
theorem valid_part12 : ∀ r∈specsPart12, Valid point r := by
  intro r hr
  simp only [specsPart12,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid144
  · exact valid145
  · exact valid146
  · exact valid147
  · exact valid148
  · exact valid149
  · exact valid150
  · exact valid151
  · exact valid152
  · exact valid153
  · exact valid154
  · exact valid155
theorem row_part12 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart12, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart12,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row144 x y z w a b c v
  · exact row145 x y z w a b c v
  · exact row146 x y z w a b c v
  · exact row147 x y z w a b c v
  · exact row148 x y z w a b c v
  · exact row149 x y z w a b c v
  · exact row150 x y z w a b c v
  · exact row151 x y z w a b c v
  · exact row152 x y z w a b c v
  · exact row153 x y z w a b c v
  · exact row154 x y z w a b c v
  · exact row155 x y z w a b c v

def specsPart13 : List Spec := [spec156,spec157,spec158,spec159,spec160,spec161,spec162,spec163,spec164,spec165,spec166,spec167]
theorem valid_part13 : ∀ r∈specsPart13, Valid point r := by
  intro r hr
  simp only [specsPart13,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid156
  · exact valid157
  · exact valid158
  · exact valid159
  · exact valid160
  · exact valid161
  · exact valid162
  · exact valid163
  · exact valid164
  · exact valid165
  · exact valid166
  · exact valid167
theorem row_part13 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart13, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart13,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row156 x y z w a b c v
  · exact row157 x y z w a b c v
  · exact row158 x y z w a b c v
  · exact row159 x y z w a b c v
  · exact row160 x y z w a b c v
  · exact row161 x y z w a b c v
  · exact row162 x y z w a b c v
  · exact row163 x y z w a b c v
  · exact row164 x y z w a b c v
  · exact row165 x y z w a b c v
  · exact row166 x y z w a b c v
  · exact row167 x y z w a b c v

def specsPart14 : List Spec := [spec168,spec169,spec170,spec171,spec172,spec173,spec174,spec175,spec176,spec177,spec178,spec179]
theorem valid_part14 : ∀ r∈specsPart14, Valid point r := by
  intro r hr
  simp only [specsPart14,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid168
  · exact valid169
  · exact valid170
  · exact valid171
  · exact valid172
  · exact valid173
  · exact valid174
  · exact valid175
  · exact valid176
  · exact valid177
  · exact valid178
  · exact valid179
theorem row_part14 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart14, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart14,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row168 x y z w a b c v
  · exact row169 x y z w a b c v
  · exact row170 x y z w a b c v
  · exact row171 x y z w a b c v
  · exact row172 x y z w a b c v
  · exact row173 x y z w a b c v
  · exact row174 x y z w a b c v
  · exact row175 x y z w a b c v
  · exact row176 x y z w a b c v
  · exact row177 x y z w a b c v
  · exact row178 x y z w a b c v
  · exact row179 x y z w a b c v

def specsPart15 : List Spec := [spec180,spec181,spec182,spec183,spec184,spec185,spec186,spec187,spec188,spec189,spec190,spec191]
theorem valid_part15 : ∀ r∈specsPart15, Valid point r := by
  intro r hr
  simp only [specsPart15,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid180
  · exact valid181
  · exact valid182
  · exact valid183
  · exact valid184
  · exact valid185
  · exact valid186
  · exact valid187
  · exact valid188
  · exact valid189
  · exact valid190
  · exact valid191
theorem row_part15 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specsPart15, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specsPart15,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row180 x y z w a b c v
  · exact row181 x y z w a b c v
  · exact row182 x y z w a b c v
  · exact row183 x y z w a b c v
  · exact row184 x y z w a b c v
  · exact row185 x y z w a b c v
  · exact row186 x y z w a b c v
  · exact row187 x y z w a b c v
  · exact row188 x y z w a b c v
  · exact row189 x y z w a b c v
  · exact row190 x y z w a b c v
  · exact row191 x y z w a b c v

end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanFiniteFamilyV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource

/-- Finite extension of the original Taylor equations, with one sign chosen
before any row is selected. No additional continuation assumption is used. -/
theorem original_finite_rows {ι : Type*} [Fintype ι] [Nonempty ι]
    (point : ℕ → ℚ) (spec : ι → Spec) (valid : ∀ i, Valid point (spec i))
    (m : ℕ) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : ι → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧ ∀ i : ι, ∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          leading (spec i) m η s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=
            error i M s+∑ n∈Finset.range M,
              shift (spec i) m η n s
                (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  classical
  obtain ⟨η,hη,hlaw⟩ := original_rows point m hf
  have hi (i : ι) := hlaw (spec i) (valid i)
  choose b error hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : ι) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨η,B,error,hη,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)
#print axioms original_finite_rows
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanFixedSignV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource

def TaylorLaw (point : ℕ → ℚ) (m : ℕ) (f : ℕ → ℂ) (η : ℂ) : Prop :=
  ∀ r : Spec, Valid point r → ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
    AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
    ∀ s : ℂ, B<s.re → leading r m η s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=error M s+
      ∑ n∈Finset.range M, shift r m η n s
        (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ)))

theorem original_taylor_law (point : ℕ → ℚ) (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ TaylorLaw point m f η := original_rows point m hf

theorem finite_rows_at_sign {ι : Type*} [Fintype ι] [Nonempty ι]
    (point : ℕ → ℚ) (spec : ι → Spec) (valid : ∀ i, Valid point (spec i))
    (m : ℕ) (f : ℕ → ℂ) (η : ℂ) (hlaw : TaylorLaw point m f η) :
    ∃ (B : ℝ) (error : ι → ℕ → ℂ → ℂ),
      ∀ i : ι, ∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          leading (spec i) m η s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=
            error i M s+∑ n∈Finset.range M,
              shift (spec i) m η n s
                (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  classical
  have hi (i : ι) := hlaw (spec i) (valid i)
  choose b error hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : ι) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
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
#print axioms finite_rows_at_sign
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def specs : List Spec := specsPart0 ++ specsPart1 ++ specsPart2 ++ specsPart3 ++ specsPart4 ++ specsPart5 ++ specsPart6 ++ specsPart7 ++ specsPart8 ++ specsPart9 ++ specsPart10 ++ specsPart11 ++ specsPart12 ++ specsPart13 ++ specsPart14 ++ specsPart15
theorem specs_length : specs.length=192 := by decide +kernel
theorem all_valid : ∀ r∈specs, Valid point r := by
  intro r hr
  simp only [specs,List.mem_append,or_assoc] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact valid_part0 r h0
  · exact valid_part1 r h1
  · exact valid_part2 r h2
  · exact valid_part3 r h3
  · exact valid_part4 r h4
  · exact valid_part5 r h5
  · exact valid_part6 r h6
  · exact valid_part7 r h7
  · exact valid_part8 r h8
  · exact valid_part9 r h9
  · exact valid_part10 r h10
  · exact valid_part11 r h11
  · exact valid_part12 r h12
  · exact valid_part13 r h13
  · exact valid_part14 r h14
  · exact valid_part15 r h15
theorem all_rows (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    ∀ r∈specs, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w 1 v := by
  intro r hr
  simp only [specs,List.mem_append,or_assoc] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact row_part0 x y z w a b c v r h0
  · exact row_part1 x y z w a b c v r h1
  · exact row_part2 x y z w a b c v r h2
  · exact row_part3 x y z w a b c v r h3
  · exact row_part4 x y z w a b c v r h4
  · exact row_part5 x y z w a b c v r h5
  · exact row_part6 x y z w a b c v r h6
  · exact row_part7 x y z w a b c v r h7
  · exact row_part8 x y z w a b c v r h8
  · exact row_part9 x y z w a b c v r h9
  · exact row_part10 x y z w a b c v r h10
  · exact row_part11 x y z w a b c v r h11
  · exact row_part12 x y z w a b c v r h12
  · exact row_part13 x y z w a b c v r h13
  · exact row_part14 x y z w a b c v r h14
  · exact row_part15 x y z w a b c v r h15

abbrev SourceIndex := Fin specs.length

def selected (i : SourceIndex) : Spec := specs.get i

theorem selected_valid (i : SourceIndex) : Valid point (selected i) :=
  all_valid _ (List.get_mem specs i)

theorem selected_physical (i : SourceIndex) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physicalRow point (selected i).source m f s=
      leading (selected i) m 1 s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s) := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physicalRow
  change _ = leading (specs.get i) m 1 s _
  change eval _ _ _ _ _ _ _ _ (inputs (specs.get i).source) = _
  rw [all_rows _ _ _ _ _ _ _ _ _ (List.get_mem specs i)]
  exact (physical_leading point (selected i) (selected_valid i) m 1 s _).symm

/-- All 192 original Taylor source rows share a half-plane and a single
Fricke sign; the positive-order terms are the explicit finite right samples. -/
theorem original_selected_rows (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : SourceIndex → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧ ∀ i : SourceIndex, ∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          leading (selected i) m η s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=
            error i M s+∑ n∈Finset.range M,
              shift (selected i) m η n s
                (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  obtain ⟨η,hη,hlaw⟩ := original_rows point m hf
  have hi (i : SourceIndex) := hlaw (selected i) (selected_valid i)
  choose b error hb using hi
  have : Nonempty SourceIndex := ⟨⟨0,by rw [specs_length]; norm_num⟩⟩
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : SourceIndex) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨η,B,error,hη,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)
#print axioms selected_physical
#print axioms original_selected_rows
end QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
end
end
end
