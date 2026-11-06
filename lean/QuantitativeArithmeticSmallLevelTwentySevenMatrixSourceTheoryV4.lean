module

public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenKnownWordsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenPhysicalPowersV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenMatrixSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open SmallLevelAdditive Complex Set

def entry (w : Word) (i j : Fin 2) : ℤ := (value w).val i j

theorem coordA_cast (w : Word) : coordA w=(entry w 0 0:ℝ) := rfl
theorem coordB_cast (w : Word) : coordB w=(entry w 0 1:ℝ) := rfl
theorem coordC_cast (w : Word) : coordC w=(entry w 1 0:ℝ) := rfl
theorem coordD_cast (w : Word) : coordD w=(entry w 1 1:ℝ) := rfl

structure Spec where
  source : ℕ
  word : Word
  left : ℕ
  right : ℕ
  lift : ℤ
  e₂ : ℤ
  e₃ : ℤ
  e₅ : ℤ
  e₇ : ℤ

def denominator (point : ℕ → ℚ) (r : Spec) : ℚ :=
  (entry r.word 1 0:ℚ)*point r.left+(entry r.word 1 1:ℚ)

def Valid (point : ℕ → ℚ) (r : Spec) : Prop :=
  entry r.word 1 0≠0 ∧ denominator point r≠0 ∧
  ((entry r.word 0 0:ℚ)*point r.left+(entry r.word 0 1:ℚ))/denominator point r=
    point r.right+(r.lift:ℚ) ∧
  denominator point r^2=(2:ℚ)^r.e₂*3^r.e₃*5^r.e₅*7^r.e₇

def formalLeading (r : Spec) (x y z w : ℂ) (v : ℕ → ℂ) : ℂ :=
  v r.left-(x^r.e₂*y^r.e₃*z^r.e₅*w^r.e₇)*v r.right

def leading (r : Spec) (m : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  formalLeading r (primeRate 2 m s) (primeRate 3 m s)
    (primeRate 5 m s) (primeRate 7 m s) v

def shift (point : ℕ → ℚ) (r : Spec) (m n : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  (primeRate 2 m s^r.e₂*primeRate 3 m s^r.e₃*
    primeRate 5 m s^r.e₅*primeRate 7 m s^r.e₇)*
    (Complex.I*((entry r.word 1 0:ℂ)*(denominator point r:ℂ)))^(n+1)*
    Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*v r.right

/-- Original known-matrix modularity gives the exact leading row and all
positive shifts on the finite coordinate system, with analytic remainders. -/
theorem original_row (point : ℕ → ℚ) (r : Spec) (hr : Valid point r)
    (m : ℕ) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        leading r m s (fun j => original (2*m) f (point j:ℝ) s)=
          error M s+∑ n∈Finset.range M,
            shift point r m n s (fun j => original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  rcases hr with ⟨hc,hd,hp,he⟩
  have hdreal : coordC r.word*(point r.left:ℝ)+coordD r.word=(denominator point r:ℝ) := by
    simp only [coordC_cast,coordD_cast,denominator,Rat.cast_add,Rat.cast_mul,Rat.cast_intCast]
  have hcreal : coordC r.word≠0 := by rw [coordC_cast]; exact_mod_cast hc
  have hdnon : coordC r.word*(point r.left:ℝ)+coordD r.word≠0 := by
    rw [hdreal]; exact_mod_cast hd
  have hpartner : (coordA r.word*(point r.left:ℝ)+coordB r.word)/
      (coordC r.word*(point r.left:ℝ)+coordD r.word)=(point r.right:ℝ)+(r.lift:ℝ) := by
    rw [hdreal,coordA_cast,coordB_cast]
    exact_mod_cast hp
  have hscale (s : ℂ) : (((coordC r.word*(point r.left:ℝ)+coordD r.word)^2:ℝ):ℂ)^(s-(m:ℂ))=
      primeRate 2 m s^r.e₂*primeRate 3 m s^r.e₃*primeRate 5 m s^r.e₅*primeRate 7 m s^r.e₇ := by
    rw [hdreal]
    have her : (denominator point r:ℝ)^2=(2:ℝ)^r.e₂*3^r.e₃*5^r.e₅*7^r.e₇ := by
      simpa only [Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_zpow] using
        congrArg (fun t : ℚ => (t:ℝ)) he
    rw [her]
    simpa only [Complex.ofReal_natCast] using four_prime_power r.e₂ r.e₃ r.e₅ r.e₇ (m:ℝ) s
  obtain ⟨B,error,herror⟩ := original_word_taylor hf r.word hcreal (point r.left) hdnon
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (herror (M+1)).1
  · intro s hs
    have h := (herror (M+1)).2 s hs
    rw [hscale,hpartner] at h
    simp only [transform_add_int,Finset.sum_range_succ',Nat.cast_zero,add_zero,pow_zero,
      Ring.choose_zero_right,one_mul] at h
    simp only [leading,formalLeading,shift,original]
    have hder : ((coordC r.word*(coordC r.word*(point r.left:ℝ)+coordD r.word):ℝ):ℂ)=
        (entry r.word 1 0:ℂ)*(denominator point r:ℂ) := by
      rw [hdreal,coordC_cast]
      push_cast
      rfl
    simp only [hder] at h
    simp_rw [mul_add,Finset.mul_sum,mul_assoc] at h
    simp_rw [mul_assoc]
    linear_combination h
#print axioms original_row
end QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceBundleV4 -/
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
namespace QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def spec0 : Spec := ⟨1,sourceWord117,30,24,0,-2,0,0,0⟩
theorem valid0 : Valid point spec0 := by
  dsimp only [Valid,spec0]
  decide +kernel
theorem row0 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 1)=formalLeading spec0 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec0] <;> ring
def spec1 : Spec := ⟨2,sourceWord101,29,30,0,2,0,-2,0⟩
theorem valid1 : Valid point spec1 := by
  dsimp only [Valid,spec1]
  decide +kernel
theorem row1 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 2)=formalLeading spec1 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec1] <;> ring
def spec2 : Spec := ⟨4,sourceWord49,0,1,-1,0,0,0,0⟩
theorem valid2 : Valid point spec2 := by
  dsimp only [Valid,spec2]
  decide +kernel
theorem row2 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 4)=formalLeading spec2 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec2] <;> ring
def spec3 : Spec := ⟨5,sourceWord66,31,1,-1,0,0,0,0⟩
theorem valid3 : Valid point spec3 := by
  dsimp only [Valid,spec3]
  decide +kernel
theorem row3 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 5)=formalLeading spec3 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec3] <;> ring
def spec4 : Spec := ⟨6,sourceWord101,31,32,1,0,0,0,0⟩
theorem valid4 : Valid point spec4 := by
  dsimp only [Valid,spec4]
  decide +kernel
theorem row4 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 6)=formalLeading spec4 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec4] <;> ring
def spec5 : Spec := ⟨7,sourceWord139,32,4,2,2,0,0,0⟩
theorem valid5 : Valid point spec5 := by
  dsimp only [Valid,spec5]
  decide +kernel
theorem row5 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 7)=formalLeading spec5 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec5] <;> ring
def spec6 : Spec := ⟨8,sourceWord144,4,5,2,-2,0,2,0⟩
theorem valid6 : Valid point spec6 := by
  dsimp only [Valid,spec6]
  decide +kernel
theorem row6 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 8)=formalLeading spec6 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec6] <;> ring
def spec7 : Spec := ⟨9,sourceWord130,72,0,1,0,0,0,0⟩
theorem valid7 : Valid point spec7 := by
  dsimp only [Valid,spec7]
  decide +kernel
theorem row7 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 9)=formalLeading spec7 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec7] <;> ring
def spec8 : Spec := ⟨10,sourceWord10,78,72,0,0,0,-2,0⟩
theorem valid8 : Valid point spec8 := by
  dsimp only [Valid,spec8]
  decide +kernel
theorem row8 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 10)=formalLeading spec8 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec8] <;> ring
def spec9 : Spec := ⟨11,sourceWord9,83,4,0,2,0,-2,0⟩
theorem valid9 : Valid point spec9 := by
  dsimp only [Valid,spec9]
  decide +kernel
theorem row9 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 11)=formalLeading spec9 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec9] <;> ring
def spec10 : Spec := ⟨12,sourceWord9,72,85,-1,0,0,2,0⟩
theorem valid10 : Valid point spec10 := by
  dsimp only [Valid,spec10]
  decide +kernel
theorem row10 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 12)=formalLeading spec10 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec10] <;> ring
def spec11 : Spec := ⟨13,sourceWord29,29,87,-1,0,0,0,0⟩
theorem valid11 : Valid point spec11 := by
  dsimp only [Valid,spec11]
  decide +kernel
theorem row11 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 13)=formalLeading spec11 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec11] <;> ring

def spec12 : Spec := ⟨15,sourceWord144,2,3,2,2,0,0,0⟩
theorem valid12 : Valid point spec12 := by
  dsimp only [Valid,spec12]
  decide +kernel
theorem row12 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 15)=formalLeading spec12 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec12] <;> ring
def spec13 : Spec := ⟨18,sourceWord49,271,2,0,-2,0,0,-2⟩
theorem valid13 : Valid point spec13 := by
  dsimp only [Valid,spec13]
  decide +kernel
theorem row13 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 18)=formalLeading spec13 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec13] <;> ring
def spec14 : Spec := ⟨19,sourceWord106,32,272,-2,2,0,0,2⟩
theorem valid14 : Valid point spec14 := by
  dsimp only [Valid,spec14]
  decide +kernel
theorem row14 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 19)=formalLeading spec14 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec14] <;> ring
def spec15 : Spec := ⟨20,sourceWord139,24,291,2,2,0,0,2⟩
theorem valid15 : Valid point spec15 := by
  dsimp only [Valid,spec15]
  decide +kernel
theorem row15 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 20)=formalLeading spec15 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec15] <;> ring
def spec16 : Spec := ⟨21,sourceWord77,306,31,-2,-2,0,0,-2⟩
theorem valid16 : Valid point spec16 := by
  dsimp only [Valid,spec16]
  decide +kernel
theorem row16 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 21)=formalLeading spec16 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec16] <;> ring
def spec17 : Spec := ⟨22,sourceWord33,309,30,-1,2,0,0,-2⟩
theorem valid17 : Valid point spec17 := by
  dsimp only [Valid,spec17]
  decide +kernel
theorem row17 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 22)=formalLeading spec17 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec17] <;> ring
def spec18 : Spec := ⟨23,sourceWord9,311,72,0,0,0,0,-2⟩
theorem valid18 : Valid point spec18 := by
  dsimp only [Valid,spec18]
  decide +kernel
theorem row18 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 23)=formalLeading spec18 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec18] <;> ring
def spec19 : Spec := ⟨24,sourceWord145,315,4,1,2,0,0,-2⟩
theorem valid19 : Valid point spec19 := by
  dsimp only [Valid,spec19]
  decide +kernel
theorem row19 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 24)=formalLeading spec19 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec19] <;> ring
def spec20 : Spec := ⟨25,sourceWord154,317,24,0,-2,0,0,-2⟩
theorem valid20 : Valid point spec20 := by
  dsimp only [Valid,spec20]
  decide +kernel
theorem row20 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 25)=formalLeading spec20 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec20] <;> ring
def spec21 : Spec := ⟨26,sourceWord41,318,2,1,-2,0,0,-2⟩
theorem valid21 : Valid point spec21 := by
  dsimp only [Valid,spec21]
  decide +kernel
theorem row21 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 26)=formalLeading spec21 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart0,formalLeading,spec21] <;> ring
def spec22 : Spec := ⟨32,sourceWord99,597,31,1,-2,0,-2,-2⟩
theorem valid22 : Valid point spec22 := by
  dsimp only [Valid,spec22]
  decide +kernel
theorem row22 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 32)=formalLeading spec22 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec22] <;> ring
def spec23 : Spec := ⟨33,sourceWord144,6,7,2,0,0,2,0⟩
theorem valid23 : Valid point spec23 := by
  dsimp only [Valid,spec23]
  decide +kernel
theorem row23 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 33)=formalLeading spec23 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec23] <;> ring

def spec24 : Spec := ⟨34,sourceWord144,8,9,2,2,0,2,0⟩
theorem valid24 : Valid point spec24 := by
  dsimp only [Valid,spec24]
  decide +kernel
theorem row24 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 34)=formalLeading spec24 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec24] <;> ring
def spec25 : Spec := ⟨35,sourceWord101,6,10,1,2,0,2,0⟩
theorem valid25 : Valid point spec25 := by
  dsimp only [Valid,spec25]
  decide +kernel
theorem row25 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 35)=formalLeading spec25 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec25] <;> ring
def spec26 : Spec := ⟨36,sourceWord101,8,11,1,0,0,2,0⟩
theorem valid26 : Valid point spec26 := by
  dsimp only [Valid,spec26]
  decide +kernel
theorem row26 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 36)=formalLeading spec26 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec26] <;> ring
def spec27 : Spec := ⟨37,sourceWord101,12,13,1,-2,0,2,0⟩
theorem valid27 : Valid point spec27 := by
  dsimp only [Valid,spec27]
  decide +kernel
theorem row27 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 37)=formalLeading spec27 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec27] <;> ring
def spec28 : Spec := ⟨38,sourceWord101,14,15,1,2,0,0,0⟩
theorem valid28 : Valid point spec28 := by
  dsimp only [Valid,spec28]
  decide +kernel
theorem row28 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 38)=formalLeading spec28 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec28] <;> ring
def spec29 : Spec := ⟨39,sourceWord101,16,6,1,0,0,0,0⟩
theorem valid29 : Valid point spec29 := by
  dsimp only [Valid,spec29]
  decide +kernel
theorem row29 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 39)=formalLeading spec29 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec29] <;> ring
def spec30 : Spec := ⟨40,sourceWord101,17,18,1,-2,0,0,0⟩
theorem valid30 : Valid point spec30 := by
  dsimp only [Valid,spec30]
  decide +kernel
theorem row30 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 40)=formalLeading spec30 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec30] <;> ring
def spec31 : Spec := ⟨41,sourceWord101,19,20,1,2,0,-2,0⟩
theorem valid31 : Valid point spec31 := by
  dsimp only [Valid,spec31]
  decide +kernel
theorem row31 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 41)=formalLeading spec31 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec31] <;> ring
def spec32 : Spec := ⟨42,sourceWord101,21,22,1,0,0,-2,0⟩
theorem valid32 : Valid point spec32 := by
  dsimp only [Valid,spec32]
  decide +kernel
theorem row32 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 42)=formalLeading spec32 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec32] <;> ring
def spec33 : Spec := ⟨43,sourceWord101,23,16,1,-2,0,-2,0⟩
theorem valid33 : Valid point spec33 := by
  dsimp only [Valid,spec33]
  decide +kernel
theorem row33 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 43)=formalLeading spec33 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec33] <;> ring
def spec34 : Spec := ⟨44,sourceWord101,25,26,0,-2,0,-2,0⟩
theorem valid34 : Valid point spec34 := by
  dsimp only [Valid,spec34]
  decide +kernel
theorem row34 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 44)=formalLeading spec34 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec34] <;> ring
def spec35 : Spec := ⟨45,sourceWord101,27,28,0,0,0,-2,0⟩
theorem valid35 : Valid point spec35 := by
  dsimp only [Valid,spec35]
  decide +kernel
theorem row35 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 45)=formalLeading spec35 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec35] <;> ring

def spec36 : Spec := ⟨46,sourceWord101,33,34,1,2,0,0,0⟩
theorem valid36 : Valid point spec36 := by
  dsimp only [Valid,spec36]
  decide +kernel
theorem row36 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 46)=formalLeading spec36 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec36] <;> ring
def spec37 : Spec := ⟨47,sourceWord101,35,36,1,-2,0,2,0⟩
theorem valid37 : Valid point spec37 := by
  dsimp only [Valid,spec37]
  decide +kernel
theorem row37 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 47)=formalLeading spec37 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec37] <;> ring
def spec38 : Spec := ⟨48,sourceWord101,37,38,1,0,0,2,0⟩
theorem valid38 : Valid point spec38 := by
  dsimp only [Valid,spec38]
  decide +kernel
theorem row38 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 48)=formalLeading spec38 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec38] <;> ring
def spec39 : Spec := ⟨49,sourceWord101,39,40,1,2,0,2,0⟩
theorem valid39 : Valid point spec39 := by
  dsimp only [Valid,spec39]
  decide +kernel
theorem row39 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 49)=formalLeading spec39 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec39] <;> ring
def spec40 : Spec := ⟨50,sourceWord117,39,41,0,2,0,2,0⟩
theorem valid40 : Valid point spec40 := by
  dsimp only [Valid,spec40]
  decide +kernel
theorem row40 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 50)=formalLeading spec40 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec40] <;> ring
def spec41 : Spec := ⟨51,sourceWord117,42,7,0,-2,0,2,0⟩
theorem valid41 : Valid point spec41 := by
  dsimp only [Valid,spec41]
  decide +kernel
theorem row41 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 51)=formalLeading spec41 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec41] <;> ring
def spec42 : Spec := ⟨52,sourceWord117,43,44,0,2,0,-2,0⟩
theorem valid42 : Valid point spec42 := by
  dsimp only [Valid,spec42]
  decide +kernel
theorem row42 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 52)=formalLeading spec42 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec42] <;> ring
def spec43 : Spec := ⟨53,sourceWord117,45,46,0,-2,0,-2,0⟩
theorem valid43 : Valid point spec43 := by
  dsimp only [Valid,spec43]
  decide +kernel
theorem row43 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 53)=formalLeading spec43 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec43] <;> ring
def spec44 : Spec := ⟨54,sourceWord117,47,16,0,0,0,-2,0⟩
theorem valid44 : Valid point spec44 := by
  dsimp only [Valid,spec44]
  decide +kernel
theorem row44 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 54)=formalLeading spec44 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec44] <;> ring
def spec45 : Spec := ⟨55,sourceWord139,34,48,2,-2,0,2,0⟩
theorem valid45 : Valid point spec45 := by
  dsimp only [Valid,spec45]
  decide +kernel
theorem row45 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 55)=formalLeading spec45 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec45] <;> ring
def spec46 : Spec := ⟨56,sourceWord139,18,49,2,0,0,2,0⟩
theorem valid46 : Valid point spec46 := by
  dsimp only [Valid,spec46]
  decide +kernel
theorem row46 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 56)=formalLeading spec46 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec46] <;> ring
def spec47 : Spec := ⟨57,sourceWord139,50,51,2,2,0,2,0⟩
theorem valid47 : Valid point spec47 := by
  dsimp only [Valid,spec47]
  decide +kernel
theorem row47 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 57)=formalLeading spec47 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec47] <;> ring

def spec48 : Spec := ⟨58,sourceWord50,33,52,0,2,0,2,0⟩
theorem valid48 : Valid point spec48 := by
  dsimp only [Valid,spec48]
  decide +kernel
theorem row48 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 58)=formalLeading spec48 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec48] <;> ring
def spec49 : Spec := ⟨59,sourceWord50,53,54,0,0,0,2,0⟩
theorem valid49 : Valid point spec49 := by
  dsimp only [Valid,spec49]
  decide +kernel
theorem row49 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 59)=formalLeading spec49 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec49] <;> ring
def spec50 : Spec := ⟨60,sourceWord50,55,56,0,-2,0,2,0⟩
theorem valid50 : Valid point spec50 := by
  dsimp only [Valid,spec50]
  decide +kernel
theorem row50 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 60)=formalLeading spec50 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec50] <;> ring
def spec51 : Spec := ⟨61,sourceWord50,39,44,0,2,0,0,0⟩
theorem valid51 : Valid point spec51 := by
  dsimp only [Valid,spec51]
  decide +kernel
theorem row51 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 61)=formalLeading spec51 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec51] <;> ring
def spec52 : Spec := ⟨62,sourceWord50,28,33,0,0,0,0,0⟩
theorem valid52 : Valid point spec52 := by
  dsimp only [Valid,spec52]
  decide +kernel
theorem row52 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 62)=formalLeading spec52 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec52] <;> ring
def spec53 : Spec := ⟨63,sourceWord50,57,58,0,-2,0,0,0⟩
theorem valid53 : Valid point spec53 := by
  dsimp only [Valid,spec53]
  decide +kernel
theorem row53 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 63)=formalLeading spec53 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart1,formalLeading,spec53] <;> ring
def spec54 : Spec := ⟨64,sourceWord50,59,60,0,2,0,-2,0⟩
theorem valid54 : Valid point spec54 := by
  dsimp only [Valid,spec54]
  decide +kernel
theorem row54 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 64)=formalLeading spec54 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec54] <;> ring
def spec55 : Spec := ⟨65,sourceWord50,61,26,0,0,0,-2,0⟩
theorem valid55 : Valid point spec55 := by
  dsimp only [Valid,spec55]
  decide +kernel
theorem row55 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 65)=formalLeading spec55 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec55] <;> ring
def spec56 : Spec := ⟨66,sourceWord50,62,28,0,-2,0,-2,0⟩
theorem valid56 : Valid point spec56 := by
  dsimp only [Valid,spec56]
  decide +kernel
theorem row56 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 66)=formalLeading spec56 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec56] <;> ring
def spec57 : Spec := ⟨67,sourceWord50,63,18,0,-2,0,-2,0⟩
theorem valid57 : Valid point spec57 := by
  dsimp only [Valid,spec57]
  decide +kernel
theorem row57 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 67)=formalLeading spec57 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec57] <;> ring
def spec58 : Spec := ⟨68,sourceWord50,64,50,0,0,0,-2,0⟩
theorem valid58 : Valid point spec58 := by
  dsimp only [Valid,spec58]
  decide +kernel
theorem row58 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 68)=formalLeading spec58 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec58] <;> ring
def spec59 : Spec := ⟨69,sourceWord50,65,66,0,2,0,-2,0⟩
theorem valid59 : Valid point spec59 := by
  dsimp only [Valid,spec59]
  decide +kernel
theorem row59 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 69)=formalLeading spec59 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec59] <;> ring

def spec60 : Spec := ⟨70,sourceWord130,67,58,1,-2,0,-2,0⟩
theorem valid60 : Valid point spec60 := by
  dsimp only [Valid,spec60]
  decide +kernel
theorem row60 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 70)=formalLeading spec60 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec60] <;> ring
def spec61 : Spec := ⟨71,sourceWord130,68,69,1,0,0,-2,0⟩
theorem valid61 : Valid point spec61 := by
  dsimp only [Valid,spec61]
  decide +kernel
theorem row61 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 71)=formalLeading spec61 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec61] <;> ring
def spec62 : Spec := ⟨72,sourceWord130,70,71,1,2,0,-2,0⟩
theorem valid62 : Valid point spec62 := by
  dsimp only [Valid,spec62]
  decide +kernel
theorem row62 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 72)=formalLeading spec62 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec62] <;> ring
def spec63 : Spec := ⟨73,sourceWord130,73,74,1,-2,0,2,0⟩
theorem valid63 : Valid point spec63 := by
  dsimp only [Valid,spec63]
  decide +kernel
theorem row63 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 73)=formalLeading spec63 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec63] <;> ring
def spec64 : Spec := ⟨74,sourceWord130,75,76,1,0,0,2,0⟩
theorem valid64 : Valid point spec64 := by
  dsimp only [Valid,spec64]
  decide +kernel
theorem row64 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 74)=formalLeading spec64 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec64] <;> ring
def spec65 : Spec := ⟨75,sourceWord130,14,77,1,2,0,2,0⟩
theorem valid65 : Valid point spec65 := by
  dsimp only [Valid,spec65]
  decide +kernel
theorem row65 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 75)=formalLeading spec65 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec65] <;> ring
def spec66 : Spec := ⟨76,sourceWord77,79,37,-2,-2,0,-2,0⟩
theorem valid66 : Valid point spec66 := by
  dsimp only [Valid,spec66]
  decide +kernel
theorem row66 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 76)=formalLeading spec66 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec66] <;> ring
def spec67 : Spec := ⟨77,sourceWord33,80,81,0,2,0,2,0⟩
theorem valid67 : Valid point spec67 := by
  dsimp only [Valid,spec67]
  decide +kernel
theorem row67 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 77)=formalLeading spec67 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec67] <;> ring
def spec68 : Spec := ⟨78,sourceWord33,82,18,0,-2,0,-2,0⟩
theorem valid68 : Valid point spec68 := by
  dsimp only [Valid,spec68]
  decide +kernel
theorem row68 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 78)=formalLeading spec68 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec68] <;> ring
def spec69 : Spec := ⟨79,sourceWord9,84,6,0,-2,0,-2,0⟩
theorem valid69 : Valid point spec69 := by
  dsimp only [Valid,spec69]
  decide +kernel
theorem row69 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 79)=formalLeading spec69 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec69] <;> ring
def spec70 : Spec := ⟨80,sourceWord29,27,86,-1,2,0,0,0⟩
theorem valid70 : Valid point spec70 := by
  dsimp only [Valid,spec70]
  decide +kernel
theorem row70 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 80)=formalLeading spec70 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart2,formalLeading,spec70] <;> ring
def spec71 : Spec := ⟨141,sourceWord49,28,270,-1,2,0,0,2⟩
theorem valid71 : Valid point spec71 := by
  dsimp only [Valid,spec71]
  decide +kernel
theorem row71 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 141)=formalLeading spec71 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec71] <;> ring

def spec72 : Spec := ⟨142,sourceWord144,34,273,2,-2,0,0,2⟩
theorem valid72 : Valid point spec72 := by
  dsimp only [Valid,spec72]
  decide +kernel
theorem row72 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 142)=formalLeading spec72 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec72] <;> ring
def spec73 : Spec := ⟨143,sourceWord144,98,274,2,0,0,0,2⟩
theorem valid73 : Valid point spec73 := by
  dsimp only [Valid,spec73]
  decide +kernel
theorem row73 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 143)=formalLeading spec73 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec73] <;> ring
def spec74 : Spec := ⟨144,sourceWord144,16,275,2,2,0,0,2⟩
theorem valid74 : Valid point spec74 := by
  dsimp only [Valid,spec74]
  decide +kernel
theorem row74 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 144)=formalLeading spec74 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec74] <;> ring
def spec75 : Spec := ⟨145,sourceWord101,75,276,1,0,0,0,2⟩
theorem valid75 : Valid point spec75 := by
  dsimp only [Valid,spec75]
  decide +kernel
theorem row75 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 145)=formalLeading spec75 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec75] <;> ring
def spec76 : Spec := ⟨146,sourceWord101,118,277,1,-2,0,0,2⟩
theorem valid76 : Valid point spec76 := by
  dsimp only [Valid,spec76]
  decide +kernel
theorem row76 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 146)=formalLeading spec76 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec76] <;> ring
def spec77 : Spec := ⟨147,sourceWord101,278,142,1,2,0,0,-2⟩
theorem valid77 : Valid point spec77 := by
  dsimp only [Valid,spec77]
  decide +kernel
theorem row77 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 147)=formalLeading spec77 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec77] <;> ring
def spec78 : Spec := ⟨148,sourceWord101,279,50,1,0,0,0,-2⟩
theorem valid78 : Valid point spec78 := by
  dsimp only [Valid,spec78]
  decide +kernel
theorem row78 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 148)=formalLeading spec78 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec78] <;> ring
def spec79 : Spec := ⟨149,sourceWord101,280,58,1,-2,0,0,-2⟩
theorem valid79 : Valid point spec79 := by
  dsimp only [Valid,spec79]
  decide +kernel
theorem row79 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 149)=formalLeading spec79 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec79] <;> ring
def spec80 : Spec := ⟨150,sourceWord101,281,33,0,-2,0,0,-2⟩
theorem valid80 : Valid point spec80 := by
  dsimp only [Valid,spec80]
  decide +kernel
theorem row80 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 150)=formalLeading spec80 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec80] <;> ring
def spec81 : Spec := ⟨151,sourceWord101,282,100,0,0,0,0,-2⟩
theorem valid81 : Valid point spec81 := by
  dsimp only [Valid,spec81]
  decide +kernel
theorem row81 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 151)=formalLeading spec81 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec81] <;> ring
def spec82 : Spec := ⟨152,sourceWord101,283,42,0,2,0,0,-2⟩
theorem valid82 : Valid point spec82 := by
  dsimp only [Valid,spec82]
  decide +kernel
theorem row82 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 152)=formalLeading spec82 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec82] <;> ring
def spec83 : Spec := ⟨153,sourceWord101,60,284,1,-2,0,0,2⟩
theorem valid83 : Valid point spec83 := by
  dsimp only [Valid,spec83]
  decide +kernel
theorem row83 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 153)=formalLeading spec83 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec83] <;> ring

def spec84 : Spec := ⟨154,sourceWord101,53,285,1,0,0,0,2⟩
theorem valid84 : Valid point spec84 := by
  dsimp only [Valid,spec84]
  decide +kernel
theorem row84 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 154)=formalLeading spec84 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec84] <;> ring
def spec85 : Spec := ⟨155,sourceWord117,286,58,0,0,0,0,-2⟩
theorem valid85 : Valid point spec85 := by
  dsimp only [Valid,spec85]
  decide +kernel
theorem row85 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 155)=formalLeading spec85 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec85] <;> ring
def spec86 : Spec := ⟨156,sourceWord117,287,50,0,-2,0,0,-2⟩
theorem valid86 : Valid point spec86 := by
  dsimp only [Valid,spec86]
  decide +kernel
theorem row86 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 156)=formalLeading spec86 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec86] <;> ring
def spec87 : Spec := ⟨157,sourceWord117,288,17,0,2,0,0,-2⟩
theorem valid87 : Valid point spec87 := by
  dsimp only [Valid,spec87]
  decide +kernel
theorem row87 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 157)=formalLeading spec87 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec87] <;> ring
def spec88 : Spec := ⟨158,sourceWord139,15,289,2,-2,0,0,2⟩
theorem valid88 : Valid point spec88 := by
  dsimp only [Valid,spec88]
  decide +kernel
theorem row88 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 158)=formalLeading spec88 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec88] <;> ring
def spec89 : Spec := ⟨159,sourceWord139,75,290,2,0,0,0,2⟩
theorem valid89 : Valid point spec89 := by
  dsimp only [Valid,spec89]
  decide +kernel
theorem row89 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 159)=formalLeading spec89 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec89] <;> ring
def spec90 : Spec := ⟨160,sourceWord50,14,292,0,2,0,0,2⟩
theorem valid90 : Valid point spec90 := by
  dsimp only [Valid,spec90]
  decide +kernel
theorem row90 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 160)=formalLeading spec90 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec90] <;> ring
def spec91 : Spec := ⟨161,sourceWord50,37,293,0,0,0,0,2⟩
theorem valid91 : Valid point spec91 := by
  dsimp only [Valid,spec91]
  decide +kernel
theorem row91 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 161)=formalLeading spec91 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec91] <;> ring
def spec92 : Spec := ⟨162,sourceWord50,149,294,0,-2,0,0,2⟩
theorem valid92 : Valid point spec92 := by
  dsimp only [Valid,spec92]
  decide +kernel
theorem row92 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 162)=formalLeading spec92 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec92] <;> ring
def spec93 : Spec := ⟨163,sourceWord50,295,121,0,2,0,0,-2⟩
theorem valid93 : Valid point spec93 := by
  dsimp only [Valid,spec93]
  decide +kernel
theorem row93 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 163)=formalLeading spec93 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec93] <;> ring
def spec94 : Spec := ⟨164,sourceWord50,296,69,0,0,0,0,-2⟩
theorem valid94 : Valid point spec94 := by
  dsimp only [Valid,spec94]
  decide +kernel
theorem row94 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 164)=formalLeading spec94 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec94] <;> ring
def spec95 : Spec := ⟨165,sourceWord50,297,22,0,0,0,0,-2⟩
theorem valid95 : Valid point spec95 := by
  dsimp only [Valid,spec95]
  decide +kernel
theorem row95 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 165)=formalLeading spec95 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec95] <;> ring

def spec96 : Spec := ⟨166,sourceWord50,298,12,0,2,0,0,-2⟩
theorem valid96 : Valid point spec96 := by
  dsimp only [Valid,spec96]
  decide +kernel
theorem row96 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 166)=formalLeading spec96 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec96] <;> ring
def spec97 : Spec := ⟨167,sourceWord172,299,275,0,0,0,0,0⟩
theorem valid97 : Valid point spec97 := by
  dsimp only [Valid,spec97]
  decide +kernel
theorem row97 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 167)=formalLeading spec97 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec97] <;> ring
def spec98 : Spec := ⟨168,sourceWord130,300,26,1,0,0,0,-2⟩
theorem valid98 : Valid point spec98 := by
  dsimp only [Valid,spec98]
  decide +kernel
theorem row98 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 168)=formalLeading spec98 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec98] <;> ring
def spec99 : Spec := ⟨169,sourceWord130,301,55,1,2,0,0,-2⟩
theorem valid99 : Valid point spec99 := by
  dsimp only [Valid,spec99]
  decide +kernel
theorem row99 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 169)=formalLeading spec99 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec99] <;> ring
def spec100 : Spec := ⟨170,sourceWord130,20,302,1,-2,0,0,2⟩
theorem valid100 : Valid point spec100 := by
  dsimp only [Valid,spec100]
  decide +kernel
theorem row100 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 170)=formalLeading spec100 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec100] <;> ring
def spec101 : Spec := ⟨171,sourceWord130,8,303,1,0,0,0,2⟩
theorem valid101 : Valid point spec101 := by
  dsimp only [Valid,spec101]
  decide +kernel
theorem row101 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 171)=formalLeading spec101 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec101] <;> ring
def spec102 : Spec := ⟨172,sourceWord10,304,6,0,0,0,0,-2⟩
theorem valid102 : Valid point spec102 := by
  dsimp only [Valid,spec102]
  decide +kernel
theorem row102 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 172)=formalLeading spec102 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec102] <;> ring
def spec103 : Spec := ⟨173,sourceWord10,305,39,-1,0,0,0,-2⟩
theorem valid103 : Valid point spec103 := by
  dsimp only [Valid,spec103]
  decide +kernel
theorem row103 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 173)=formalLeading spec103 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec103] <;> ring
def spec104 : Spec := ⟨174,sourceWord77,307,69,-2,0,0,0,-2⟩
theorem valid104 : Valid point spec104 := by
  dsimp only [Valid,spec104]
  decide +kernel
theorem row104 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 174)=formalLeading spec104 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec104] <;> ring
def spec105 : Spec := ⟨175,sourceWord33,308,39,-1,-2,0,0,-2⟩
theorem valid105 : Valid point spec105 := by
  dsimp only [Valid,spec105]
  decide +kernel
theorem row105 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 175)=formalLeading spec105 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec105] <;> ring
def spec106 : Spec := ⟨176,sourceWord33,37,310,0,2,0,0,2⟩
theorem valid106 : Valid point spec106 := by
  dsimp only [Valid,spec106]
  decide +kernel
theorem row106 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 176)=formalLeading spec106 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec106] <;> ring
def spec107 : Spec := ⟨177,sourceWord9,312,100,-1,-2,0,0,-2⟩
theorem valid107 : Valid point spec107 := by
  dsimp only [Valid,spec107]
  decide +kernel
theorem row107 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 177)=formalLeading spec107 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec107] <;> ring

def spec108 : Spec := ⟨178,sourceWord9,34,313,-1,-2,0,0,2⟩
theorem valid108 : Valid point spec108 := by
  dsimp only [Valid,spec108]
  decide +kernel
theorem row108 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 178)=formalLeading spec108 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec108] <;> ring
def spec109 : Spec := ⟨179,sourceWord9,98,314,-1,2,0,0,2⟩
theorem valid109 : Valid point spec109 := by
  dsimp only [Valid,spec109]
  decide +kernel
theorem row109 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 179)=formalLeading spec109 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec109] <;> ring
def spec110 : Spec := ⟨180,sourceWord145,316,18,1,-2,0,0,-2⟩
theorem valid110 : Valid point spec110 := by
  dsimp only [Valid,spec110]
  decide +kernel
theorem row110 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 180)=formalLeading spec110 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec110] <;> ring
def spec111 : Spec := ⟨181,sourceWord129,319,66,0,0,0,0,-2⟩
theorem valid111 : Valid point spec111 := by
  dsimp only [Valid,spec111]
  decide +kernel
theorem row111 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 181)=formalLeading spec111 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec111] <;> ring
def spec112 : Spec := ⟨182,sourceWord129,35,320,0,0,0,0,2⟩
theorem valid112 : Valid point spec112 := by
  dsimp only [Valid,spec112]
  decide +kernel
theorem row112 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 182)=formalLeading spec112 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart5,formalLeading,spec112] <;> ring
def spec113 : Spec := ⟨215,sourceWord130,594,22,3,0,0,-2,-2⟩
theorem valid113 : Valid point spec113 := by
  dsimp only [Valid,spec113]
  decide +kernel
theorem row113 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 215)=formalLeading spec113 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec113] <;> ring
def spec114 : Spec := ⟨216,sourceWord10,595,46,0,0,0,-2,-2⟩
theorem valid114 : Valid point spec114 := by
  dsimp only [Valid,spec114]
  decide +kernel
theorem row114 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 216)=formalLeading spec114 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec114] <;> ring
def spec115 : Spec := ⟨217,sourceWord9,596,33,-1,0,0,-2,-2⟩
theorem valid115 : Valid point spec115 := by
  dsimp only [Valid,spec115]
  decide +kernel
theorem row115 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 217)=formalLeading spec115 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec115] <;> ring
def spec116 : Spec := ⟨218,sourceWord29,91,598,-1,2,0,0,2⟩
theorem valid116 : Valid point spec116 := by
  dsimp only [Valid,spec116]
  decide +kernel
theorem row116 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 218)=formalLeading spec116 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec116] <;> ring
def spec117 : Spec := ⟨219,sourceWord29,599,13,0,-2,0,0,-2⟩
theorem valid117 : Valid point spec117 := by
  dsimp only [Valid,spec117]
  decide +kernel
theorem row117 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 219)=formalLeading spec117 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec117] <;> ring
def spec118 : Spec := ⟨220,sourceWord41,600,73,1,2,0,-2,-2⟩
theorem valid118 : Valid point spec118 := by
  dsimp only [Valid,spec118]
  decide +kernel
theorem row118 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 220)=formalLeading spec118 x y z w v := by
  norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec118] <;> ring

end QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceBindingBundleV4 -/
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
namespace QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
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
theorem row_part0 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart0, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part1 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart1, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part2 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart2, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part3 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart3, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part4 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart4, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part5 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart5, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part6 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart6, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part7 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart7, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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
theorem row_part8 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart8, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
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

def specsPart9 : List Spec := [spec108,spec109,spec110,spec111,spec112,spec113,spec114,spec115,spec116,spec117,spec118]
theorem valid_part9 : ∀ r∈specsPart9, Valid point r := by
  intro r hr
  simp only [specsPart9,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
theorem row_part9 (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specsPart9, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
  intro r hr
  simp only [specsPart9,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def specs : List Spec := specsPart0 ++ specsPart1 ++ specsPart2 ++ specsPart3 ++ specsPart4 ++ specsPart5 ++ specsPart6 ++ specsPart7 ++ specsPart8 ++ specsPart9
theorem specs_length : specs.length=119 := by decide +kernel
theorem all_valid : ∀ r∈specs, Valid point r := by
  intro r hr
  simp only [specs,List.mem_append,or_assoc] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
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
theorem all_rows (x y z w a b c : ℂ) (v : ℕ → ℂ) : ∀ r∈specs, eval x y z w a b c v (inputs r.source)=formalLeading r x y z w v := by
  intro r hr
  simp only [specs,List.mem_append,or_assoc] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
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
abbrev SourceIndex := Fin specs.length

def selected (i : SourceIndex) : Spec := specs.get i

theorem selected_valid (i : SourceIndex) : Valid point (selected i) :=
  all_valid _ (List.get_mem specs i)

theorem selected_physical (i : SourceIndex) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physicalRow point (selected i).source m f s=
      leading (selected i) m s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s) := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physicalRow
  change _ = leading (specs.get i) m s _
  change eval _ _ _ _ _ _ _ _ (inputs (specs.get i).source) = _
  rw [all_rows _ _ _ _ _ _ _ _ _ (List.get_mem specs i)]
  rfl

/-- The 119 matrix source rows share a half-plane; no twist continuation
beyond the original hypotheses is assumed. -/
theorem original_selected_rows (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (error : SourceIndex → ℕ → ℂ → ℂ),
      ∀ i : SourceIndex, ∀ M : ℕ,
        AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          leading (selected i) m s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=
            error i M s+∑ n∈Finset.range M,
              shift point (selected i) m n s
                (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n+1:ℕ):ℂ))) := by
  have hi (i : SourceIndex) := original_row point (selected i) (selected_valid i) m hf
  choose b error hb using hi
  have : Nonempty SourceIndex := ⟨⟨0,by rw [specs_length]; norm_num⟩⟩
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : SourceIndex) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,error,?_⟩
  intro i M
  constructor
  · exact (hb i M).1.mono (fun s hs => by change B-((M:ℝ)+1)<s.re at hs; change b i-((M:ℝ)+1)<s.re; linarith [hbB i])
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)
#print axioms selected_physical
#print axioms original_selected_rows
end QuantitativeArithmeticSmallLevelTwentySevenMatrixSource
end
end
