module

public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenKnownWordsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceTheoryV4
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenEntireSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenEntireSourceModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenEntireSource
open SmallLevelAdditive SmallLevelTaylor FinitenessRamanujanSum
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (physicalRow)
open QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource (sampleEval sample_original)
open QuantitativeArithmeticSmallLevelTwentySevenMatrixSource (entry coordC_cast coordD_cast)
open QuantitativeArithmeticOriginalMatrixMellin

def HasEntireRow (point : ℕ → ℚ) (source m : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ (B : ℝ) (E : ℂ → ℂ), Differentiable ℂ E ∧
    ∀ s : ℂ, B<s.re → physicalRow point source m f s=E s

theorem ramanujan_row (point : ℕ → ℚ) (source Q q : ℕ) (hQ : 0<Q) (hq : 0<q)
    (hqQ : q∣Q) (sample : ℕ → ℕ)
    (hpoint : ∀ a : Fin q, a.val.Coprime q →
      point (sample a.val)=((((a.val:ℤ)*(Q/q:ℕ))%(Q:ℤ):ℤ):ℚ)/(Q:ℚ))
    (hrow : ∀ (x y z w a b c : ℂ) (v : ℕ → ℂ),
      eval x y z w a b c v (inputs source)=sampleEval q sample v)
    (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point source m f := by
  obtain ⟨hE,B,hB⟩ := original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf hq
  refine ⟨B,ramanujanEntire 27 (2*m) f q,fun s => (hE s).differentiableAt,?_⟩
  intro s hs
  unfold physicalRow
  rw [hrow]
  have hsample := sample_original point hQ hq hqQ 0 sample (by simpa only [zero_add] using hpoint) m f s
  rw [show sampleEval q sample (fun j => original (2*m) f (point j:ℝ) s)=
      ramanujanAdditive (2*m) f q 0 s by simpa using hsample]
  exact (hB s hs).symm

theorem infinity_row (point : ℕ → ℚ) (source j : ℕ) (w : Word)
    (hc : entry w 1 0≠0) (hp : (entry w 1 0:ℚ)*point j+(entry w 1 1:ℚ)=0)
    (hrow : ∀ (x y z u a b c : ℂ) (v : ℕ → ℂ),
      eval x y z u a b c v (inputs source)=v j)
    (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point source m f := by
  have hc' : coordC w≠0 := by rw [coordC_cast]; exact_mod_cast hc
  have hp' : coordC w*(point j:ℝ)+coordD w=0 := by
    rw [coordC_cast,coordD_cast]; exact_mod_cast hp
  have hE := word_infinity_entire m hm hf w (point j) hc' hp'
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point j),hE,?_⟩
  intro s hs
  unfold physicalRow
  rw [hrow]
  exact ((hB (point j) s hs).2).symm
#print axioms ramanujan_row
#print axioms infinity_row
end QuantitativeArithmeticSmallLevelTwentySevenEntireSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenEntireSourceRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 2048
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenEntireSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource (sampleEval)
open QuantitativeArithmeticSmallLevelTwentySevenMatrixSource (entry)
theorem row0 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 0)=v 24 := by
  norm_num [eval,monomial,inputs,inputPart0] <;> ring
theorem original0 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 0 m f := by
  exact infinity_row point 0 24 sourceWord101 (by decide +kernel) (by decide +kernel) row0 m hm hf
theorem row3 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 3)=v 0 := by
  norm_num [eval,monomial,inputs,inputPart0] <;> ring
theorem original3 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 3 m f := by
  exact infinity_row point 3 0 sourceWord50 (by decide +kernel) (by decide +kernel) row3 m hm hf
def sample14 : ℕ → ℕ
  | 0 => 2
  | _ => 0
theorem points14 : ∀ a : Fin 1, a.val.Coprime 1 →
    point (sample14 a.val)=((((a.val:ℤ)*(270/1:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem row14 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 14)=sampleEval 1 sample14 v := by
  norm_num [eval,monomial,inputs,inputPart0,sampleEval,sample14,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original14 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 14 m f := by
  exact ramanujan_row point 14 270 1 (by decide) (by decide) (by decide) sample14 points14 row14 m hm hf
def sample93 : ℕ → ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
theorem points93 : ∀ a : Fin 3, a.val.Coprime 3 →
    point (sample93 a.val)=((((a.val:ℤ)*(270/3:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem row93 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 93)=sampleEval 3 sample93 v := by
  norm_num [eval,monomial,inputs,inputPart2,sampleEval,sample93,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original93 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 93 m f := by
  exact ramanujan_row point 93 270 3 (by decide) (by decide) (by decide) sample93 points93 row93 m hm hf
def sample116 : ℕ → ℕ
  | 1 => 101
  | 2 => 91
  | 3 => 90
  | 4 => 99
  | _ => 0
theorem points116 : ∀ a : Fin 5, a.val.Coprime 5 →
    point (sample116 a.val)=((((a.val:ℤ)*(270/5:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem row116 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 116)=sampleEval 5 sample116 v := by
  norm_num [eval,monomial,inputs,inputPart3,sampleEval,sample116,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original116 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 116 m f := by
  exact ramanujan_row point 116 270 5 (by decide) (by decide) (by decide) sample116 points116 row116 m hm hf
def sample129 : ℕ → ℕ
  | 1 => 92
  | 3 => 128
  | 7 => 127
  | 9 => 93
  | _ => 0
theorem points129 : ∀ a : Fin 10, a.val.Coprime 10 →
    point (sample129 a.val)=((((a.val:ℤ)*(270/10:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem row129 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 129)=sampleEval 10 sample129 v := by
  norm_num [eval,monomial,inputs,inputPart4,sampleEval,sample129,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original129 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 129 m f := by
  exact ramanujan_row point 129 270 10 (by decide) (by decide) (by decide) sample129 points129 row129 m hm hf
def sample209 : ℕ → ℕ
  | 1 => 318
  | 3 => 413
  | 5 => 356
  | 9 => 359
  | 11 => 418
  | 13 => 271
  | _ => 0
theorem points209 : ∀ a : Fin 14, a.val.Coprime 14 →
    point (sample209 a.val)=((((a.val:ℤ)*(378/14:ℕ))%(378:ℤ):ℤ):ℚ)/(378:ℚ) := by decide +kernel
theorem row209 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 209)=sampleEval 14 sample209 v := by
  norm_num [eval,monomial,inputs,inputPart6,sampleEval,sample209,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original209 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 209 m f := by
  exact ramanujan_row point 209 378 14 (by decide) (by decide) (by decide) sample209 points209 row209 m hm hf
def sample213 : ℕ → ℕ
  | 1 => 310
  | 5 => 435
  | 11 => 368
  | 13 => 358
  | 17 => 366
  | 19 => 431
  | 23 => 437
  | 25 => 369
  | 29 => 357
  | 31 => 367
  | 37 => 434
  | 41 => 287
  | _ => 0
theorem points213 : ∀ a : Fin 42, a.val.Coprime 42 →
    point (sample213 a.val)=((((a.val:ℤ)*(378/42:ℕ))%(378:ℤ):ℤ):ℚ)/(378:ℚ) := by decide +kernel
theorem row213 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 213)=sampleEval 42 sample213 v := by
  norm_num [eval,monomial,inputs,inputPart6,sampleEval,sample213,residues,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem original213 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    HasEntireRow point 213 m f := by
  exact ramanujan_row point 213 378 42 (by decide) (by decide) (by decide) sample213 points213 row213 m hm hf
def source : Fin 8 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 14
  | 3 => 93
  | 4 => 116
  | 5 => 129
  | 6 => 209
  | _ => 213
theorem original_sources (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : Fin 8 → ℂ → ℂ), ∀ i : Fin 8,
      Differentiable ℂ (E i) ∧ ∀ s : ℂ, B<s.re →
        QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physicalRow point (source i) m f s=E i s := by
  have hi : ∀ i : Fin 8, HasEntireRow point (source i) m f := by
    intro i
    fin_cases i
    · exact original0 m hm hf
    · exact original3 m hm hf
    · exact original14 m hm hf
    · exact original93 m hm hf
    · exact original116 m hm hf
    · exact original129 m hm hf
    · exact original209 m hm hf
    · exact original213 m hm hf
  choose b E hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 8) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,E,?_⟩
  intro i
  exact ⟨(hb i).1,fun s hs => (hb i).2 s (lt_of_le_of_lt (hbB i) hs)⟩
#print axioms original_sources
end QuantitativeArithmeticSmallLevelTwentySevenEntireSource
end
end
