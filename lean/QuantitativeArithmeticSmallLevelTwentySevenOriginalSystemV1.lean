module
public import QuantitativeArithmeticSmallLevelTwentySevenSourceShiftMatrixV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues basisValues_original)

def ramanujanIndex (i : Fin 192) : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.SourceIndex := ⟨i.val,by rw [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.specs_length]; exact i.isLt⟩
def matrixIndex (i : Fin 119) : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.SourceIndex := ⟨i.val,by rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.specs_length]; exact i.isLt⟩

/-- All selected original equations hold simultaneously. The sign remains
explicit, and every positive shift factors through the fixed321 observations. -/
theorem original_system (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : ℕ → ℂ → Fin 550 → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ M : ℕ, ∀ i : Fin 550, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re → originalRows m f η s=error M s+
        ∑ n∈Finset.range M, coefficient m η n s *ᵥ
          (basisMatrix *ᵥ originalVector m f (s+((n:ℂ)+1))) := by
  obtain ⟨BH,hH⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_hecke_sources hm hf
  obtain ⟨η,BR,ER,hη,hR⟩ := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.original_selected_rows m hf
  obtain ⟨BG,EG,hG⟩ := QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.original_selected_rows m hf
  obtain ⟨BE,EE,hE⟩ := QuantitativeArithmeticSmallLevelTwentySevenEntireSource.original_sources m hm hf
  let B := max BH (max BR (max BG BE))
  have hBH : BH≤B := le_max_left _ _
  have hBR : BR≤B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBG : BG≤B := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hBE : BE≤B := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  let err : Kind → ℕ → ℂ → ℂ := fun r M s =>
    match r with
    | .hecke _ _ => 0
    | .ramanujan j => ER (ramanujanIndex j) M s
    | .matrix j => EG (matrixIndex j) M s
    | .entire j => EE j s
  have ha (r : Kind) (M : ℕ) (s : ℂ) (hs : B-((M:ℝ)+1)<s.re) :
      AnalyticAt ℂ (err r M) s := by
    cases r with
    | hecke j hj => exact analyticAt_const
    | ramanujan j =>
      apply (hR (ramanujanIndex j) M).1 s
      change BR-((M:ℝ)+1)<s.re
      linarith
    | matrix j =>
      apply (hG (matrixIndex j) M).1 s
      change BG-((M:ℝ)+1)<s.re
      linarith
    | entire j => exact ((hE j).1.analyticAt s)
  have hr (r : Kind) (M : ℕ) (s : ℂ) (hs : B<s.re) :
      row r m f η s=err r M s+∑ n∈Finset.range M,
        kindShift r m η n s (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1))) := by
    cases r with
    | hecke j hj =>
      simpa only [row,err,kindShift,Finset.sum_const_zero,add_zero] using hH s (lt_of_le_of_lt hBH hs) j hj
    | ramanujan j =>
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected,ramanujanIndex,Nat.cast_add,Nat.cast_one] using
        (hR (ramanujanIndex j) M).2 s (lt_of_le_of_lt hBR hs)
    | matrix j =>
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected,matrixIndex,Nat.cast_add,Nat.cast_one] using
        (hG (matrixIndex j) M).2 s (lt_of_le_of_lt hBG hs)
    | entire j =>
      simpa only [row,err,kindShift,Finset.sum_const_zero,add_zero] using
        (hE j).2 s (lt_of_le_of_lt hBE hs)
  refine ⟨η,B,fun M s i => err (kind i) M s,hη,?_,?_⟩
  · intro M i s hs
    exact ha (kind i) M s hs
  · intro M s hs
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    simp_rw [← basisValues_original,shift_action]
    exact hr (kind i) M s hs
#print axioms original_system
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
