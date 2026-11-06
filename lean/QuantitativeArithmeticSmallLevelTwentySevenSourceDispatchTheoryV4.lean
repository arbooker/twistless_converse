module

public import QuantitativeArithmeticSmallLevelTwentySevenOriginalSystemV1
public import QuantitativeArithmeticSmallLevelTwentySevenPoleExtraRamanujanV1
public import QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenSelectedSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues basisValues_original)

def selectedRows (selection : Fin 550 → Kind) (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : Fin 550 → ℂ :=
  fun i => row (selection i) m f η s

def selectedCoefficient (selection : Fin 550 → Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 550) (Fin 321) ℂ :=
  fun i => kindCoefficient (selection i) m η n s

theorem selected_shift_action (selection : Fin 550 → Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) (i : Fin 550) :
    (selectedCoefficient selection m η n s *ᵥ basisValues v) i=kindShift (selection i) m η n s v :=
  kindShift_action (selection i) m η n s v

/-- All selected original equations hold simultaneously. The sign remains
explicit, and every positive shift factors through the fixed321 observations. -/
theorem selected_system (selection : Fin 550 → Kind) (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : ℕ → ℂ → Fin 550 → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ M : ℕ, ∀ i : Fin 550, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re → selectedRows selection m f η s=error M s+
        ∑ n∈Finset.range M, selectedCoefficient selection m η n s *ᵥ
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
  refine ⟨η,B,fun M s i => err (selection i) M s,hη,?_,?_⟩
  · intro M i s hs
    exact ha (selection i) M s hs
  · intro M s hs
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    simp_rw [← basisValues_original,selected_shift_action]
    exact hr (selection i) M s hs
#print axioms selected_system
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenFamilySystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues basisValues_original)

/-- One Fricke sign and one half-plane work for every source kind. A chart
may therefore be selected after the sign has been determined. -/
theorem family_system (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      ∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → row r m f η s=error r M s+
        ∑ n∈Finset.range M, kindShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1))) := by
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
  exact ⟨η,B,err,hη,ha,hr⟩

/-- Specialize a common source family to any chosen list of550 rows. -/
theorem family_selection (selection : Fin 550 → Kind) (m : ℕ) (f : ℕ → ℂ)
    (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ)
    (hr : ∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → row r m f η s=error r M s+
      ∑ n∈Finset.range M, kindShift r m η n s
        (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) :
    ∀ M : ℕ, ∀ s : ℂ, B<s.re → selectedRows selection m f η s=(fun i => error (selection i) M s)+
      ∑ n∈Finset.range M, selectedCoefficient selection m η n s *ᵥ
        (basisMatrix *ᵥ originalVector m f (s+((n:ℂ)+1))) := by
  intro M s hs
  funext i
  simp only [Pi.add_apply,Finset.sum_apply]
  simp_rw [← basisValues_original,selected_shift_action]
  exact hr (selection i) M s hs
#print axioms family_system
#print axioms family_selection
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenPoleExtendedRamanujanFamilyV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def extendedRamanujanSpec : Sum (Fin 192) (Fin 4) → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec :=
  Sum.elim QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource.ramanujanSpec
theorem extendedRamanujanValid (i : Sum (Fin 192) (Fin 4)) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (extendedRamanujanSpec i) := by
  cases i with
  | inl j => exact QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_valid _
  | inr j => exact QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource.ramanujan_valid j

/-- The original source family and the four extra Taylor rows have a common
Fricke sign and a common half-plane, before choosing either pole chart. -/
theorem family_with_extra_ramanujan (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ)
      (extraError : Fin 4 → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → row r m f η s=error r M s+
        ∑ n∈Finset.range M, kindShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) ∧
      (∀ i : Fin 4, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (extraError i M) s) ∧
      (∀ i : Fin 4, ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading
          (QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource.ramanujanSpec i) m η s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=extraError i M s+
        ∑ n∈Finset.range M,
          QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
            (QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource.ramanujanSpec i) m η n s
            (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) := by
  obtain ⟨BH,hH⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_hecke_sources hm hf
  obtain ⟨η,BR,ER,hη,hR⟩ := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.original_finite_rows point extendedRamanujanSpec extendedRamanujanValid m hf
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
    | .ramanujan j => ER (Sum.inl j) M s
    | .matrix j => EG (matrixIndex j) M s
    | .entire j => EE j s
  have ha (r : Kind) (M : ℕ) (s : ℂ) (hs : B-((M:ℝ)+1)<s.re) :
      AnalyticAt ℂ (err r M) s := by
    cases r with
    | hecke j hj => exact analyticAt_const
    | ramanujan j =>
      apply (hR (Sum.inl j) M).1 s
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
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected,extendedRamanujanSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
        (hR (Sum.inl j) M).2 s (lt_of_le_of_lt hBR hs)
    | matrix j =>
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected,matrixIndex,Nat.cast_add,Nat.cast_one] using
        (hG (matrixIndex j) M).2 s (lt_of_le_of_lt hBG hs)
    | entire j =>
      simpa only [row,err,kindShift,Finset.sum_const_zero,add_zero] using
        (hE j).2 s (lt_of_le_of_lt hBE hs)
  refine ⟨η,B,err,(fun i => ER (Sum.inr i)),hη,ha,hr,?_,?_⟩
  · intro i M s hs
    apply (hR (Sum.inr i) M).1 s
    change BR-((M:ℝ)+1)<s.re
    linarith
  · intro i M s hs
    simpa only [extendedRamanujanSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
      (hR (Sum.inr i) M).2 s (lt_of_le_of_lt hBR hs)
#print axioms family_with_extra_ramanujan
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanExtensionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def ramanujanExtensionSpec {ι : Type*} (extra : ι → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) : Sum (Fin 192) ι → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec :=
  Sum.elim QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected extra
theorem ramanujanExtensionValid {ι : Type*} (extra : ι → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec)
    (hv : ∀ i, QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (extra i)) (i : Sum (Fin 192) ι) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (ramanujanExtensionSpec extra i) := by
  cases i with
  | inl j => exact QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_valid _
  | inr j => exact hv j

/-- The original source family and any finite extra Taylor family have a common
Fricke sign and a common half-plane, before choosing either pole chart. -/
theorem family_with_ramanujan_extension {ι : Type*} [Fintype ι] [Nonempty ι]
    (extra : ι → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec)
    (hv : ∀ i, QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (extra i)) (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ)
      (extraError : ι → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → row r m f η s=error r M s+
        ∑ n∈Finset.range M, kindShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) ∧
      (∀ i : ι, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (extraError i M) s) ∧
      (∀ i : ι, ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading
          (extra i) m η s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=extraError i M s+
        ∑ n∈Finset.range M,
          QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
            (extra i) m η n s
            (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) := by
  obtain ⟨BH,hH⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_hecke_sources hm hf
  obtain ⟨η,BR,ER,hη,hR⟩ := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.original_finite_rows point (ramanujanExtensionSpec extra) (ramanujanExtensionValid extra hv) m hf
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
    | .ramanujan j => ER (Sum.inl j) M s
    | .matrix j => EG (matrixIndex j) M s
    | .entire j => EE j s
  have ha (r : Kind) (M : ℕ) (s : ℂ) (hs : B-((M:ℝ)+1)<s.re) :
      AnalyticAt ℂ (err r M) s := by
    cases r with
    | hecke j hj => exact analyticAt_const
    | ramanujan j =>
      apply (hR (Sum.inl j) M).1 s
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
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected,ramanujanExtensionSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
        (hR (Sum.inl j) M).2 s (lt_of_le_of_lt hBR hs)
    | matrix j =>
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected,matrixIndex,Nat.cast_add,Nat.cast_one] using
        (hG (matrixIndex j) M).2 s (lt_of_le_of_lt hBG hs)
    | entire j =>
      simpa only [row,err,kindShift,Finset.sum_const_zero,add_zero] using
        (hE j).2 s (lt_of_le_of_lt hBE hs)
  refine ⟨η,B,err,(fun i => ER (Sum.inr i)),hη,ha,hr,?_,?_⟩
  · intro i M s hs
    apply (hR (Sum.inr i) M).1 s
    change BR-((M:ℝ)+1)<s.re
    linarith
  · intro i M s hs
    simpa only [ramanujanExtensionSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
      (hR (Sum.inr i) M).2 s (lt_of_le_of_lt hBR hs)
#print axioms family_with_ramanujan_extension
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanExtensionFixedSignV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

/-- The original source family and any finite extra Taylor family have a common
Fricke sign and a common half-plane, before choosing either pole chart. -/
theorem family_with_ramanujan_extension_at_sign {ι : Type*} [Fintype ι] [Nonempty ι]
    (extra : ι → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec)
    (hv : ∀ i, QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (extra i)) (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hlaw : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.TaylorLaw point m f η) :
    ∃ (B : ℝ) (error : Kind → ℕ → ℂ → ℂ)
      (extraError : ι → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → row r m f η s=error r M s+
        ∑ n∈Finset.range M, kindShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) ∧
      (∀ i : ι, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (extraError i M) s) ∧
      (∀ i : ι, ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading
          (extra i) m η s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=extraError i M s+
        ∑ n∈Finset.range M,
          QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
            (extra i) m η n s
            (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) := by
  obtain ⟨BH,hH⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_hecke_sources hm hf
  obtain ⟨BR,ER,hR⟩ := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.finite_rows_at_sign point (ramanujanExtensionSpec extra) (ramanujanExtensionValid extra hv) m f η hlaw
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
    | .ramanujan j => ER (Sum.inl j) M s
    | .matrix j => EG (matrixIndex j) M s
    | .entire j => EE j s
  have ha (r : Kind) (M : ℕ) (s : ℂ) (hs : B-((M:ℝ)+1)<s.re) :
      AnalyticAt ℂ (err r M) s := by
    cases r with
    | hecke j hj => exact analyticAt_const
    | ramanujan j =>
      apply (hR (Sum.inl j) M).1 s
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
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected,ramanujanExtensionSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
        (hR (Sum.inl j) M).2 s (lt_of_le_of_lt hBR hs)
    | matrix j =>
      simpa only [row,err,kindShift,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected,matrixIndex,Nat.cast_add,Nat.cast_one] using
        (hG (matrixIndex j) M).2 s (lt_of_le_of_lt hBG hs)
    | entire j =>
      simpa only [row,err,kindShift,Finset.sum_const_zero,add_zero] using
        (hE j).2 s (lt_of_le_of_lt hBE hs)
  refine ⟨B,err,(fun i => ER (Sum.inr i)),hη,ha,hr,?_,?_⟩
  · intro i M s hs
    apply (hR (Sum.inr i) M).1 s
    change BR-((M:ℝ)+1)<s.re
    linarith
  · intro i M s hs
    simpa only [ramanujanExtensionSpec,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one] using
      (hR (Sum.inr i) M).2 s (lt_of_le_of_lt hBR hs)
#print axioms family_with_ramanujan_extension_at_sign
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
end
end
