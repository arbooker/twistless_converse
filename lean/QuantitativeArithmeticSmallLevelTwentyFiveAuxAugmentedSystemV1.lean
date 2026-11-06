module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridRowSourcesV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridSourceRowV1
public import QuantitativeArithmeticRectangularContinuationTheoryV4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix
variable {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]

/-- The extra coordinate rows fix the source-free gauge. -/
def augmentedLeading (rows : ρ → SourceRow) (free : κ → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 1050 → ℂ) : ρ ⊕ κ → ℂ :=
  Sum.elim (fun i => sourceLeading (rows i) m f ε s v) (fun j => v (free j))

def augmentedShifted (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 1050 → ℂ) : ρ ⊕ κ → ℂ :=
  Sum.elim (fun i => sourceShifted (rows i) m f ε n s v) (fun _ => 0)

private theorem source_add (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (v w : Fin 1050 → ℂ) : sourceLeading r m f ε s (v+w)=
      sourceLeading r m f ε s v+sourceLeading r m f ε s w := by
  cases r with
  | physical r => exact leading_add r m f ε s v w
  | old j => rfl

private theorem source_smul (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε s c : ℂ)
    (v : Fin 1050 → ℂ) : sourceLeading r m f ε s (c • v)=c*sourceLeading r m f ε s v := by
  cases r with
  | physical r => exact leading_smul r m f ε s c v
  | old j => rfl

private theorem source_shift_add (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (v w : Fin 1050 → ℂ) : sourceShifted r m f ε n s (v+w)=
      sourceShifted r m f ε n s v+sourceShifted r m f ε n s w := by
  cases r with
  | physical r => exact shifted_add r m f ε n s v w
  | old j => simp [sourceShifted]

private theorem source_shift_smul (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s c : ℂ) (v : Fin 1050 → ℂ) :
    sourceShifted r m f ε n s (c • v)=c*sourceShifted r m f ε n s v := by
  cases r with
  | physical r => exact shifted_smul r m f ε n s c v
  | old j => simp [sourceShifted]

def augmentedLeadingLinear (rows : ρ → SourceRow) (free : κ → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 1050 → ℂ) →ₗ[ℂ] (ρ ⊕ κ → ℂ) where
  toFun := augmentedLeading rows free m f ε s
  map_add' := by
    intro v w
    funext i
    cases i with
    | inl i => exact source_add (rows i) m f ε s v w
    | inr j => rfl
  map_smul' := by
    intro c v
    funext i
    cases i with
    | inl i => exact source_smul (rows i) m f ε s c v
    | inr j => rfl

def augmentedShiftedLinear (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 1050 → ℂ) →ₗ[ℂ] (ρ ⊕ κ → ℂ) where
  toFun := augmentedShifted rows m f ε n s
  map_add' := by
    intro v w
    funext i
    cases i with
    | inl i => exact source_shift_add (rows i) m f ε n s v w
    | inr j => simp [augmentedShifted]
  map_smul' := by
    intro c v
    funext i
    cases i with
    | inl i => exact source_shift_smul (rows i) m f ε n s c v
    | inr j => simp [augmentedShifted]

def augmentedMatrix (rows : ρ → SourceRow) (free : κ → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (ρ ⊕ κ) (Fin 1050) ℂ :=
  (augmentedLeadingLinear rows free m f ε s).toMatrix'

def augmentedShiftMatrix (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (ρ ⊕ κ) (Fin 1050) ℂ :=
  (augmentedShiftedLinear rows m f ε n s).toMatrix'

theorem augmentedMatrix_mulVec (rows : ρ → SourceRow) (free : κ → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 1050 → ℂ) :
    augmentedMatrix rows free m f ε s *ᵥ v=augmentedLeading rows free m f ε s v :=
  LinearMap.toMatrix'_mulVec _ _

theorem augmentedShiftMatrix_mulVec (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 1050 → ℂ) :
    augmentedShiftMatrix (κ := κ) rows m f ε n s *ᵥ v=augmentedShifted rows m f ε n s v :=
  LinearMap.toMatrix'_mulVec _ _

theorem augmentedMatrix_analytic (rows : ρ → SourceRow) (free : κ → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : ρ ⊕ κ) (j : Fin 1050) :
    AnalyticAt ℂ (fun z => augmentedMatrix rows free m f ε z i j) s := by
  change AnalyticAt ℂ (fun z => augmentedLeading rows free m f ε z (Pi.single j 1) i) s
  cases i with
  | inr i => exact analyticAt_const
  | inl i =>
    cases h : rows i with
    | physical r => simpa only [augmentedLeading,h,Sum.elim_inl,sourceLeading] using
        leading_analytic r m f ε (Pi.single j 1) s
    | old a => simpa only [augmentedLeading,h,Sum.elim_inl,sourceLeading] using
        (analyticAt_const (v := (Pi.single j (1:ℂ) : Fin 1050 → ℂ) ⟨7*a.val,by omega⟩) (x := s))

theorem augmentedShiftMatrix_analytic (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) (i : ρ ⊕ κ) (j : Fin 1050) :
    AnalyticAt ℂ (fun z => augmentedShiftMatrix rows m f ε n z i j) s := by
  change AnalyticAt ℂ (fun z => augmentedShifted rows m f ε n z (Pi.single j 1) i) s
  cases i with
  | inr i => exact analyticAt_const
  | inl i =>
    cases h : rows i with
    | physical r => simpa only [augmentedShifted,h,Sum.elim_inl,sourceShifted] using
        shifted_analytic r m f ε n (Pi.single j 1) s
    | old a => simpa only [augmentedShifted,h,Sum.elim_inl,sourceShifted] using
        (analyticAt_const (v := (0:ℂ)) (x := s))

#print axioms augmentedMatrix_analytic
#print axioms augmentedShiftMatrix_analytic
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
