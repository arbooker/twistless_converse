module
public import SmallLevelTwentySixGridLeadingLinearV1
public import SmallLevelTwentySixGridLeadingSupportV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM

/-- All370 original rows, on the common320-coordinate support. -/
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
end SmallLevelTwentySixGrid
