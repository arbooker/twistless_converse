module
public import QuantitativeArithmeticSmallLevelThirtyThreeLeadingLinearV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix

def fullLeadingMatrix (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix GridSource (Fin 66) ℂ :=
  (leadingLinearMap m f ε s).toMatrix'

def fullShiftMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix GridSource (Fin 66) ℂ :=
  (shiftLinearMap m f ε n s).toMatrix'

theorem fullLeadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (i : GridSource) (j : Fin 66) (z : ℂ) :
    AnalyticAt ℂ (fun s => fullLeadingMatrix m f ε s i j) z := by
  simp only [fullLeadingMatrix,LinearMap.toMatrix'_apply]
  exact leadingRows_analytic m f ε (Pi.single j 1) i z

theorem fullShiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ)
    (i : GridSource) (j : Fin 66) (z : ℂ) :
    AnalyticAt ℂ (fun s => fullShiftMatrix m f ε n s i j) z := by
  simp only [fullShiftMatrix,LinearMap.toMatrix'_apply]
  exact shiftRows_analytic m f ε n (Pi.single j 1) i z

theorem fullLeadingMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 66→ℂ) :
    fullLeadingMatrix m f ε s *ᵥ v=gridLeadingRows m f ε s v := by
  rw [fullLeadingMatrix,LinearMap.toMatrix'_mulVec]
  rfl

theorem fullShiftMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 66→ℂ) : fullShiftMatrix m f ε n s *ᵥ v=gridShiftRows m f ε n s v := by
  rw [fullShiftMatrix,LinearMap.toMatrix'_mulVec]
  rfl

#print axioms fullLeadingMatrix_mulVec
#print axioms fullShiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
