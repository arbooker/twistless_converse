module
public import SmallLevelTwentySixGridOriginalRowsV1
public import SmallLevelFiniteGridSupportV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
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
end SmallLevelTwentySixGrid
