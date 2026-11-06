module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridOriginalRowsV1
public import SmallLevelFiniteGridSupportV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelFiniteGridSupport

/-- Every positive Taylor shift is a linear map on the additive grid. -/
def shiftLinearMap (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 66→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := gridShiftRows m f ε n s
  map_add' v w := by
    funext i
    cases i <;> simp [gridShiftRows,gridSample_add,mul_add]
  map_smul' c v := by
    funext i
    cases i <;> simp [gridShiftRows,gridSample_smul,mul_left_comm]

theorem shiftRows_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ)
    (v : Fin 66→ℂ) (i : GridSource) (z : ℂ) :
    AnalyticAt ℂ (fun s => gridShiftRows m f ε n s v i) z := by
  cases i with
  | word i => exact (gridMatrixScalar_analytic m f _ i (n+1) z).mul analyticAt_const
  | taylor i => exact (gridTaylorCoefficient_analytic m f ε i (n+1) z).mul analyticAt_const
  | entire i => exact analyticAt_const
  | hecke i => exact analyticAt_const
  | infinity i => exact analyticAt_const

#print axioms shiftRows_analytic
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
