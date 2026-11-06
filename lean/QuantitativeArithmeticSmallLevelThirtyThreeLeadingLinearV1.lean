module
public import QuantitativeArithmeticSmallLevelThirtyThreeShiftLinearV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelFiniteGridSupport SmallLevelPrimeRates

/-- The original leading equations form a linear map before any sign selection. -/
def leadingLinearMap (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) :
    (Fin 66→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := gridLeadingRows m f ε s
  map_add' v w := by
    funext i
    cases i <;>
      simp [gridLeadingRows,gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
        gridSample_add,mul_add,Finset.sum_add_distrib] <;> (try split) <;> (try simp only [←Finset.mul_sum]) <;> ring
  map_smul' c v := by
    funext i
    cases i <;>
      simp [gridLeadingRows,gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
        gridSample_smul,Finset.mul_sum,mul_left_comm] <;> (try split) <;> (try simp only [←Finset.mul_sum]) <;> ring

theorem leadingRows_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (v : Fin 66→ℂ) (i : GridSource) (z : ℂ) :
    AnalyticAt ℂ (fun s => gridLeadingRows m f ε s v i) z := by
  cases i with
  | word i =>
    unfold gridLeadingRows gridGroupLeading
    apply AnalyticAt.sub
    · exact analyticAt_const
    · exact (gridMatrixScalar_analytic m f _ i 0 z).mul analyticAt_const
  | taylor i =>
    unfold gridLeadingRows gridRamanujanLeading
    apply AnalyticAt.sub
    · exact analyticAt_const
    · exact (gridTaylorCoefficient_analytic m f ε i 0 z).mul analyticAt_const
  | entire i => exact analyticAt_const
  | infinity i => exact analyticAt_const
  | hecke i =>
    have hp : gridHeckeP i≠0 := (gridHeckeSpecs_valid i).1.ne_zero
    have hi := (parameter_analytic (gridHeckeP i) m hp z).inv
      (parameter_ne_zero (gridHeckeP i) m hp z)
    unfold gridLeadingRows gridHeckeLeading
    apply AnalyticAt.add
    · exact analyticAt_const.sub ((analyticAt_const.mul hi).mul analyticAt_const)
    · split
      · exact analyticAt_const
      · exact (hi.pow 2).mul analyticAt_const

#print axioms leadingRows_analytic
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
