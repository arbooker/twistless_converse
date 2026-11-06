module
public import SmallLevelTwentySixGridShiftLinearV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix SmallLevelFiniteGridSupport SmallLevelPrimeRates

/-- The original leading equations form a linear map before any sign selection. -/
def leadingLinearMap (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) :
    (Fin 780→ℂ)→ₗ[ℂ](GridSource→ℂ) where
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
    (v : Fin 780→ℂ) (i : GridSource) (z : ℂ) :
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

def selectedLeadingLinearMap {r : ℕ} (J : Fin r→GridSource)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin r→ℂ) where
  toFun v i := gridLeadingRows m f ε s v (J i)
  map_add' v w := by
    funext i
    exact congrFun ((leadingLinearMap m f ε s).map_add v w) (J i)
  map_smul' c v := by
    funext i
    exact congrFun ((leadingLinearMap m f ε s).map_smul c v) (J i)

def restrictedLeadingMatrix {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin r) (Fin d) ℂ :=
  ((selectedLeadingLinearMap J m f ε s).comp (extension u)).toMatrix'

theorem restrictedLeadingMatrix_analytic {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin r) (j : Fin d) (z : ℂ) :
    AnalyticAt ℂ (fun s => restrictedLeadingMatrix J u m f ε s i j) z := by
  simp only [restrictedLeadingMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact leadingRows_analytic m f ε (extension u (Pi.single j 1)) (J i) z

theorem restrictedLeadingMatrix_mulVec {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 780)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin d→ℂ) (i : Fin r) :
    (restrictedLeadingMatrix J u m f ε s *ᵥ v) i=
      gridLeadingRows m f ε s (extension u v) (J i) := by
  rw [restrictedLeadingMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

#print axioms restrictedLeadingMatrix_analytic
#print axioms restrictedLeadingMatrix_mulVec
end SmallLevelTwentySixGrid
