module
public import Mathlib.Order.Fin.Basic
public import SmallLevelTwentySixUnitMMMKernelV1
public import SmallLevelTwentySixUnitMMMLinearBundleV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 7000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMM
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteGridSupport SmallLevelTwentySixContinuationMinorMMM

def sourceLinearMap (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 366→ℂ) where
  toFun := sourceRows X Y Z W a b
  map_add' v w := by
    funext i
    simp only [sourceRows,Pi.add_apply]
    split
    · exact congrFun ((partLinear0 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear1 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear2 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear3 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear4 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear5 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear6 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear7 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear8 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear9 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear10 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear11 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear12 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear13 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear14 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear15 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear16 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear17 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear18 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear19 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear20 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear21 X Y Z W a b).map_add v w) _
    · exact congrFun ((partLinear22 X Y Z W a b).map_add v w) _
    · simp
  map_smul' c v := by
    funext i
    simp only [sourceRows,Pi.smul_apply]
    split
    · exact congrFun ((partLinear0 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear1 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear2 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear3 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear4 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear5 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear6 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear7 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear8 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear9 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear10 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear11 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear12 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear13 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear14 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear15 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear16 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear17 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear18 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear19 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear20 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear21 X Y Z W a b).map_smul c v) _
    · exact congrFun ((partLinear22 X Y Z W a b).map_smul c v) _
    · simp

theorem sourceRows_analytic (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 366) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRows (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  unfold sourceRows
  split
  · exact part_analytic_0 m a b v _ z
  · exact part_analytic_1 m a b v _ z
  · exact part_analytic_2 m a b v _ z
  · exact part_analytic_3 m a b v _ z
  · exact part_analytic_4 m a b v _ z
  · exact part_analytic_5 m a b v _ z
  · exact part_analytic_6 m a b v _ z
  · exact part_analytic_7 m a b v _ z
  · exact part_analytic_8 m a b v _ z
  · exact part_analytic_9 m a b v _ z
  · exact part_analytic_10 m a b v _ z
  · exact part_analytic_11 m a b v _ z
  · exact part_analytic_12 m a b v _ z
  · exact part_analytic_13 m a b v _ z
  · exact part_analytic_14 m a b v _ z
  · exact part_analytic_15 m a b v _ z
  · exact part_analytic_16 m a b v _ z
  · exact part_analytic_17 m a b v _ z
  · exact part_analytic_18 m a b v _ z
  · exact part_analytic_19 m a b v _ z
  · exact part_analytic_20 m a b v _ z
  · exact part_analytic_21 m a b v _ z
  · exact part_analytic_22 m a b v _ z
  · exact analyticAt_const

theorem support_injective : Function.Injective support := by
  have hs : StrictMono support := Fin.strictMono_iff_lt_succ.mpr (by decide)
  exact hs.injective

def leadingMatrix (m : ℕ) (a b s : ℂ) : Matrix (Fin 366) (Fin 320) ℂ :=
  ((sourceLinearMap (parameter 2 m s) (parameter 3 m s) (parameter 13 m s)
    (parameter 5 m s) a b).comp (extension support)).toMatrix'

theorem leadingMatrix_analytic (m : ℕ) (a b : ℂ) (i : Fin 366) (j : Fin 320) (z : ℂ) :
    AnalyticAt ℂ (fun s => leadingMatrix m a b s i j) z := by
  simp only [leadingMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact sourceRows_analytic m a b (extension support (Pi.single j 1)) i z

/-- Uniform full column rank at some point of the exponential curve.
Both auxiliary Hecke parameters remain arbitrary complex numbers. -/
theorem leadingMatrix_kernel_exists (m : ℕ) (a b : ℂ) :
    ∃ s : ℂ, ∀ v : Fin 320→ℂ,leadingMatrix m a b s *ᵥ v=0 → v=0 := by
  obtain ⟨s,hs⟩:=SmallLevelTwentySixContinuationMinorMMM.minor_nonzero_on_curve a m
  refine ⟨s,?_⟩
  intro v hv
  apply matrix_kernel_of_support support support_injective _ ?_ v hv
  intro w hw
  apply source_kernel_zero _ _ _ _ a b
    (parameter_ne_zero 2 m (by decide) s) (parameter_ne_zero 3 m (by decide) s)
    (parameter_ne_zero 13 m (by decide) s) (parameter_ne_zero 5 m (by decide) s) w _ hs
  exact fun i => congrFun hw i

#print axioms leadingMatrix_analytic
#print axioms leadingMatrix_kernel_exists

end SmallLevelTwentySixUnitMMM
