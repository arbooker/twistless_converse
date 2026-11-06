module
public import QuantitativeArithmeticSmallLevelTwentySevenPoleExtraDataBundleV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftFactorsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
open Matrix QuantitativeArithmeticSmallLevelTwentySevenObservation QuantitativeArithmeticSmallLevelTwentySevenShiftSource
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def ramanujanSpec : Fin 4 → QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ![extraSpec0,extraSpec1,extraSpec10,extraSpec11]
def ramanujanObservation : Fin 4 → Fin 553 := ![extraObservation0,extraObservation1,extraObservation10,extraObservation11]
theorem ramanujan_valid (i : Fin 4) : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (ramanujanSpec i) := by
  fin_cases i
  · exact extraValid0
  · exact extraValid1
  · exact extraValid10
  · exact extraValid11
theorem ramanujan_observed (v : ℕ → ℂ) (i : Fin 4) :
    QuantitativeArithmeticRationalRows.eval v (observation (ramanujanObservation i))=
      QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval (ramanujanSpec i).q (ramanujanSpec i).right v := by
  fin_cases i
  · exact extraObserved0 v
  · exact extraObserved1 v
  · exact extraObserved10 v
  · exact extraObserved11 v
def ramanujanCoefficient (i : Fin 4) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  SmallLevelTaylor.taylorRowScalar (2*m) (Nat.lcm 27 ((ramanujanSpec i).q^2))
    (((ramanujanSpec i).t:ℝ)/(ramanujanSpec i).Q) η (n+1) s

theorem ramanujan_shift_factor (i : Fin 4) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift (ramanujanSpec i) m η n s v=
      ramanujanCoefficient i m η n s*(factorMatrix *ᵥ basisValues v) (ramanujanObservation i) := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
  rw [← ramanujan_observed v i,observation_basis]
  rfl

theorem ramanujan_coefficient_analytic (i : Fin 4) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (ramanujanCoefficient i m η n) s := by
  have hv := ramanujan_valid i
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<27) (pow_pos hv.2.1 2)
  · exact div_ne_zero (by exact_mod_cast hv.2.2.2.1) (by exact_mod_cast hv.1.ne')
#print axioms ramanujan_shift_factor
#print axioms ramanujan_coefficient_analytic
end QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
