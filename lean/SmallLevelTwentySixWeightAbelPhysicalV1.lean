module
public import SmallLevelFourPrimePowerSumTheoryV4
public import SmallLevelTwentySixWeightAbelMMMPPV1
public import SmallLevelTwentySixWeightAbelMMMPMV1
public import SmallLevelTwentySixWeightAbelMMMMPV1
public import SmallLevelTwentySixWeightAbelMMMMMV1
public import SmallLevelTwentySixWeightAbelMMPPPV1
public import SmallLevelTwentySixWeightAbelMMPPMV1
public import SmallLevelTwentySixWeightAbelMMPMPV1
public import SmallLevelTwentySixWeightAbelMMPMMV1
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixWeightAbelPhysical
open Complex QuantitativeArithmeticSparsePolynomialCertificate SmallLevelFourPrimePowerSum
theorem mmm_nonzero (sx sz : ℤ) (n : ℕ)
    (hx : sx=1 ∨ sx= -1) (hz : sz=1 ∨ sz= -1)
    (hn : if sx=1 then 2≤n else 1≤n) :
    eval ((sx:ℂ)*(2:ℂ)^n) ((9:ℂ)^n) ((sz:ℂ)*(13:ℂ)^n) ((25:ℂ)^n) 1
      SmallLevelTwentySixWeightAbelMMM.terms≠0 := by
  rcases hx with rfl|rfl <;> rcases hz with rfl|rfl
  · exact physical_eval_ne_zero (1) (1) (1) n SmallLevelTwentySixWeightAbelMMM.terms
      (SmallLevelTwentySixWeightAbelMMM.PP.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (1) (-1) (-1) n SmallLevelTwentySixWeightAbelMMM.terms
      (SmallLevelTwentySixWeightAbelMMM.PM.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (-1) (1) (-1) n SmallLevelTwentySixWeightAbelMMM.terms
      (SmallLevelTwentySixWeightAbelMMM.MP.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (-1) (-1) (1) n SmallLevelTwentySixWeightAbelMMM.terms
      (SmallLevelTwentySixWeightAbelMMM.MM.power_sum_nonzero n (by simpa using hn))

#print axioms mmm_nonzero

theorem mmp_nonzero (sx sz : ℤ) (n : ℕ)
    (hx : sx=1 ∨ sx= -1) (hz : sz=1 ∨ sz= -1)
    (hn : if sx=1 then 2≤n else 1≤n) :
    eval ((sx:ℂ)*(2:ℂ)^n) ((9:ℂ)^n) ((sz:ℂ)*(13:ℂ)^n) ((25:ℂ)^n) 1
      SmallLevelTwentySixWeightAbelMMP.terms≠0 := by
  rcases hx with rfl|rfl <;> rcases hz with rfl|rfl
  · exact physical_eval_ne_zero (1) (1) (1) n SmallLevelTwentySixWeightAbelMMP.terms
      (SmallLevelTwentySixWeightAbelMMP.PP.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (1) (-1) (-1) n SmallLevelTwentySixWeightAbelMMP.terms
      (SmallLevelTwentySixWeightAbelMMP.PM.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (-1) (1) (-1) n SmallLevelTwentySixWeightAbelMMP.terms
      (SmallLevelTwentySixWeightAbelMMP.MP.power_sum_nonzero n (by simpa using hn))
  · exact physical_eval_ne_zero (-1) (-1) (1) n SmallLevelTwentySixWeightAbelMMP.terms
      (SmallLevelTwentySixWeightAbelMMP.MM.power_sum_nonzero n (by simpa using hn))

#print axioms mmp_nonzero

end SmallLevelTwentySixWeightAbelPhysical
