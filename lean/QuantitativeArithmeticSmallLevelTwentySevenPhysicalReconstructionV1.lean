module
public import QuantitativeArithmeticSmallLevelTwentySevenStagedNonzeroV1
public import QuantitativeArithmeticSmallLevelTwentySevenStagedMeromorphicV1
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open Complex

/-- The real shift is k/2 for the internal holomorphic Mellin coordinate. -/
def primeRate (p κ : ℝ) (s : ℂ) : ℂ := exp ((Real.log p:ℂ)*(s-(κ:ℂ)))

theorem primeRate_analytic (p κ : ℝ) (s : ℂ) : AnalyticAt ℂ (primeRate p κ) s :=
  (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp'

theorem primeRate_nonzero (p κ : ℝ) (s : ℂ) : primeRate p κ s≠0 := exp_ne_zero _

theorem primeRate_norm (p κ : ℝ) (s : ℂ) :
    ‖primeRate p κ s‖=Real.exp (Real.log p*(s.re-κ)) := by
  simp only [primeRate,Complex.norm_exp,Complex.mul_re,Complex.sub_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

def physicalLeft (κ : ℝ) (a b c : ℂ) (s : ℂ) : Matrix (Fin 321) (Fin 550) ℂ :=
  stagedLeftMatrix (primeRate 2 κ s) (primeRate 3 κ s) (primeRate 5 κ s) (primeRate 7 κ s) a b c

def physicalSource (κ : ℝ) (a b c : ℂ) (s : ℂ) : Matrix (Fin 550) (Fin 607) ℂ :=
  sourceMatrix (primeRate 2 κ s) (primeRate 3 κ s) (primeRate 5 κ s) (primeRate 7 κ s) a b c

theorem physical_left_meromorphic (κ : ℝ) (a b c : ℂ) (s : ℂ) (i : Fin 321) (j : Fin 550) :
    MeromorphicAt (fun t => physicalLeft κ a b c t i j) s :=
  staged_left_meromorphic _ _ _ _ _ _ _ s
    (primeRate_analytic 2 κ s).meromorphicAt (primeRate_analytic 3 κ s).meromorphicAt
    (primeRate_analytic 5 κ s).meromorphicAt (primeRate_analytic 7 κ s).meromorphicAt
    (MeromorphicAt.const a s) (MeromorphicAt.const b s) (MeromorphicAt.const c s) i j

theorem physical_reconstruction (κ : ℝ) (a b c : ℂ) (ha : a≠0) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      physicalLeft κ a b c s * physicalSource κ a b c s=
        QuantitativeArithmeticSmallLevelTwentySevenObservation.basisMatrix := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨κ+(‖a‖+2)/Real.log 2,?_⟩
  intro s hs
  have hd : (‖a‖+2)/Real.log 2<s.re-κ := by linarith
  have hm := (div_lt_iff₀ hl).mp hd
  have he := Real.add_one_le_exp (Real.log 2*(s.re-κ))
  have hlarge : ‖a‖+2<‖primeRate 2 κ s‖ := by
    rw [primeRate_norm]
    nlinarith
  exact large_x_reconstruction _ _ _ _ a b c
    (primeRate_nonzero 3 κ s) (primeRate_nonzero 5 κ s) (primeRate_nonzero 7 κ s) ha hlarge
#print axioms physical_left_meromorphic
#print axioms physical_reconstruction
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
