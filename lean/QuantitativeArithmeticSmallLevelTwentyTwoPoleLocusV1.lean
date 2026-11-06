module

public import QuantitativeArithmeticSmallLevelTwentyTwoChiFiveV1
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex

/-- Every possible pole of the quadratic continuation lies on the
critical line Re(s)=m. This uses the actual ramified Euler sign. -/
theorem denominator_zero_re (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {s : ℂ}
    (hs : denominator m f s=0) : s.re=(m:ℝ) := by
  have hmult : ‖QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2‖=(2:ℝ)^m := by
    rcases QuantitativeArithmeticRamifiedFullTrace.multiplier_simple hf.toEulerData
      (by decide : Nat.Prime 2) (by decide : 2∣22) (by decide : ¬2^2∣22) m with h|h <;>
      simp [h,norm_pow]
  have he : heckeScalar m f s= -1 := eq_neg_of_add_eq_zero_left hs
  have hn:=congrArg norm he
  rw [heckeScalar,norm_mul,hmult] at hn
  have hp : ‖(2:ℂ)^(-s)‖=(2:ℝ)^(-s.re) := by
    simpa using norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (-s)
  rw [hp] at hn
  norm_num only [norm_neg,norm_one] at hn
  have hr : (2:ℝ)^((m:ℝ)-s.re)=(2:ℝ)^(0:ℝ) := by
    rw [sub_eq_add_neg,Real.rpow_add (by norm_num),Real.rpow_natCast]
    simpa using hn
  have hh:=(Real.rpow_right_inj (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp hr
  linarith

/-- The possible-pole denominator has a nonzero derivative at every zero.
In particular its zeros are simple, independently of all eigenvalues. -/
theorem denominator_derivative_at_zero (m : ℕ) (f : ℕ→ℂ) {s : ℂ}
    (hs : denominator m f s=0) : HasDerivAt (denominator m f) (Complex.log 2) s := by
  have he : heckeScalar m f s= -1 := eq_neg_of_add_eq_zero_left hs
  have hh:=(((hasDerivAt_id s).neg).const_cpow
    (Or.inl (by norm_num : (2:ℂ)≠0))).const_mul
      (QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2)
  have hg:=hh.add_const 1
  convert hg using 1
  · rfl
  · change Complex.log 2=QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2*
      ((2:ℂ)^(-s)*Complex.log 2*(-1))
    change QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2*(2:ℂ)^(-s)= -1 at he
    rw [show QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2*
      ((2:ℂ)^(-s)*Complex.log 2*(-1))=
      -(QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2*(2:ℂ)^(-s))*Complex.log 2 by ring,
      he]
    ring

#print axioms denominator_zero_re
#print axioms denominator_derivative_at_zero
end QuantitativeArithmeticSmallLevelTwentyTwo
