module
public import QuantitativeArithmeticSmallLevelTwentySevenStagedObservationLinkV1
public import QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStagesClosureV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

/-- The checked generic chart works at every nonzero value of a, including
both a=1 and a=-1. The only remaining exclusions concern x. -/
theorem nonzero_parameter_reconstruction (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (ha : a≠0)
    (hm : x-1≠0) (hp : x+1≠0) (hq : a*x+x^2-1≠0) :
    stagedLeftMatrix x y z w a b c*sourceMatrix x y z w a b c=
      QuantitativeArithmeticSmallLevelTwentySevenObservation.basisMatrix := by
  apply staged_basis_reconstruction x y z w a b c hx hy hz hw
  intro n hn
  exact all_leading_nonzero x y z w a b c hx hy hz hw ha hm hp hq n hn

theorem large_x_avoids_pivots (x a : ℂ) (hlarge : ‖a‖+2<‖x‖) :
    x≠0 ∧ x-1≠0 ∧ x+1≠0 ∧ a*x+x^2-1≠0 := by
  have hbig : 1<‖x‖ := by have := norm_nonneg a; linarith
  have hx : x≠0 := by intro h; norm_num [h] at hbig
  have hm : x-1≠0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he,norm_one] at hbig
    exact (lt_irrefl 1) hbig
  have hp : x+1≠0 := by
    intro h
    have he : x= -1 := by linear_combination h
    rw [he,norm_neg,norm_one] at hbig
    exact (lt_irrefl 1) hbig
  refine ⟨hx,hm,hp,?_⟩
  intro hq
  have he : x^2=1-a*x := by linear_combination hq
  have hn := norm_sub_le (1:ℂ) (a*x)
  rw [← he,norm_pow,norm_one,norm_mul] at hn
  have hprod := mul_pos (show 0<‖x‖ by linarith) (show 0<‖x‖-‖a‖-2 by linarith)
  nlinarith

theorem large_x_reconstruction (x y z w a b c : ℂ)
    (hy : y≠0) (hz : z≠0) (hw : w≠0) (ha : a≠0) (hlarge : ‖a‖+2<‖x‖) :
    stagedLeftMatrix x y z w a b c*sourceMatrix x y z w a b c=
      QuantitativeArithmeticSmallLevelTwentySevenObservation.basisMatrix := by
  obtain ⟨hx,hm,hp,hq⟩ := large_x_avoids_pivots x a hlarge
  exact nonzero_parameter_reconstruction x y z w a b c hx hy hz hw ha hm hp hq
#print axioms nonzero_parameter_reconstruction
#print axioms large_x_reconstruction
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
