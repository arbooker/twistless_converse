module

public import Mathlib.Tactic
public import SmallLevelTwentySixPhysicalModulusTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic

/-- The extra quadratic component in the second sign family has squared
modulus eight. This proof uses exact real and imaginary parts. -/
theorem norm_sq_of_quadratic (z : ℂ) (hz : z^2-5*z+8=0) : ‖z‖^2=8 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
  have hne : z.im≠0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg (2*z.re-5)]
  have hr5 : 2*z.re=5 := by
    have hprod : z.im*(2*z.re-5)=0 := by nlinarith [hi]
    have := (mul_eq_zero.mp hprod).resolve_left hne
    linarith
  rw [Complex.sq_norm]
  change z.re*z.re+z.im*z.im=8
  nlinarith [hr]

/-- The extra component Y=9 is incompatible with physical prime powers,
including a reflected prime-two parameter. -/
theorem no_physical_quadratic (h z : ℂ)
    (hz : z^2-5*z+8=0)
    (hx : ‖z‖^2=‖(2:ℂ)^h‖^2)
    (hy : (9:ℂ)^h=9) : False := by
  have hx8 : ‖(2:ℂ)^h‖^2=8 := hx.symm.trans (norm_sq_of_quadratic z hz)
  have hy81 : ‖(9:ℂ)^h‖^2=(81:ℝ) := by rw [hy]; norm_num
  rcases SmallLevelTwentySixPhysicalModulus.physical_bounds h with H|H
  · rw [hx8,hy81] at H
    norm_num at H
  · rw [hx8] at H
    norm_num at H

#print axioms norm_sq_of_quadratic
#print axioms no_physical_quadratic
end QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticParametersV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic
open SmallLevelPrimeRates

/-- Exclude the extra quadratic component directly at the actual signed
prime-power parameters. Both signs are covered, without a norm premise. -/
theorem no_signed_parameter_quadratic (m : ℕ) (s u : ℂ)
    (hu : u = 1 ∨ u = -1)
    (hx : (u * parameter 2 m s)^2 - 5*(u * parameter 2 m s) + 8 = 0)
    (hy : (parameter 3 m s)^2 = 9) : False := by
  apply no_physical_quadratic (s-(m:ℂ)) (u*parameter 2 m s) hx
  · rcases hu with rfl | rfl <;> simp [parameter]
  · have h := Complex.natCast_mul_natCast_cpow 3 3 (s-(m:ℂ))
    norm_num only [Nat.cast_ofNat, show (3:ℂ)*3=9 by norm_num] at h
    have h9 : (9:ℂ)^(s-(m:ℂ)) = (parameter 3 m s)^2 := by
      simpa [parameter, pow_two] using h
    exact h9.trans hy

#print axioms no_signed_parameter_quadratic
end QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic
end
end
