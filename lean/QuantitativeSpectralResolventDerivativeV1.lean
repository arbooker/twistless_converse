module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralResolventDerivative

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- The noncommutative algebra behind differentiating the compact-parameter
logarithm integrand. No commutativity of the perturbation is required. -/
theorem resolvent_derivative_algebra (A V : R) (t : ℝ)
    (hu : IsUnit (1+t • (A-1))) :
    V * Ring.inverse (1+t • (A-1)) + (A-1) *
      (-(Ring.inverse (1+t • (A-1)) * (t • V) * Ring.inverse (1+t • (A-1)))) =
    Ring.inverse (1+t • (A-1)) * V * Ring.inverse (1+t • (A-1)) := by
  let B := Ring.inverse (1+t • (A-1))
  have hb : B + t • ((A-1)*B) = 1 := by
    have h := Ring.mul_inverse_cancel (1+t • (A-1)) hu
    simpa only [add_mul, one_mul, smul_mul_assoc] using h
  have he : 1-t • ((A-1)*B) = B := (eq_sub_of_add_eq hb).symm
  change V*B+(A-1)*(-(B*(t • V)*B)) = B*V*B
  calc
    V*B+(A-1)*(-(B*(t • V)*B)) = (1-t • ((A-1)*B))*V*B := by
      simp only [mul_neg, mul_smul_comm, smul_mul_assoc, sub_mul, one_mul,
        mul_assoc]
      simp only [sub_eq_add_neg]
    _ = B*V*B := by rw [he]

/-- Actual derivative of the logarithm's resolvent integrand along any
differentiable path in a real Banach algebra. The inverse is required only
at the point of differentiation. -/
theorem hasDerivAt_resolvent_integrand {G : ℝ → R} {V : R} {s : ℝ}
    (hG : HasDerivAt G V s) (t : ℝ)
    (hu : IsUnit (1+t • (G s-1))) :
    HasDerivAt (fun x => (G x-1) * Ring.inverse (1+t • (G x-1)))
      (Ring.inverse (1+t • (G s-1)) * V * Ring.inverse (1+t • (G s-1))) s := by
  have h₁ : HasFDerivAt Ring.inverse _ (1+t • (G s-1)) :=
    hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h₂ : HasDerivAt (fun x => 1+t • (G x-1)) (t • V) s :=
    ((hG.sub_const 1).const_smul t).const_add 1
  have hinv : HasDerivAt (fun x => Ring.inverse (1+t • (G x-1)))
      (-(Ring.inverse (1+t • (G s-1)) * (t • V) * Ring.inverse (1+t • (G s-1)))) s := by
    simpa [hu.unit_spec, ← Ring.inverse_unit hu.unit] using! h₁.comp_hasDerivAt s h₂
  have h := (hG.sub_const 1).mul hinv
  rwa [resolvent_derivative_algebra (G s) V t hu] at h

#print axioms resolvent_derivative_algebra
#print axioms hasDerivAt_resolvent_integrand

end QuantitativeSpectralResolventDerivative
