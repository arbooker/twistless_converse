module

public import QuantitativeSpectralLogResolventV1
public import QuantitativeSpectralResolventDerivativeV1

set_option autoImplicit false
@[expose] public section

open MeasureTheory Set

namespace QuantitativeSpectralTraceResolvent

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- Every affine resolvent denominator on the compact logarithm interval
is invertible for a strictly positive selfadjoint operator. -/
theorem affine_isUnit (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsUnit (1+t • (A-1)) := by
  have hu := isUnit_cfc (fun r : ℝ => 1+t*(r-1)) A (by fun_prop) hA
    (fun r hr => (QuantitativeSpectralLogResolvent.affine_pos (hpos r hr) ht).ne')
  have hn : cfc (fun r : ℝ => r-1) A = A-1 := by
    rw [cfc_sub (fun r : ℝ => r) (fun _ => 1) A, cfc_id' ℝ A, cfc_const_one ℝ A]
  rw [cfc_const_add 1 (fun r : ℝ => t*(r-1)) A,
    cfc_const_mul t (fun r : ℝ => r-1) A, hn, map_one] at hu
  exact hu

/-- Continuity of the actual affine resolvent throughout the compact interval. -/
theorem continuousOn_resolvent (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    ContinuousOn (fun t : ℝ => Ring.inverse (1+t • (A-1))) (Icc 0 1) := by
  intro t ht
  have hi : ContinuousAt Ring.inverse (1+t • (A-1)) :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) (affine_isUnit A hA hpos ht).unit).continuousAt
  have ha : ContinuousAt (fun u : ℝ => 1+u • (A-1)) t := by fun_prop
  exact (hi.comp (f := fun u : ℝ => 1+u • (A-1)) ha).continuousWithinAt

/-- Compact-interval integrability of the actual operator resolvent square. -/
theorem integrable_resolvent_sq (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    IntegrableOn (fun t : ℝ => Ring.inverse (1+t • (A-1))^2) (Icc 0 1) :=
  ((continuousOn_resolvent A hA hpos).pow 2).integrableOn_Icc

/-- The noncommutative resolvent derivative is Bochner integrable. -/
theorem integrable_resolvent_sandwich (A V : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    IntegrableOn (fun t : ℝ =>
      Ring.inverse (1+t • (A-1))*V*Ring.inverse (1+t • (A-1))) (Icc 0 1) :=
  (((continuousOn_resolvent A hA hpos).mul continuousOn_const).mul
    (continuousOn_resolvent A hA hpos)).integrableOn_Icc

/-- Cyclicity turns the integrated derivative of the resolvent logarithm
into the expected inverse-times-perturbation trace. This uses an actual
bounded linear trace functional, rather than a determinant axiom. -/
theorem trace_integral_resolvent_sandwich (A V : 𝔄)
    (hA : IsSelfAdjoint A) (hpos : ∀ r ∈ spectrum ℝ A, 0 < r)
    (τ : (𝔄) →L[ℝ] ℝ)
    (hcyc : ∀ B C, τ (B*C) = τ (C*B)) :
    (∫ t in Icc (0 : ℝ) 1,
      τ (Ring.inverse (1+t • (A-1))*V*Ring.inverse (1+t • (A-1)))) =
      τ (Ring.inverse A*V) := by
  let L : (𝔄) →L[ℝ] ℝ :=
    τ.comp ((ContinuousLinearMap.mul ℝ (𝔄)).flip V)
  have he : ∀ B : 𝔄, τ (B*V*B) = L (B^2) := by
    intro B
    change τ ((B*V)*B) = τ (B^2*V)
    rw [hcyc (B*V) B, pow_two, mul_assoc]
  simp_rw [he]
  rw [L.integral_comp_comm (integrable_resolvent_sq A hA hpos),
    ← QuantitativeSpectralLogResolvent.operator_inverse_eq_integral_resolvent_sq A hA hpos]
  rfl

#print axioms affine_isUnit
#print axioms continuousOn_resolvent
#print axioms integrable_resolvent_sq
#print axioms integrable_resolvent_sandwich
#print axioms trace_integral_resolvent_sandwich

end QuantitativeSpectralTraceResolvent
