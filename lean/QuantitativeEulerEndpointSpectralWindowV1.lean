module

public import QuantitativeEulerEndpointCutCalculusV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSpectralWindow
open ContinuousLinearMap QuantitativeSpectralCut QuantitativeEulerEndpointCutCalculus
open QuantitativeEulerEndpointHighInverse

/-- Continuous window between two strict spectral cuts. -/
def window (a b x : ℝ) : ℝ := (x-a)⁺*clippedInverse (b-a) (x-a)

theorem window_continuous {a b : ℝ} (hab : a<b) : Continuous (window a b) := by
  have hi : Continuous (fun x : ℝ => clippedInverse (b-a) (x-a)) :=
    (clippedInverse_continuous (sub_pos.mpr hab)).comp (continuous_id.sub continuous_const)
  exact (by fun_prop : Continuous (fun x : ℝ => (x-a)⁺)).mul hi

theorem window_nonneg {a b : ℝ} (hab : a<b) (x : ℝ) : 0≤window a b x := by
  exact mul_nonneg (by positivity) (inv_nonneg.mpr ((sub_pos.mpr hab).le.trans (le_max_left _ _)))

theorem window_le_one {a b : ℝ} (hab : a<b) (x : ℝ) : window a b x≤1 := by
  have hd : 0<max (b-a) (x-a) := (sub_pos.mpr hab).trans_le (le_max_left _ _)
  change (x-a)⁺*(max (b-a) (x-a))⁻¹≤1
  rw [← div_eq_mul_inv,div_le_one hd]
  exact max_le (le_max_right _ _) (le_of_lt hd)

theorem window_zero {a b x : ℝ} (hx : x≤a) : window a b x=0 := by
  simp [window,posPart_def,max_eq_right (sub_nonpos.mpr hx)]

theorem window_one {a b x : ℝ} (hab : a<b) (hx : b≤x) : window a b x=1 := by
  have hxa : 0<x-a := sub_pos.mpr (hab.trans_le hx)
  simp only [window,clippedInverse,posPart_def,max_eq_left hxa.le,
    max_eq_right (sub_le_sub_right hx a),mul_inv_cancel₀ hxa.ne']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous window lies between the actual high-cut projections.
The gap between thresholds is arbitrary and strictly positive. -/
theorem window_sandwich (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {a b : ℝ} (hab : a<b) :
    (highAt A b).starProjection≤cfc (window a b) A ∧
      cfc (window a b) A≤(highAt A a).starProjection := by
  have hf := window_continuous hab
  have hf0 : 0≤cfc (window a b) A := cfc_nonneg (fun x _ => window_nonneg hab x)
  have hf1 : cfc (window a b) A≤1 := by
    have hh := cfc_mono (a := A) (f := window a b) (g := fun _ : ℝ => 1)
      (fun x _ => window_le_one hab x) hf.continuousOn continuous_const.continuousOn
    simpa only [cfc_const_one ℝ A hA] using hh
  have hp (t : ℝ) : IsStarProjection ((highAt A t).starProjection) :=
    ⟨Submodule.isIdempotentElem_starProjection _,
      isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
  constructor
  · apply projection_le_of_fixed _ _ (hp b) hf0
    exact cfc_fixed_high A hA b (window a b) hf (fun _ _ hx => window_one hab hx.le)
  · apply le_projection_of_supported _ _ (hp a) hf0 hf1
    apply cfc_supported_high A hA a (window a b) (fun x => clippedInverse (b-a) (x-a)) hf
      ((clippedInverse_continuous (sub_pos.mpr hab)).comp (continuous_id.sub continuous_const))
    intro x _
    rfl

#print axioms window_continuous
#print axioms window_nonneg
#print axioms window_le_one
#print axioms window_zero
#print axioms window_one
#print axioms window_sandwich
end QuantitativeEulerEndpointSpectralWindow
