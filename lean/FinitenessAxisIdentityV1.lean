module

public import FinitenessOriginalFourierV1
public import FinitenessComplexGeometryV1
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

set_option autoImplicit false

namespace FinitenessAxisIdentity

open Complex Set Metric

def upper : Set ℂ := {z | 0 < z.im}

theorem upper_open : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

/-- Agreement on the positive imaginary axis determines holomorphic
functions on the entire upper half-plane. The accumulating points and
connectedness are supplied, not left as hypotheses. -/
theorem eq_of_axis {F G : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    (hG : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ G z)
    (he : ∀ y : ℝ, 0 < y → F ((y : ℂ)*I)=G ((y : ℂ)*I)) :
    ∀ z : ℂ, 0 < z.im → F z=G z := by
  have hFa : AnalyticOnNhd ℂ F upper :=
    (show DifferentiableOn ℂ F upper from fun z hz => (hF z hz).differentiableWithinAt).analyticOnNhd upper_open
  have hGa : AnalyticOnNhd ℂ G upper :=
    (show DifferentiableOn ℂ G upper from fun z hz => (hG z hz).differentiableWithinAt).analyticOnNhd upper_open
  have hc : I ∈ closure ({z | F z=G z} \ {I}) := by
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    refine ⟨((1+δ/2 : ℝ):ℂ)*I, ?_, ?_⟩
    · constructor
      · exact he (1+δ/2) (by linarith)
      · intro hi
        have hz : (((1+δ/2 : ℝ):ℂ)*I)=I := Set.mem_singleton_iff.mp hi
        have hh := congrArg Complex.im hz
        simp only [mul_I_im, ofReal_re, I_im] at hh
        linarith
    · rw [dist_eq_norm]
      have hz : I-(((1+δ/2 : ℝ):ℂ)*I)=(((-δ/2 : ℝ):ℂ))*I := by push_cast; ring
      rw [hz, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith : -δ/2 < 0)]
      linarith
  exact hFa.eqOn_of_preconnected_of_mem_closure hGa
    (convex_halfSpace_im_gt 0).isPreconnected (by simp [upper]) hc

/-- The transformation in the target law is holomorphic on the upper
half-plane and stays within it. -/
theorem reflected_holomorphic {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w => F (-1/((L : ℂ)*w))) z := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have hden : (L : ℂ)*z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hL.ne') hz0
  exact (hF _ (FinitenessComplexGeometry.reflected_im_pos hL hz)).comp z
    ((differentiableAt_const _).div ((differentiableAt_const _).mul differentiableAt_id) hden)

/-- A cleared-denominator Fricke identity on the axis extends throughout
the upper half-plane, for every integer weight. -/
theorem fricke_of_axis {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    {L : ℝ} (hL : 0 < L) (k : ℕ) (χ : ℂ)
    (he : ∀ y : ℝ, 0 < y →
      (((Real.sqrt L : ℝ):ℂ)*((y : ℂ)*I))^k*F ((y : ℂ)*I)=
        χ*F (-1/((L : ℂ)*((y : ℂ)*I)))) :
    ∀ z : ℂ, 0 < z.im → (((Real.sqrt L : ℝ):ℂ)*z)^k*F z=
      χ*F (-1/((L : ℂ)*z)) := by
  apply eq_of_axis _ _ he
  · intro z hz
    exact (((differentiableAt_const _).mul differentiableAt_id).pow k).mul (hF z hz)
  · intro z hz
    exact (differentiableAt_const _).mul (reflected_holomorphic hF hL hz)

#print axioms eq_of_axis
#print axioms fricke_of_axis

end FinitenessAxisIdentity
