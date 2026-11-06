module

public import FinitenessBoundaryDecayV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessMellinContour

open Complex MeasureTheory FinitenessFiniteOrder FinitenessBoundaryDecay

noncomputable def kernel (F : ℂ → ℂ) (l : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-l : ℝ)*z)*F z

noncomputable def integral (F : ℂ → ℂ) (σ l : ℝ) : ℂ :=
  ∫ t : ℝ, kernel F l ((σ : ℂ)+(t : ℂ)*I)

theorem kernel_norm (F : ℂ → ℂ) (l : ℝ) (z : ℂ) :
    ‖kernel F l z‖ = Real.exp (-l*z.re)*‖F z‖ := by
  simp only [kernel, norm_mul, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero]

theorem kernel_rapid {F : ℂ → ℂ} {σ : ℝ} (hF : Rapid F σ) (l : ℝ) :
    Rapid (kernel F l) σ := by
  apply of_norm_le hF (Real.exp_pos (-l*σ)).le
  intro z hz
  exact le_of_eq (by rw [kernel_norm, hz])

theorem kernel_bound {F : ℂ → ℂ} (hF : Bound F) (l : ℝ) : Bound (kernel F l) :=
  FinitenessFiniteOrder.mul (exp_linear (-l)) hF

theorem kernel_holomorphic {F : ℂ → ℂ} (hF : Differentiable ℂ F) (l : ℝ) :
    Differentiable ℂ (kernel F l) :=
  (((differentiable_const ((-l : ℝ):ℂ)).mul differentiable_id).cexp).mul hF

theorem integral_eq {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b : ℝ} (hab : a < b) (ha : Rapid F a) (hb : Rapid F b) (l : ℝ) :
    integral F a l=integral F b l :=
  contour_eq (kernel_holomorphic hhol l) (kernel_bound hF l) hab
    (kernel_rapid ha l) (kernel_rapid hb l)

theorem integrable {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b : ℝ} (hab : a < b) (ha : Rapid F a) (hb : Rapid F b) (l : ℝ)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) : VerticalIntegrable (kernel F l) σ := by
  obtain ⟨C₀,C₂,h0,h2⟩ := strip_majorant (kernel_holomorphic hhol l) (kernel_bound hF l)
    hab (kernel_rapid ha l) (kernel_rapid hb l)
  exact FinitenessStripDecay.vertical_integrable (kernel_holomorphic hhol l).continuous
    h0 h2 hσa hσb

/-- Reflection of the completed entire function becomes the exact
inversion relation for its inverse Mellin integral (logarithmic variable). -/
theorem inversion {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {c κ : ℝ} (hc : κ-c < c) (hr : Rapid F c) {ε : ℂ} (hε : ‖ε‖=1)
    (hFE : ∀ z : ℂ, F z=ε*F ((κ : ℂ)-z)) (l : ℝ) :
    integral F c l = ε*Complex.exp ((-l*κ : ℝ):ℂ)*integral F c (-l) := by
  have hl := reflected hr hε hFE
  rw [← integral_eq hhol hF hc hl hr l]
  have he (t : ℝ) : kernel F l (((κ-c : ℝ):ℂ)+(t : ℂ)*I) =
      (ε*Complex.exp ((-l*κ : ℝ):ℂ))*kernel F (-l) ((c : ℂ)+((-t : ℝ):ℂ)*I) := by
    have hz : (κ : ℂ)-(((κ-c : ℝ):ℂ)+(t : ℂ)*I) =
        (c : ℂ)+((-t : ℝ):ℂ)*I := by push_cast; ring
    rw [kernel, hFE, hz, kernel]
    have hp : ((-l : ℝ):ℂ)*(((κ-c : ℝ):ℂ)+(t : ℂ)*I) =
        ((-l*κ : ℝ):ℂ)+(( -(-l) : ℝ):ℂ)*((c : ℂ)+((-t : ℝ):ℂ)*I) := by
      push_cast; ring
    rw [hp, Complex.exp_add]
    ring
  change (∫ t : ℝ, kernel F l (((κ-c : ℝ):ℂ)+(t : ℂ)*I)) = _
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact MeasureTheory.integral_neg_eq_self (fun t : ℝ => kernel F (-l) ((c : ℂ)+(t : ℂ)*I)) volume

theorem kernel_log {x : ℝ} (hx : 0 < x) (F : ℂ → ℂ) (z : ℂ) :
    kernel F (Real.log x) z=(x : ℂ)^(-z)*F z := by
  rw [kernel, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]
  congr 2
  push_cast
  ring

theorem mellinInv_eq {x : ℝ} (hx : 0 < x) (F : ℂ → ℂ) (σ : ℝ) :
    mellinInv σ F x=(1/(2*Real.pi):ℝ) • integral F σ (Real.log x) := by
  unfold mellinInv integral
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [kernel_log hx, smul_eq_mul]

theorem mellin_inversion {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {c κ : ℝ} (hc : κ-c < c) (hr : Rapid F c) {ε : ℂ} (hε : ‖ε‖=1)
    (hFE : ∀ z : ℂ, F z=ε*F ((κ : ℂ)-z)) {x : ℝ} (hx : 0 < x) :
    mellinInv c F x = ε*(x : ℂ)^(-(κ : ℂ))*mellinInv c F (x⁻¹) := by
  rw [mellinInv_eq hx, mellinInv_eq (inv_pos.mpr hx), Real.log_inv,
    inversion hhol hF hc hr hε hFE]
  have he : Complex.exp ((-Real.log x*κ : ℝ):ℂ)=(x : ℂ)^(-(κ : ℂ)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]
    congr 1
    push_cast
    ring
  rw [he, Complex.real_smul, Complex.real_smul]
  ring

#print axioms integral_eq
#print axioms integrable
#print axioms inversion
#print axioms mellin_inversion

end FinitenessMellinContour
