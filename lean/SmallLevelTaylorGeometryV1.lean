module

public import SmallLevelFourierBoundaryBoundV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Set Metric FinitenessPolynomialSeries FinitenessFourierConstruction

theorem one_add_re_lower {u : ℂ} (hu : ‖u‖≤1/2) : (1:ℝ)/2≤(1+u).re := by
  have h := (neg_abs_le u.re).trans' (neg_le_neg (abs_re_le_norm u))
  simp only [Complex.add_re,Complex.one_re]
  linarith

theorem one_add_ne_zero {u : ℂ} (hu : ‖u‖≤1/2) : 1+u≠0 := by
  intro he
  have h := one_add_re_lower hu
  rw [he] at h
  norm_num at h

theorem one_add_inv_re_lower {u : ℂ} (hu : ‖u‖≤1/2) :
    (1:ℝ)/8≤((1+u)⁻¹).re := by
  have hnorm : ‖1+u‖≤2 := by
    have h := norm_add_le (1:ℂ) u
    rw [norm_one] at h
    linarith
  have hpos : 0<Complex.normSq (1+u) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr (one_add_ne_zero hu)) 2
  rw [Complex.inv_re]
  apply (le_div_iff₀ hpos).mpr
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [one_add_re_lower hu,norm_nonneg (1+u)]

theorem one_add_inv_norm_le {u : ℂ} (hu : ‖u‖≤1/2) : ‖(1+u)⁻¹‖≤2 := by
  have hn : (1:ℝ)/2≤‖1+u‖ :=
    (one_add_re_lower hu).trans (re_le_norm _)
  rw [norm_inv]
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hn
  simpa only [one_div,inv_inv] using h

/-- The deformation appearing after Fricke inversion, with c=ell*r^2 and
u=i*y/r. The auxiliary complex variable u is independent of the height y. -/
def deformPoint (β c y : ℝ) (u : ℂ) : ℂ :=
  (β:ℂ)+((y/c:ℝ):ℂ)*I/(1+u)

theorem deformPoint_im (β c y : ℝ) (u : ℂ) :
    (deformPoint β c y u).im=(y/c)*((1+u)⁻¹).re := by
  change ((β:ℂ)+((y/c:ℝ):ℂ)*I*(1+u)⁻¹).im=_
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,
    zero_mul,sub_zero,mul_one,add_zero]

theorem deformPoint_height (β : ℝ) {c y : ℝ} (hc : 0<c) (hy : 0<y)
    {u : ℂ} (hu : ‖u‖≤1/2) : y/(8*c)≤(deformPoint β c y u).im := by
  rw [deformPoint_im]
  calc
    y/(8*c)=(y/c)*(1/8) := by ring
    _≤_ := mul_le_mul_of_nonneg_left (one_add_inv_re_lower hu) (div_pos hy hc).le

theorem deformPoint_positive (β : ℝ) {c y : ℝ} (hc : 0<c) (hy : 0<y)
    {u : ℂ} (hu : ‖u‖≤1/2) : 0<(deformPoint β c y u).im :=
  lt_of_lt_of_le (by positivity) (deformPoint_height β hc hy hu)

theorem deformPoint_analytic (β c y : ℝ) {u : ℂ} (hu : ‖u‖≤1/2) :
    AnalyticAt ℂ (deformPoint β c y) u := by
  unfold deformPoint
  fun_prop (disch := exact one_add_ne_zero hu)

def deformed (k : ℕ) (a : ℕ → ℂ) (β c y : ℝ) (u : ℂ) : ℂ :=
  ((1+u)^k)⁻¹*fourier a (deformPoint β c y u)

theorem deformed_analytic (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (β : ℝ) {c y : ℝ} (hc : 0<c) (hy : 0<y) {u : ℂ} (hu : ‖u‖≤1/2) :
    AnalyticAt ℂ (deformed k a β c y) u := by
  have hf : AnalyticAt ℂ (fourier a) (deformPoint β c y u) :=
    (show DifferentiableOn ℂ (fourier a) {z : ℂ | 0<z.im} from
      fun z hz => (FinitenessFourierConstruction.holomorphic ha hz).differentiableWithinAt).analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_im) _ (deformPoint_positive β hc hy hu)
  exact (by fun_prop (disch := exact pow_ne_zero k (one_add_ne_zero hu)) :
    AnalyticAt ℂ (fun u : ℂ => ((1+u)^k)⁻¹) u).mul
      (hf.comp (deformPoint_analytic β c y hu))

#print axioms one_add_inv_re_lower
#print axioms one_add_inv_norm_le
#print axioms deformPoint_height
#print axioms deformPoint_analytic
#print axioms deformed_analytic

end SmallLevelTaylor
