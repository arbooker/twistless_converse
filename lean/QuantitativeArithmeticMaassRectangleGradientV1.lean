module

public import QuantitativeArithmeticMaassRectangleSmoothingV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem innerIntervalCutoff_deriv (a b h x : ℝ) :
    deriv (innerIntervalCutoff a b h) x=
      deriv Real.smoothTransition ((x-a)/h)/h*Real.smoothTransition ((b-x)/h)-
      Real.smoothTransition ((x-a)/h)*(deriv Real.smoothTransition ((b-x)/h)/h) := by
  have hd (t : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).differentiable (by simp) t).hasDerivAt
  have h1 := (hd ((x-a)/h)).comp x (((hasDerivAt_id x).sub_const a).div_const h)
  have h2 := (hd ((b-x)/h)).comp x (((hasDerivAt_const x b).sub (hasDerivAt_id x)).div_const h)
  convert (h1.mul h2).deriv using 1
  · rfl
  · dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
    ring

/-- Only one universal bound for the transition derivative is needed. -/
theorem innerIntervalCutoff_deriv_bound (D : ℝ) (hD : 0≤D)
    (hDb : ∀ x, |deriv Real.smoothTransition x|≤D)
    (a b h x : ℝ) (hh : 0<h) :
    |deriv (innerIntervalCutoff a b h) x|≤2*D/h := by
  rw [innerIntervalCutoff_deriv]
  have h1 := Real.smoothTransition.nonneg ((x-a)/h)
  have h2 := Real.smoothTransition.nonneg ((b-x)/h)
  have h3 := Real.smoothTransition.le_one ((x-a)/h)
  have h4 := Real.smoothTransition.le_one ((b-x)/h)
  have hleft : |deriv Real.smoothTransition ((x-a)/h)/h*Real.smoothTransition ((b-x)/h)|≤D/h := by
    rw [abs_mul,abs_div,abs_of_pos hh,abs_of_nonneg h2]
    exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hDb _) hh.le) h2).trans
      (mul_le_of_le_one_right (div_nonneg hD hh.le) h4)
  have hright : |Real.smoothTransition ((x-a)/h)*(deriv Real.smoothTransition ((b-x)/h)/h)|≤D/h := by
    rw [abs_mul,abs_div,abs_of_pos hh,abs_of_nonneg h1]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hDb _) hh.le) h1).trans
      (mul_le_of_le_one_left (div_nonneg hD hh.le) h3)
  have he := abs_sub
    (deriv Real.smoothTransition ((x-a)/h)/h*Real.smoothTransition ((b-x)/h))
    (Real.smoothTransition ((x-a)/h)*(deriv Real.smoothTransition ((b-x)/h)/h))
  rw [mul_div_assoc]
  linarith

theorem rectangleCutoff_X (l r a b h x y : ℝ) :
    X (rectangleCutoffFunction l r a b h) (x,y)=
      ((deriv (innerIntervalCutoff l r h) x*innerIntervalCutoff a b h y : ℝ):ℂ) := by
  rw [X_eq_deriv (rectangleCutoffFunction_smooth l r a b h).contDiffOn isOpen_univ (mem_univ _)]
  exact (((innerIntervalCutoff_smooth l r h).differentiable (by simp) x).hasDerivAt.mul_const
    (innerIntervalCutoff a b h y)).ofReal_comp.deriv

theorem rectangleCutoff_Y (l r a b h x y : ℝ) :
    Y (rectangleCutoffFunction l r a b h) (x,y)=
      ((innerIntervalCutoff l r h x*deriv (innerIntervalCutoff a b h) y : ℝ):ℂ) := by
  rw [Y_eq_deriv (rectangleCutoffFunction_smooth l r a b h).contDiffOn isOpen_univ (mem_univ _)]
  exact (((innerIntervalCutoff_smooth a b h).differentiable (by simp) y).hasDerivAt.const_mul
    (innerIntervalCutoff l r h x)).ofReal_comp.deriv

/-- Quantitative hyperbolic gradient cost of the actual rectangular
smoothing. The bound is uniform as the rectangle and collar vary. -/
theorem rectangleSmoothSeed_gradient_quantitative (D : ℝ) (hD : 0≤D)
    (hDb : ∀ x, |deriv Real.smoothTransition x|≤D)
    (l r a b h : ℝ) (ha : 0<a) (hh : 0<h)
    (z : ℍ) (hz : z∈upperRectangle l r a b) :
    (upperEnergy (rectangleSmoothSeed l r a b h ha hh).toFun
      (rectangleSmoothSeed l r a b h ha hh).toFun z).re ≤ (4*b*D/h)^2 := by
  have hb : 0<b := z.im_pos.trans_le hz.2.2
  have hx : ‖X (rectangleCutoffFunction l r a b h) (z.re,z.im)‖≤2*D/h := by
    rw [rectangleCutoff_X,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (innerIntervalCutoff_bounds a b h z.im).1]
    exact (mul_le_mul_of_nonneg_right (innerIntervalCutoff_deriv_bound D hD hDb l r h z.re hh)
      (innerIntervalCutoff_bounds a b h z.im).1).trans
      (mul_le_of_le_one_right (by positivity) (innerIntervalCutoff_bounds a b h z.im).2)
  have hy : ‖Y (rectangleCutoffFunction l r a b h) (z.re,z.im)‖≤2*D/h := by
    rw [rectangleCutoff_Y,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (innerIntervalCutoff_bounds l r h z.re).1]
    exact (mul_le_mul_of_nonneg_left (innerIntervalCutoff_deriv_bound D hD hDb a b h z.im hh)
      (innerIntervalCutoff_bounds l r h z.re).1).trans
      (mul_le_of_le_one_left (by positivity) (innerIntervalCutoff_bounds l r h z.re).2)
  change (hyperbolicEnergy (rectangleCutoffFunction l r a b h)
    (rectangleCutoffFunction l r a b h) (z.re,z.im)).re≤_
  rw [hyperbolicEnergy_self_eq]
  have hxs := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hys := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hzs := pow_le_pow_left₀ z.im_pos.le hz.2.2 2
  calc
    z.im^2*(‖X (rectangleCutoffFunction l r a b h) (z.re,z.im)‖^2+
        ‖Y (rectangleCutoffFunction l r a b h) (z.re,z.im)‖^2)
      ≤ b^2*((2*D/h)^2+(2*D/h)^2) :=
      mul_le_mul hzs (add_le_add hxs hys) (by positivity) (by positivity)
    _ = 8*(b*D/h)^2 := by ring
    _ ≤ 16*(b*D/h)^2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    _ = (4*b*D/h)^2 := by ring

#print axioms innerIntervalCutoff_deriv_bound
#print axioms rectangleSmoothSeed_gradient_quantitative

end QuantitativeMaass
