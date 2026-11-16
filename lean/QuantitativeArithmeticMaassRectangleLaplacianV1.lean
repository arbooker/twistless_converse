module

public import QuantitativeArithmeticMaassRectangleGradientV1
public import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem smoothTransition_second_deriv_bounded :
    ∃ E : ℝ, 0≤E ∧ ∀ x, |deriv (deriv Real.smoothTransition) x|≤E := by
  have hc : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  obtain ⟨E,hE⟩ := smoothTransition_deriv_compact.deriv.exists_bound_of_continuous
    (hc.continuous_deriv (by simp))
  exact ⟨E,(norm_nonneg _).trans (hE 0),fun x => by
    simpa only [Real.norm_eq_abs] using hE x⟩

theorem innerIntervalCutoff_second_deriv (a b h x : ℝ) :
    deriv (deriv (innerIntervalCutoff a b h)) x =
      (deriv (deriv Real.smoothTransition) ((x-a)/h)*Real.smoothTransition ((b-x)/h)-
        2*deriv Real.smoothTransition ((x-a)/h)*deriv Real.smoothTransition ((b-x)/h)+
        Real.smoothTransition ((x-a)/h)*deriv (deriv Real.smoothTransition) ((b-x)/h))/h^2 := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd (t : ℝ) := (hs.differentiable (by simp) t).hasDerivAt
  have hdd (t : ℝ) :=
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) t).hasDerivAt
  have ha := ((hasDerivAt_id x).sub_const a).div_const h
  have hb := ((hasDerivAt_const x b).sub (hasDerivAt_id x)).div_const h
  have h1 := (hd ((x-a)/h)).comp x ha
  have h2 := (hd ((b-x)/h)).comp x hb
  have h3 := ((hdd ((x-a)/h)).comp x ha).div_const h
  have h4 := ((hdd ((b-x)/h)).comp x hb).div_const h
  have he : deriv (innerIntervalCutoff a b h) = fun t =>
      deriv Real.smoothTransition ((t-a)/h)/h*Real.smoothTransition ((b-t)/h)-
      Real.smoothTransition ((t-a)/h)*(deriv Real.smoothTransition ((b-t)/h)/h) :=
    funext (innerIntervalCutoff_deriv a b h)
  rw [he]
  convert ((h3.mul h2).sub (h1.mul h4)).deriv using 1
  · congr 1
  · dsimp only [Function.comp_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
    ring

theorem innerIntervalCutoff_second_deriv_bound (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hDb : ∀ x, |deriv Real.smoothTransition x|≤D)
    (hEb : ∀ x, |deriv (deriv Real.smoothTransition) x|≤E)
    (a b h x : ℝ) (hh : 0<h) :
    |deriv (deriv (innerIntervalCutoff a b h)) x|≤(2*E+2*D^2)/h^2 := by
  rw [innerIntervalCutoff_second_deriv,abs_div,abs_of_pos (sq_pos_of_pos hh)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  have hleft : |deriv (deriv Real.smoothTransition) ((x-a)/h)*
      Real.smoothTransition ((b-x)/h)|≤E := by
    rw [abs_mul,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_mul_of_nonneg_right (hEb _) (Real.smoothTransition.nonneg _)).trans
      (mul_le_of_le_one_right hE (Real.smoothTransition.le_one _))
  have hright : |Real.smoothTransition ((x-a)/h)*
      deriv (deriv Real.smoothTransition) ((b-x)/h)|≤E := by
    rw [abs_mul,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hEb _) (Real.smoothTransition.nonneg _)).trans
      (mul_le_of_le_one_left hE (Real.smoothTransition.le_one _))
  have hmiddle : |2*deriv Real.smoothTransition ((x-a)/h)*
      deriv Real.smoothTransition ((b-x)/h)|≤2*D^2 := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hm := mul_le_mul (hDb ((x-a)/h)) (hDb ((b-x)/h)) (abs_nonneg _) hD
    nlinarith
  have ht := (abs_add_le
    (deriv (deriv Real.smoothTransition) ((x-a)/h)*Real.smoothTransition ((b-x)/h)-
      2*deriv Real.smoothTransition ((x-a)/h)*deriv Real.smoothTransition ((b-x)/h))
    (Real.smoothTransition ((x-a)/h)*deriv (deriv Real.smoothTransition) ((b-x)/h))).trans
    (add_le_add (abs_sub _ _) le_rfl)
  linarith

theorem rectangleCutoff_XX (l r a b h x y : ℝ) :
    X (X (rectangleCutoffFunction l r a b h)) (x,y)=
      ((deriv (deriv (innerIntervalCutoff l r h)) x*innerIntervalCutoff a b h y : ℝ):ℂ) := by
  have hs : ContDiffOn ℝ ∞ (X (rectangleCutoffFunction l r a b h)) univ :=
    dir_contDiffOn (rectangleCutoffFunction_smooth l r a b h).contDiffOn isOpen_univ e₁
  rw [X_eq_deriv hs isOpen_univ (mem_univ _)]
  simp_rw [rectangleCutoff_X]
  exact ((((contDiff_infty_iff_deriv.mp (innerIntervalCutoff_smooth l r h)).2.differentiable
    (by simp) x).hasDerivAt).mul_const (innerIntervalCutoff a b h y)).ofReal_comp.deriv

theorem rectangleCutoff_YY (l r a b h x y : ℝ) :
    Y (Y (rectangleCutoffFunction l r a b h)) (x,y)=
      ((innerIntervalCutoff l r h x*deriv (deriv (innerIntervalCutoff a b h)) y : ℝ):ℂ) := by
  have hs : ContDiffOn ℝ ∞ (Y (rectangleCutoffFunction l r a b h)) univ :=
    dir_contDiffOn (rectangleCutoffFunction_smooth l r a b h).contDiffOn isOpen_univ e₂
  rw [Y_eq_deriv hs isOpen_univ (mem_univ _)]
  simp_rw [rectangleCutoff_Y]
  exact ((((contDiff_infty_iff_deriv.mp (innerIntervalCutoff_smooth a b h)).2.differentiable
    (by simp) y).hasDerivAt).const_mul (innerIntervalCutoff l r h x)).ofReal_comp.deriv

/-- Uniform second-order cost for the actual rectangle seed, with the
transition bounds separated from all geometric parameters. -/
theorem rectangleSmoothSeed_laplacian_quantitative (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hDb : ∀ x, |deriv Real.smoothTransition x|≤D)
    (hEb : ∀ x, |deriv (deriv Real.smoothTransition) x|≤E)
    (l r a b h : ℝ) (ha : 0<a) (hh : 0<h)
    (z : ℍ) (hz : z∈upperRectangle l r a b) :
    ‖upperLaplacian (rectangleSmoothSeed l r a b h ha hh).toFun z‖ ≤
      4*(E+D^2)*b^2/h^2 := by
  let u := rectangleCutoffFunction l r a b h
  have hs : ContDiffOn ℝ ∞ u univ := (rectangleCutoffFunction_smooth l r a b h).contDiffOn
  have hxx : ‖X (X u) (z.re,z.im)‖≤(2*E+2*D^2)/h^2 := by
    rw [rectangleCutoff_XX,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (innerIntervalCutoff_bounds a b h z.im).1]
    exact (mul_le_mul_of_nonneg_right
      (innerIntervalCutoff_second_deriv_bound D E hD hE hDb hEb l r h z.re hh)
      (innerIntervalCutoff_bounds a b h z.im).1).trans
      (mul_le_of_le_one_right (by positivity) (innerIntervalCutoff_bounds a b h z.im).2)
  have hyy : ‖Y (Y u) (z.re,z.im)‖≤(2*E+2*D^2)/h^2 := by
    rw [rectangleCutoff_YY,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (innerIntervalCutoff_bounds l r h z.re).1]
    exact (mul_le_mul_of_nonneg_left
      (innerIntervalCutoff_second_deriv_bound D E hD hE hDb hEb a b h z.im hh)
      (innerIntervalCutoff_bounds l r h z.re).1).trans
      (mul_le_of_le_one_left (by positivity) (innerIntervalCutoff_bounds l r h z.re).2)
  have he : euclidean u (z.re,z.im)=X (X u) (z.re,z.im)+Y (Y u) (z.re,z.im) := by
    rw [XX_eq_deriv hs isOpen_univ (mem_univ _),YY_eq_deriv hs isOpen_univ (mem_univ _)]
    rfl
  change ‖hyperbolic u (z.re,z.im)‖≤_
  rw [hyperbolic,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg _),he]
  have hsum := (norm_add_le _ _).trans (add_le_add hxx hyy)
  have hb : 0≤b := z.im_pos.le.trans hz.2.2
  calc
    z.im^2*‖X (X u) (z.re,z.im)+Y (Y u) (z.re,z.im)‖
      ≤ b^2*((2*E+2*D^2)/h^2+(2*E+2*D^2)/h^2) :=
      mul_le_mul (pow_le_pow_left₀ z.im_pos.le hz.2.2 2) hsum (norm_nonneg _) (sq_nonneg _)
    _ = 4*(E+D^2)*b^2/h^2 := by ring

/-- A single universal constant works for every rectangle and collar. -/
theorem rectangleSmoothSeed_laplacian_uniform :
    ∃ C : ℝ, 0≤C ∧ ∀ (l r a b h : ℝ) (ha : 0<a) (hh : 0<h)
      (z : ℍ), z∈upperRectangle l r a b →
      ‖upperLaplacian (rectangleSmoothSeed l r a b h ha hh).toFun z‖≤C*b^2/h^2 := by
  obtain ⟨D,hD,hDb⟩ := smoothTransition_deriv_bounded
  obtain ⟨E,hE,hEb⟩ := smoothTransition_second_deriv_bounded
  exact ⟨4*(E+D^2),by positivity,fun l r a b h ha hh z hz =>
    rectangleSmoothSeed_laplacian_quantitative D E hD hE hDb hEb l r a b h ha hh z hz⟩

/-- Outside the rectangle the Laplacian vanishes, so the same bound is global. -/
theorem rectangleSmoothSeed_laplacian_global :
    ∃ C : ℝ, 0≤C ∧ ∀ (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) (z : ℍ),
      ‖upperLaplacian (rectangleSmoothSeed l r a b h ha hh).toFun z‖≤C*b^2/h^2 := by
  obtain ⟨C,hC,hbound⟩ := rectangleSmoothSeed_laplacian_uniform
  refine ⟨C,hC,?_⟩
  intro l r a b h ha hh z
  by_cases hz : z∈upperRectangle l r a b
  · exact hbound l r a b h ha hh z hz
  · have hzero : upperLaplacian (rectangleSmoothSeed l r a b h ha hh).toFun z=0 := by
      by_contra hn
      exact hz (rectangleSmoothSeed_support l r a b h ha hh
        (upperLaplacian_support _ hn))
    rw [hzero,norm_zero]
    positivity

#print axioms rectangleSmoothSeed_laplacian_global
#print axioms smoothTransition_second_deriv_bounded
#print axioms innerIntervalCutoff_second_deriv_bound
#print axioms rectangleSmoothSeed_laplacian_quantitative
#print axioms rectangleSmoothSeed_laplacian_uniform

end QuantitativeMaass
