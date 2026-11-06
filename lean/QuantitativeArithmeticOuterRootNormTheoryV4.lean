module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Consolidated chapter: QuantitativeArithmeticOuterRootNorm. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticOuterRootNormV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticOuterRootNorm
open Complex

/-- A small disk about a negative real center forces the geometric
inequalities needed in the level-35 physical prime-power obstruction. -/
theorem negative_disk_bounds (u : ℂ) (c : ℝ)
    (hc : 397/80≤c) (hc' : c≤15/2) (hu : ‖u+(c:ℂ)‖<1/16) :
    ‖u‖<8 ∧ 27<‖u^2-(5/2:ℂ)*u-2‖ := by
  have hcre : (u+(c:ℂ)).re≤‖u+(c:ℂ)‖ := re_le_norm _
  have hneg : u.re< -(49/10:ℝ) := by
    simp only [add_re,ofReal_re] at hcre
    linarith
  have huupper := norm_sub_le (u+(c:ℂ)) (c:ℂ)
  have hcn : ‖(c:ℂ)‖=c := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  rw [add_sub_cancel_right,hcn] at huupper
  have hulo : (49/10:ℝ)<‖u‖ := by
    have h := (abs_le.mp (Complex.abs_re_le_norm u)).1
    linarith
  have hvlo : (74/10:ℝ)<‖u-(5/2:ℂ)‖ := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (u-(5/2:ℂ)))).1
    norm_num at h
    linarith
  have hmul : (49/10:ℝ)*(74/10)<‖u*(u-(5/2:ℂ))‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg u,norm_nonneg (u-(5/2:ℂ))]
  have hy := norm_sub_norm_le (u*(u-(5/2:ℂ))) (2:ℂ)
  have he : u*(u-(5/2:ℂ))-2=u^2-(5/2:ℂ)*u-2 := by ring
  rw [he] at hy
  norm_num at hy hmul
  exact ⟨by linarith,by linarith⟩

/-- Lower bound for one approximate root factor, normalized at radius R. -/
theorem root_factor_lower (u z : ℂ) (R c : ℝ)
    (hR : 0<R) (hu : R≤‖u‖) (hc : 0≤c) (hz : ‖z‖≤c) :
    (1-c/R)*‖u‖≤‖u-z‖ := by
  have hratio : c≤(c/R)*‖u‖ := by
    have h := mul_le_mul_of_nonneg_left hu (div_nonneg hc hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using h
  have h := norm_sub_norm_le u z
  nlinarith

/-- A degree-six remainder bound outside the radius-four disk. -/
theorem polynomial_six_norm (c : Fin 7 → ℂ) (u : ℂ) (hu : 4≤‖u‖) :
    ‖∑ i : Fin 7, c i*u^(i:ℕ)‖≤
      ((∑ i : Fin 7, ‖c i‖*(4:ℝ)^(i:ℕ))/4096)*‖u‖^6 := by
  let t : ℝ := ‖u‖/4
  have ht : 1≤t := by dsimp [t]; linarith
  have he : ‖u‖=4*t := by dsimp [t]; ring
  have hterm (i : Fin 7) : ‖c i*u^(i:ℕ)‖≤(‖c i‖*4^(i:ℕ))*t^6 := by
    have hp : t^(i:ℕ)≤t^6 := pow_le_pow_right₀ ht (by omega)
    rw [norm_mul,norm_pow,he,mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg (c i))
      (pow_nonneg (by norm_num : (0:ℝ)≤4) (i:ℕ)))]
  calc
    ‖∑ i : Fin 7, c i*u^(i:ℕ)‖≤∑ i : Fin 7, ‖c i*u^(i:ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 7, (‖c i‖*4^(i:ℕ))*t^6 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [t]; ring

#print axioms polynomial_six_norm
#print axioms negative_disk_bounds
#print axioms root_factor_lower
end QuantitativeArithmeticOuterRootNorm
end
end

/-! ## QuantitativeArithmeticQuadraticOuterNormV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticOuterRootNorm
open Complex

/-- A real quadratic with conjugate roots of modulus at most c has an
explicit exterior-disk lower bound. -/
theorem quadratic_outer_lower (u : ℂ) (a b c : ℝ)
    (hu : 4≤‖u‖) (hd : a^2≤4*b) (hb : b≤c^2)
    (hc : 0≤c) (hc4 : c≤4) :
    (1-c/4)^2*‖u‖^2≤‖u^2+(a:ℂ)*u+(b:ℂ)‖ := by
  let d : ℝ := Real.sqrt (b-a^2/4)
  have hd2 : d^2=b-a^2/4 := Real.sq_sqrt (by nlinarith)
  let z : ℂ := ((-a/2:ℝ):ℂ)+(d:ℂ)*I
  let w : ℂ := ((-a/2:ℝ):ℂ)-(d:ℂ)*I
  have hz2 : ‖z‖^2=b := by
    have h := Complex.normSq_eq_norm_sq z
    norm_num [z,Complex.normSq] at h ⊢
    nlinarith
  have hw2 : ‖w‖^2=b := by
    have h := Complex.normSq_eq_norm_sq w
    norm_num [w,Complex.normSq] at h ⊢
    nlinarith
  have hz : ‖z‖≤c := by nlinarith [norm_nonneg z]
  have hw : ‖w‖≤c := by nlinarith [norm_nonneg w]
  have hfac : (u-z)*(u-w)=u^2+(a:ℂ)*u+(b:ℂ) := by
    apply Complex.ext
    · norm_num [z,w,pow_two,Complex.mul_re,Complex.mul_im]
      nlinarith
    · norm_num [z,w,pow_two,Complex.mul_re,Complex.mul_im]
      ring
  have h1 := root_factor_lower u z 4 c (by norm_num) hu hc hz
  have h2 := root_factor_lower u w 4 c (by norm_num) hu hc hw
  have hn : 0≤(1-c/4)*‖u‖ := mul_nonneg (by linarith) (norm_nonneg u)
  have h := mul_le_mul h1 h2 hn (norm_nonneg (u-z))
  rw [← norm_mul,hfac] at h
  convert h using 1
  ring

#print axioms quadratic_outer_lower
end QuantitativeArithmeticOuterRootNorm
end
end
