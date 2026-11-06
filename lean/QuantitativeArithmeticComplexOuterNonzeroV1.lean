module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexOuterNonzero
open Complex

/-- A small multiple of X+1 cannot equal a larger multiple of Y outside
the unit disk when the modulus of Y is at least that of X. -/
theorem linear_nonzero (X Y : ℂ) (u v : ℝ)
    (hX : 1≤‖X‖) (hXY : ‖X‖≤‖Y‖) (hu : 0<u) (huv : 2*u<v) :
    (X+1)*(u:ℂ)-Y*(v:ℂ)≠0 := by
  intro h
  have hv : 0<v := by linarith
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hu,abs_of_pos hv] at he
  have htri : ‖X+1‖≤‖X‖+1 := by simpa only [norm_one] using norm_add_le X (1:ℂ)
  have h1 := mul_le_mul_of_nonneg_right htri hu.le
  have h2 := mul_le_mul_of_nonneg_right hXY hv.le
  have h3 : (2*u)*‖X‖<v*‖X‖ := mul_lt_mul_of_pos_right huv (by linarith)
  nlinarith

/-- A positive real quadratic with 0<b<c<a has both roots strictly
inside the unit disk. The proof uses its real and imaginary parts. -/
theorem quadratic_nonzero (X : ℂ) (a b c : ℝ)
    (hX : 1≤‖X‖) (hb : 0<b) (hbc : b<c) (hca : c<a) :
    (a:ℂ)*X^2+(b:ℂ)*X+(c:ℂ)≠0 := by
  intro h
  have hc : 0<c := lt_trans hb hbc
  have ha : 0<a := lt_trans hc hca
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  norm_num [Complex.mul_re,Complex.mul_im,pow_two] at hr hi
  have him : X.im*(2*a*X.re+b)=0 := by nlinarith [hi]
  have hn : ‖X‖^2=X.re^2+X.im^2 := by
    have ht := Complex.normSq_eq_norm_sq X
    norm_num [Complex.normSq] at ht
    nlinarith
  rcases mul_eq_zero.mp him with hzero|hlinear
  · rw [hzero] at hr
    have hd : b^2<4*a*c := by nlinarith
    have hs := sq_nonneg (2*a*X.re+b)
    have he : (2*a*X.re+b)^2=b^2-4*a*c := by
      nlinarith [mul_eq_zero_of_left (show a*X.re^2+b*X.re+c=0 by nlinarith [hr]) (4*a)]
    nlinarith
  · have he : a*(X.re^2+X.im^2)=c := by nlinarith [hr]
    have hnorm : 1≤‖X‖^2 := by nlinarith [norm_nonneg X]
    have hmul := mul_le_mul_of_nonneg_left hnorm ha.le
    rw [hn,he] at hmul
    nlinarith

#print axioms linear_nonzero
#print axioms quadratic_nonzero
end QuantitativeArithmeticComplexOuterNonzero
