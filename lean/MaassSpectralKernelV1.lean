module

public import MaassKBesselComparisonV1
public import MaassExceptionalComparisonV1
public import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

@[expose] public section

namespace MaassSpectral

/-- Exactly the permitted principal and exceptional spectral parameters.
The exceptional endpoint is excluded; no Selberg restriction is made. -/
inductive Parameter
  | principal (r : ℝ)
  | exceptional (τ : ℝ) (hτ : |τ| < 1/2)

noncomputable def parameter : Parameter → ℂ
  | .principal r => r
  | .exceptional τ _ => Complex.I * (τ : ℂ)

noncomputable def order (p : Parameter) : ℂ := Complex.I * parameter p

noncomputable def eigenvalue : Parameter → ℝ
  | .principal r => 1/4 + r^2
  | .exceptional τ _ => 1/4 - τ^2

noncomputable def K : Parameter → ℝ → ℝ
  | .principal r => MaassKBessel.K r
  | .exceptional τ _ => MaassExceptional.K τ

noncomputable def W (p : Parameter) (x : ℝ) : ℝ := Real.sqrt x * K p x

theorem eigenvalue_pos (p : Parameter) : 0 < eigenvalue p := by
  cases p with
  | principal r => dsimp [eigenvalue]; positivity
  | exceptional τ hτ => exact MaassExceptional.exceptional_eigenvalue_pos hτ

theorem order_sq (p : Parameter) : order p ^ 2 = (1/4 - (eigenvalue p : ℂ)) := by
  cases p with
  | principal r =>
    simp only [order, parameter, eigenvalue, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow, mul_pow, Complex.I_sq]
    ring
  | exceptional τ hτ =>
    simp only [order, parameter, eigenvalue, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow, ← mul_assoc, Complex.I_mul_I]
    ring

theorem W_pos (p : Parameter) {x : ℝ} (hx : 0 < x) (hthreshold : eigenvalue p ≤ x^2) :
    0 < W p x := by
  cases p with
  | principal r =>
    exact MaassKBessel.W_pos r hx (by simpa only [eigenvalue, add_comm] using hthreshold)
  | exceptional τ hτ =>
    exact MaassExceptional.W_pos (by linarith : |τ| ≤ 1) hx

/-- Common two-sided comparison on the whole allowed spectral domain. -/
theorem W_ratio (p : Parameter) {a x y : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hthreshold : eigenvalue p ≤ (1-a^2)*x^2) (hxy : x ≤ y) :
    Real.exp (-(y-x)) ≤ W p y / W p x ∧
      W p y / W p x ≤ Real.exp (-a*(y-x)) := by
  cases p with
  | principal r =>
    exact MaassKBessel.W_ratio r ha ha1 hx
      (by simpa only [eigenvalue, add_comm] using hthreshold) hxy
  | exceptional τ hτ =>
    exact MaassExceptional.W_ratio hτ ha ha1 hx hthreshold hxy

/-- The exceptional eigenvalue bound underlying a uniform cutoff. -/
theorem exceptional_eigenvalue_le {τ : ℝ} (hτ : |τ| < 1/2) :
    eigenvalue (.exceptional τ hτ) ≤ 1/4 := by
  dsimp [eigenvalue]
  nlinarith [sq_nonneg τ]

#print axioms order_sq
#print axioms W_pos
#print axioms W_ratio

end MaassSpectral
