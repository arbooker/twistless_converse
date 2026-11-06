module

public import MaassExceptionalODEV1
public import MaassSqrtBoundaryV1
public import MaassODELowerComparisonV1

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassExceptional

theorem moment_nonneg (j : ℕ) (τ x : ℝ) : 0 ≤ moment j τ x := by
  apply integral_nonneg
  intro r
  positivity

theorem moment_le_at_one (j : ℕ) {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 1 ≤ x) :
    moment j τ x ≤ moment j τ 1 := by
  apply integral_mono (moment_integrable j hτ (lt_of_lt_of_le zero_lt_one hx))
    (moment_integrable j hτ zero_lt_one)
  intro r
  apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [Real.cosh_pos r]

noncomputable def k₁ (τ x : ℝ) := -moment 1 τ x
noncomputable def k₂ (τ x : ℝ) := moment 2 τ x
noncomputable def W (τ : ℝ) := MaassSqrtRescaling.W (K τ)
noncomputable def W₁ (τ : ℝ) := MaassSqrtRescaling.W₁ (K τ) (k₁ τ)
noncomputable def W₂ (τ : ℝ) := MaassSqrtRescaling.W₂ (K τ) (k₁ τ) (k₂ τ)

theorem k₁_hasDerivAt {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (k₁ τ) (k₂ τ x) x := by
  convert (moment_hasDerivAt 1 hτ hx).neg using 1
  · rfl
  · simp [k₂]

theorem W_hasDerivAt {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (W τ) (W₁ τ x) x :=
  MaassSqrtRescaling.W_hasDerivAt hx (K_hasDerivAt hτ hx)

theorem W₁_hasDerivAt {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    HasDerivAt (W₁ τ) (W₂ τ x) x :=
  MaassSqrtRescaling.W₁_hasDerivAt hx (K_hasDerivAt hτ hx) (k₁_hasDerivAt hτ hx)

theorem W_ode {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) :
    W₂ τ x = (1 - (1/4-τ^2)/x^2) * W τ x := by
  apply MaassSqrtRescaling.rescaled_ode hx
  dsimp [k₁, k₂]
  nlinarith [moment_ode hτ hx]

theorem W_pos {τ x : ℝ} (hτ : |τ| ≤ 1) (hx : 0 < x) : 0 < W τ x :=
  mul_pos (Real.sqrt_pos.mpr hx) (K_pos hτ hx)

theorem W_boundary_tendsto {τ a : ℝ} (hτ : |τ| ≤ 1) (ha : 0 < a) :
    Tendsto (fun x => Real.exp (-a*x) * (W₁ τ x + a*W τ x)) atTop (𝓝 0) := by
  let C := moment 0 τ 1 + moment 1 τ 1
  apply MaassSqrtRescaling.weighted_boundary_tendsto (K τ) (k₁ τ) ha
    (show 0 ≤ C from add_nonneg (moment_nonneg 0 τ 1) (moment_nonneg 1 τ 1))
  · intro x hx
    change |moment 0 τ x| ≤ C
    rw [abs_of_nonneg (moment_nonneg 0 τ x)]
    exact (moment_le_at_one 0 hτ hx).trans (le_add_of_nonneg_right (moment_nonneg 1 τ 1))
  · intro x hx
    change |-moment 1 τ x| ≤ C
    rw [abs_neg, abs_of_nonneg (moment_nonneg 1 τ x)]
    exact (moment_le_at_one 1 hτ hx).trans (le_add_of_nonneg_left (moment_nonneg 0 τ 1))

theorem exceptional_eigenvalue_pos {τ : ℝ} (hτ : |τ| < 1/2) : 0 < 1/4-τ^2 := by
  have hh := abs_lt.mp hτ
  nlinarith [sq_nonneg (τ-1/2), sq_nonneg (τ+1/2)]

/-- The w.tex lower bound for the actual exceptional Bessel integral.
No ODE, positivity, decay or derivative hypotheses are assumed. -/
theorem W_lower {τ x y : ℝ} (hτ : |τ| < 1/2) (hx : 0 < x) (hxy : x ≤ y) :
    Real.exp (-(y-x)) * W τ x ≤ W τ y := by
  have ht : |τ| ≤ 1 := by linarith
  apply MaassODEComparison.w_lower_comparison (W τ) (W₁ τ) (W₂ τ) x
    (1/4-τ^2) (exceptional_eigenvalue_pos hτ).le
    (fun z hz => W_hasDerivAt ht (hx.trans_le hz))
    (fun z hz => W₁_hasDerivAt ht (hx.trans_le hz))
    (fun z hz => (W_pos ht (hx.trans_le hz)).le)
    (fun z hz => W_ode ht (hx.trans_le hz))
    (by simpa using W_boundary_tendsto ht (show (0:ℝ)<1 by norm_num))
    le_rfl hxy

/-- Actual upper comparison beyond the linear transition. The threshold
is written without square roots: lambda ≤ (1-a²)x². -/
theorem W_upper {τ a x y : ℝ} (hτ : |τ| < 1/2) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hthreshold : 1/4-τ^2 ≤ (1-a^2)*x^2) (hxy : x ≤ y) :
    W τ y ≤ Real.exp (-a*(y-x)) * W τ x := by
  have ht : |τ| ≤ 1 := by linarith
  have ha2 : 0 ≤ 1-a^2 := by nlinarith
  apply MaassODEComparison.exponential_comparison (W τ) (W₁ τ) (W₂ τ) x a
    (fun z hz => W_hasDerivAt ht (hx.trans_le hz))
    (fun z hz => W₁_hasDerivAt ht (hx.trans_le hz)) _
    (W_boundary_tendsto ht ha) le_rfl hxy
  intro z hz
  rw [W_ode ht (hx.trans_le hz)]
  have hz2 : 0 < z^2 := sq_pos_of_pos (hx.trans_le hz)
  have hsq : x^2 ≤ z^2 := by nlinarith [show x ≤ z from hz]
  have hd : (1/4-τ^2)/z^2 ≤ 1-a^2 :=
    (div_le_iff₀ hz2).mpr (hthreshold.trans
      (mul_le_mul_of_nonneg_left hsq ha2))
  exact mul_le_mul_of_nonneg_right (by linarith) (W_pos ht (hx.trans_le hz)).le

/-- Two-sided ratio estimate for the actual exceptional kernel. -/
theorem W_ratio {τ a x y : ℝ} (hτ : |τ| < 1/2) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hthreshold : 1/4-τ^2 ≤ (1-a^2)*x^2) (hxy : x ≤ y) :
    Real.exp (-(y-x)) ≤ W τ y / W τ x ∧
      W τ y / W τ x ≤ Real.exp (-a*(y-x)) := by
  have ht : |τ| ≤ 1 := by linarith
  exact ⟨(le_div_iff₀ (W_pos ht hx)).mpr (W_lower hτ hx hxy),
    (div_le_iff₀ (W_pos ht hx)).mpr (W_upper hτ ha ha1 hx hthreshold hxy)⟩

#print axioms W_ode
#print axioms W_boundary_tendsto
#print axioms W_lower
#print axioms W_ratio

end MaassExceptional
