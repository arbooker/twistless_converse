module

public import MaassKBesselEventualPosV1
public import MaassKBesselDecayV1
public import MaassODEPositivityV1
public import MaassODELowerComparisonV1

set_option autoImplicit false

@[expose] public section

open Set Filter
open scoped Topology

namespace MaassKBessel

noncomputable def k₁ (t x : ℝ) := -moment 1 t x
noncomputable def k₂ (t x : ℝ) := moment 2 t x
noncomputable def W (t : ℝ) := MaassSqrtRescaling.W (K t)
noncomputable def W₁ (t : ℝ) := MaassSqrtRescaling.W₁ (K t) (k₁ t)
noncomputable def W₂ (t : ℝ) := MaassSqrtRescaling.W₂ (K t) (k₁ t) (k₂ t)

theorem k₁_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (k₁ t) (k₂ t x) x := by
  convert (moment_hasDerivAt 1 t hx).neg using 1
  · rfl
  · simp [k₂]

theorem W_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (W t) (W₁ t x) x :=
  MaassSqrtRescaling.W_hasDerivAt hx (K_hasDerivAt t hx)

theorem W₁_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (W₁ t) (W₂ t x) x :=
  MaassSqrtRescaling.W₁_hasDerivAt hx (K_hasDerivAt t hx) (k₁_hasDerivAt t hx)

theorem W_ode (t : ℝ) {x : ℝ} (hx : 0 < x) :
    W₂ t x = (1 - (t^2+1/4)/x^2) * W t x := by
  apply MaassSqrtRescaling.rescaled_ode hx
  dsimp [k₁, k₂]
  nlinarith [moment_ode t hx]

theorem W_boundary_tendsto (t : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => Real.exp (-a*x) * (W₁ t x + a*W t x)) atTop (𝓝 0) := by
  let C := moment 0 0 1 + moment 1 0 1
  apply MaassSqrtRescaling.weighted_boundary_tendsto (K t) (k₁ t) ha
    (show 0 ≤ C from add_nonneg (zero_moment_nonneg 0 1) (zero_moment_nonneg 1 1))
  · intro x hx
    rw [← moment_zero t x]
    exact (moment_norm_bounded 0 t hx).trans (le_add_of_nonneg_right (zero_moment_nonneg 1 1))
  · intro x hx
    change ‖-moment 1 t x‖ ≤ C
    rw [norm_neg]
    exact (moment_norm_bounded 1 t hx).trans (le_add_of_nonneg_left (zero_moment_nonneg 0 1))

theorem W_product_identity (t : ℝ) {x : ℝ} (hx : 0 < x) :
    W t x * W₁ t x = (moment 0 t x * moment 0 t x)/2 - x*(moment 0 t x * moment 1 t x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  dsimp only [W, W₁, MaassSqrtRescaling.W, MaassSqrtRescaling.W₁, k₁]
  rw [← moment_zero t x]
  field_simp [hs.ne']
  rw [Real.sq_sqrt hx.le]
  ring

theorem W_product_tendsto (t : ℝ) :
    Tendsto (fun x => W t x * W₁ t x) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => (moment 0 t x * moment 0 t x)/2) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, zero_div] using (moment_product_tendsto 0 0 t 0).div_const 2
  have h1 : Tendsto (fun x : ℝ => x*(moment 0 t x * moment 1 t x)) atTop (𝓝 0) := by
    simpa only [pow_one] using moment_product_tendsto 0 1 t 1
  have h : Tendsto (fun x : ℝ => (moment 0 t x * moment 0 t x)/2 -
      x*(moment 0 t x * moment 1 t x)) atTop (𝓝 0) := by simpa using h0.sub h1
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact (W_product_identity t hx).symm

/-- Positivity at and beyond the linear transition, from the actual
integral, ODE, product limit and eventual positivity. -/
theorem W_pos (t : ℝ) {x : ℝ} (hx : 0 < x) (hthreshold : t^2+1/4 ≤ x^2) :
    0 < W t x := by
  apply MaassODEComparison.pos_of_eventual_pos (W t) (W₁ t) (W₂ t) x
    (fun z hz => W_hasDerivAt t (hx.trans_le hz))
    (fun z hz => W₁_hasDerivAt t (hx.trans_le hz)) _ (W_product_tendsto t) _ le_rfl
  · intro z hz
    rw [W_ode t (hx.trans_le hz)]
    have hz2 : 0 < z^2 := sq_pos_of_pos (hx.trans_le hz)
    have hsz : t^2+1/4 ≤ z^2 := hthreshold.trans (by nlinarith [show x ≤ z from hz])
    have hq : 0 ≤ 1-(t^2+1/4)/z^2 := by
      have hh := (div_le_one hz2).mpr hsz
      linarith
    have hh := mul_nonneg hq (sq_nonneg (W t z))
    nlinarith
  · refine ⟨max 1 (t^2+1), ?_⟩
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hy)
    have hlarge : t^2/2 < y := by
      have hh := (le_max_right (1:ℝ) (t^2+1)).trans hy
      nlinarith [sq_nonneg t]
    exact mul_pos (Real.sqrt_pos.mpr hy0) (K_pos_of_large t hy0 hlarge)

theorem W_lower (t : ℝ) {x y : ℝ} (hx : 0 < x)
    (hthreshold : t^2+1/4 ≤ x^2) (hxy : x ≤ y) :
    Real.exp (-(y-x)) * W t x ≤ W t y := by
  have hp (z : ℝ) (hz : z ∈ Ici x) : 0 < W t z :=
    W_pos t (hx.trans_le hz) (hthreshold.trans (by nlinarith [show x ≤ z from hz]))
  apply MaassODEComparison.w_lower_comparison (W t) (W₁ t) (W₂ t) x
    (t^2+1/4) (by positivity)
    (fun z hz => W_hasDerivAt t (hx.trans_le hz))
    (fun z hz => W₁_hasDerivAt t (hx.trans_le hz))
    (fun z hz => (hp z hz).le)
    (fun z hz => W_ode t (hx.trans_le hz))
    (by simpa using W_boundary_tendsto t (show (0:ℝ)<1 by norm_num)) le_rfl hxy

theorem W_upper (t : ℝ) {a x y : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hthreshold : t^2+1/4 ≤ (1-a^2)*x^2) (hxy : x ≤ y) :
    W t y ≤ Real.exp (-a*(y-x)) * W t x := by
  have ha2 : 0 ≤ 1-a^2 := by nlinarith
  have ht : t^2+1/4 ≤ x^2 := hthreshold.trans (by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg x)])
  apply MaassODEComparison.exponential_comparison (W t) (W₁ t) (W₂ t) x a
    (fun z hz => W_hasDerivAt t (hx.trans_le hz))
    (fun z hz => W₁_hasDerivAt t (hx.trans_le hz)) _
    (W_boundary_tendsto t ha) le_rfl hxy
  intro z hz
  rw [W_ode t (hx.trans_le hz)]
  have hsq : x^2 ≤ z^2 := by nlinarith [show x ≤ z from hz]
  have hd : (t^2+1/4)/z^2 ≤ 1-a^2 :=
    (div_le_iff₀ (sq_pos_of_pos (hx.trans_le hz))).mpr (hthreshold.trans
      (mul_le_mul_of_nonneg_left hsq ha2))
  exact mul_le_mul_of_nonneg_right (by linarith) (W_pos t (hx.trans_le hz) (ht.trans hsq)).le

theorem W_ratio (t : ℝ) {a x y : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hthreshold : t^2+1/4 ≤ (1-a^2)*x^2) (hxy : x ≤ y) :
    Real.exp (-(y-x)) ≤ W t y / W t x ∧
      W t y / W t x ≤ Real.exp (-a*(y-x)) := by
  have ht : t^2+1/4 ≤ x^2 := hthreshold.trans (by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg x)])
  exact ⟨(le_div_iff₀ (W_pos t hx ht)).mpr (W_lower t hx ht hxy),
    (div_le_iff₀ (W_pos t hx ht)).mpr (W_upper t ha ha1 hx hthreshold hxy)⟩

#print axioms W_product_tendsto
#print axioms W_pos
#print axioms W_ratio

end MaassKBessel
