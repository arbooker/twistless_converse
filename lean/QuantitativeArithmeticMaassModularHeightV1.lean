module
public import Mathlib.NumberTheory.Modular
public import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public noncomputable section
open Set Filter UpperHalfPlane Matrix
open scoped MatrixGroups Topology
namespace QuantitativeArithmeticMaassModularHeight

/-- Actual maximal modular height; existence is Mathlib's reduction theorem. -/
def height (z : ℍ) : ℝ := ((ModularGroup.exists_max_im z).choose • z).im

theorem orbit_le_height (z : ℍ) (g : SL(2,ℤ)) : (g•z).im≤height z :=
  (ModularGroup.exists_max_im z).choose_spec g

theorem height_le (z : ℍ) {B : ℝ} (h : ∀ g : SL(2,ℤ), (g•z).im≤B) : height z≤B :=
  h _

theorem im_le_height (z : ℍ) : z.im≤height z := by
  simpa only [one_smul] using orbit_le_height z (1 : SL(2,ℤ))

theorem height_invariant (g : SL(2,ℤ)) (z : ℍ) : height (g•z)=height z := by
  apply le_antisymm
  · apply height_le
    intro h
    simpa only [mul_smul] using orbit_le_height z (h*g)
  · apply height_le
    intro h
    simpa only [mul_smul,inv_smul_smul] using orbit_le_height (g•z) (h*g⁻¹)

theorem im_eq_of_lower_left_zero (g : SL(2,ℤ)) (z : ℍ) (hc : g 1 0=0) :
    (g•z).im=z.im := by
  obtain ⟨n,hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
  rw [hn z,ModularGroup.im_T_zpow_smul]

theorem im_le_inverse_of_lower_left_ne_zero (g : SL(2,ℤ)) (z : ℍ) (hc : g 1 0≠0) :
    (g•z).im≤1/z.im := by
  have hcint : (1:ℤ)≤(g 1 0)^2 := by
    have := sq_pos_of_ne_zero hc
    omega
  have hc2 : (1:ℝ)≤(g 1 0:ℝ)^2 := by exact_mod_cast hcint
  have hd : z.im^2≤Complex.normSq (denom g z) := by
    rw [ModularGroup.denom_apply,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.intCast_re,Complex.intCast_im,zero_mul,sub_zero,add_zero,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    nlinarith [sq_nonneg ((g 1 0:ℝ)*z.re+(g 1 1:ℝ)),
      mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im)]
  rw [ModularGroup.im_smul_eq_div_normSq]
  calc
    z.im/Complex.normSq (denom g z)≤z.im/z.im^2 :=
      div_le_div_of_nonneg_left z.im_pos.le (sq_pos_of_pos z.im_pos) hd
    _ = 1/z.im := by field_simp

theorem height_bound (z : ℍ) : height z≤max z.im (1/z.im) := by
  apply height_le
  intro g
  by_cases hc : g 1 0=0
  · rw [im_eq_of_lower_left_zero g z hc]
    exact le_max_left _ _
  · exact (im_le_inverse_of_lower_left_ne_zero g z hc).trans (le_max_right _ _)

/-- Above height one, the identity cusp realizes maximal modular height. -/
theorem height_eq_im (z : ℍ) (hz : 1≤z.im) : height z=z.im := by
  apply le_antisymm _ (im_le_height z)
  apply (height_bound z).trans
  apply max_le le_rfl
  exact (div_le_iff₀ z.im_pos).mpr (by nlinarith)

/-- A profile vanishing below two ignores every non-parabolic branch
throughout the open chart im(z)>1/2. -/
theorem profile_eq (ψ : ℝ → ℂ) (hψ : ∀ y, y≤2 → ψ y=0)
    (z : ℍ) (hz : 1/2<z.im) : ψ (height z)=ψ z.im := by
  by_cases hy : 1≤z.im
  · rw [height_eq_im z hy]
  · have hlow : z.im≤2 := by linarith
    have hinv : 1/z.im≤2 := (div_le_iff₀ z.im_pos).mpr (by linarith)
    rw [hψ _ ((height_bound z).trans (max_le hlow hinv)),hψ _ hlow]

theorem exists_high_chart (z : ℍ) : ∃ g : SL(2,ℤ), 1/2<(g•z).im := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨g,?_⟩
  nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg,(g•z).im_pos]

#print axioms height_invariant
#print axioms profile_eq
#print axioms exists_high_chart
end QuantitativeArithmeticMaassModularHeight
