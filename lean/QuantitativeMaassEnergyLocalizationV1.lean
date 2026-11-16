module

public import QuantitativeMaassPoincareEnergyIdentityV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Exact norm expression for the literal hyperbolic gradient energy. -/
theorem hyperbolicEnergy_self_eq (u : Point → ℂ) (Z : Point) :
    (hyperbolicEnergy u u Z).re=Z.2^2*(‖X u Z‖^2+‖Y u Z‖^2) := by
  unfold hyperbolicEnergy
  simp only [Complex.star_def,Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_add,
    ← Complex.ofReal_mul,Complex.ofReal_re]

private theorem norm_add_sq_bound (a b : ℂ) : ‖a+b‖^2≤2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_add_le a b
  have hs := sq_le_sq₀ (norm_nonneg (a+b)) (by positivity : 0≤‖a‖+‖b‖) |>.mpr h
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- Pointwise localization estimate with an explicit gradient-error term.
It is derived from the actual product rule, before any form completion. -/
theorem hyperbolicEnergy_product_bound {u b : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    (hyperbolicEnergy (fun W => b W*u W) (fun W => b W*u W) Z).re≤
      2*‖b Z‖^2*(hyperbolicEnergy u u Z).re+
      2*‖u Z‖^2*(hyperbolicEnergy b b Z).re := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  simp only [hyperbolicEnergy_self_eq]
  have hx := dir_mul_smooth hs hb hu hZ e₁
  have hy := dir_mul_smooth hs hb hu hZ e₂
  change X (fun W => b W*u W) Z=X b Z*u Z+b Z*X u Z at hx
  change Y (fun W => b W*u W) Z=Y b Z*u Z+b Z*Y u Z at hy
  rw [hx,hy]
  have h1 := norm_add_sq_bound (X b Z*u Z) (b Z*X u Z)
  have h2 := norm_add_sq_bound (Y b Z*u Z) (b Z*Y u Z)
  simp only [norm_mul,mul_pow] at h1 h2
  have he := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (sq_nonneg Z.2)
  nlinarith

/-- An invariant scalar multiplier commutes with literal Poincaré summation,
including the central stabilizer multiplicity already in that summation. -/
theorem poincareSum_mul_invariant {G A : Type*} [Group G] [MulAction G A]
    (f b : A→ℂ) (hb : ∀ g : G, ∀ x, b (g•x)=b x) (x : A) :
    poincareSum (G := G) (fun y => b y*f y) x=b x*poincareSum (G := G) f x := by
  unfold poincareSum
  simp_rw [hb]
  exact tsum_mul_left

#print axioms hyperbolicEnergy_product_bound
#print axioms poincareSum_mul_invariant

end QuantitativeMaass
