module

public import AsymptoticCylinderLiftV1
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open MeasureTheory UpperHalfPlane AsymptoticCylinder AsymptoticFourierNorm
open AsymptoticStripCoordinates AsymptoticGammaTail

/-- A fixed continuous representative of the actual normalized mode. -/
noncomputable def unitRepresentative (m t n : ℕ) (ε : ℝ) (z : Cylinder) : ℂ :=
  (Real.sqrt (beta m t (4*Real.pi*(n+1:ℕ)) ε) : ℂ)⁻¹ *
    mode m t n (4*Real.pi) ε z

theorem unitRepresentative_coeFn (m t n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    unitMode m t n (by positivity : 0 < 4*Real.pi) hε =ᵐ[AsymptoticCylinder.measure]
      unitRepresentative m t n ε := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (beta m t (4*Real.pi*(n+1:ℕ)) ε) : ℂ)⁻¹
    (modeLp m t n (by positivity : 0 < 4*Real.pi) hε),
    modeLp_coeFn m t n (by positivity : 0 < 4*Real.pi) hε] with z hs hm
  exact hs.trans (by simp only [Pi.smul_apply, smul_eq_mul, hm, unitRepresentative])

theorem inv_beta_zero (m : ℕ) {r : ℝ} (hr : 0 < r) (ε : ℝ) :
    (beta m 0 r ε)⁻¹ = r^(m+1)/(m.factorial : ℝ) := by
  simp only [beta, density, Nat.mul_zero, pow_zero, mul_one]
  rw [integral_kernel m hr, mul_inv_rev, one_div, ← inv_pow, inv_inv]
  rw [div_eq_mul_inv, mul_comm]

/-- The difference of the first variable and the conjugate second
variable is again in the upper half plane. -/
noncomputable def difference (z u : ℍ) : ℍ :=
  ⟨(z : ℂ) - star (u : ℂ), by
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, coe_im, sub_neg_eq_add]
    exact add_pos z.im_pos u.im_pos⟩

theorem q_product (z u : ℍ) :
    qCylinder (cylinder z) * star (qCylinder (cylinder u)) =
      Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ)) := by
  rw [AsymptoticCylinderLift.qCylinder_coordinates, AsymptoticCylinderLift.qCylinder_coordinates]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.star_def,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, difference, Complex.star_def]
  ring

noncomputable def kernelTerm (h n : ℕ) (ε : ℝ) (z u : ℍ) : ℂ :=
  unitRepresentative (2*h) 0 n ε (cylinder z) *
    star (unitRepresentative (2*h) 0 n ε (cylinder u))

/-- The Fourier diagonal kernel uses the normalization of the actual
cylinder modes; no independent Bergman-kernel normalization is assumed. -/
theorem kernelTerm_formula (h n : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    kernelTerm h n ε z u =
      (((4*Real.pi)^(2*h+1) * (z.im*u.im)^h / ((2*h).factorial : ℝ)) : ℂ) *
        (n+1 : ℕ)^(2*h+1) * Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^(n+1) := by
  let B := beta (2*h) 0 (4*Real.pi*(n+1:ℕ)) ε
  have hB : 0 ≤ B := beta_nonneg (2*h) 0 hε
  have hc : ((Real.sqrt B : ℂ)⁻¹)^2 = (B⁻¹ : ℝ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt hB, Complex.ofReal_inv]
  have he : kernelTerm h n ε z u =
      (B⁻¹ : ℝ) * ((z.im*u.im)^h : ℝ) *
        (qCylinder (cylinder z)*star (qCylinder (cylinder u)))^(n+1) := by
    unfold kernelTerm unitRepresentative
    rw [mode_even_eq_qCylinder h 0 n hε z.im_pos.le,
      mode_even_eq_qCylinder h 0 n hε u.im_pos.le]
    simp only [cylinder, pow_zero, mul_one, Complex.star_def, map_mul, map_pow,
      map_inv₀, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [← hc]
    simp only [mul_pow]
    ring
  rw [he, q_product, show B⁻¹ = (4*Real.pi*(n+1:ℕ))^(2*h+1)/((2*h).factorial : ℝ) from
    inv_beta_zero (2*h) (by positivity) ε]
  push_cast
  rw [mul_pow]
  ring

noncomputable def fourierKernel (h : ℕ) (ε : ℝ) (z u : ℍ) : ℂ :=
  ∑' n, kernelTerm h n ε z u

theorem kernelTerm_summable (h : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    Summable (fun n => kernelTerm h n ε z u) := by
  have hs : Summable (fun n : ℕ => (n : ℂ)^(2*h+1) *
      Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^n) := by
    simpa only [PNat.val_ofNat, Nat.cast_one, mul_one] using
      summable_pow_mul_cexp (2*h+1) 1 (difference z u)
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hh := hshift.mul_left
    ((((4*Real.pi)^(2*h+1) * (z.im*u.im)^h / ((2*h).factorial : ℝ)) : ℂ))
  apply hh.congr
  intro n
  rw [kernelTerm_formula h n hε z u]
  ring

theorem fourierKernel_formula (h : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    fourierKernel h ε z u =
      (((4*Real.pi)^(2*h+1) * (z.im*u.im)^h / ((2*h).factorial : ℝ)) : ℂ) *
        ∑' n : ℕ, (n : ℂ)^(2*h+1) *
          Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^n := by
  have hs : Summable (fun n : ℕ => (n : ℂ)^(2*h+1) *
      Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^n) := by
    simpa only [PNat.val_ofNat, Nat.cast_one, mul_one] using
      summable_pow_mul_cexp (2*h+1) 1 (difference z u)
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hs)]
  simp only [Nat.cast_zero, zero_pow (by omega : 2*h+1 ≠ 0), zero_mul, zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [kernelTerm_formula h n hε z u]
  ring

#print axioms unitRepresentative_coeFn
#print axioms kernelTerm_formula
#print axioms kernelTerm_summable
#print axioms fourierKernel_formula

end AsymptoticUnweightedKernel
