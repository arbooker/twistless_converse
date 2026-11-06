module

public import MaassMellinFubiniV1

set_option autoImplicit false

@[expose] public section

open Set MeasureTheory

namespace MaassMellin

theorem mellin_integrand_full_line (p : MaassSpectral.Parameter) (s : ℂ)
    {x : ℝ} (hx : 0<x) :
    (x:ℂ)^(s-1)*(MaassSpectral.K p x:ℂ) =
      (1/2:ℂ) * ∫ r : ℝ, doubleKernel s (MaassSpectral.order p) r x := by
  simp only [doubleKernel, integral_const_mul]
  rw [actual_full_line p hx]
  ring

theorem actual_mellin_convergent (p : MaassSpectral.Parameter) {s : ℂ} (hs : 1<s.re) :
    MellinConvergent (fun x => (MaassSpectral.K p x:ℂ)) s := by
  have hi := doubleKernel_integrable hs
    ((order_re_bound p).trans (by linarith : (1:ℝ)/2<s.re))
  have hh := hi.integral_prod_right.const_mul (1/2:ℂ)
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (mellin_integrand_full_line p s hx).symm

/-- Mellin transform of the actual cosine/hyperbolic Bessel integral,
with all integrability and identification inputs discharged. -/
theorem actual_mellin (p : MaassSpectral.Parameter) {s : ℂ} (hs : 1<s.re) :
    mellin (fun x => (MaassSpectral.K p x:ℂ)) s =
      (2:ℂ)^(s-2) * Complex.Gamma ((s+MaassSpectral.order p)/2) *
        Complex.Gamma ((s-MaassSpectral.order p)/2) := by
  let ν := MaassSpectral.order p
  have hν : |ν.re|<s.re := (order_re_bound p).trans (by linarith)
  have hi := doubleKernel_integrable hs hν
  have hA : 0<((s+ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re]
    linarith [neg_abs_le ν.re]
  have hB : 0<((s-ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re]
    linarith [le_abs_self ν.re]
  have hsum : (s+ν)/2+(s-ν)/2=s := by ring
  have hgamma := Complex.Gamma_mul_Gamma_eq_betaIntegral hA hB
  rw [hsum] at hgamma
  have hpower : (1/2:ℂ)*(2:ℂ)^(s-1) = (2:ℂ)^(s-2) := by
    rw [show s-1=(s-2)+1 by ring,
      Complex.cpow_add _ _ (two_ne_zero : (2:ℂ)≠0), Complex.cpow_one]
    ring
  calc
    mellin (fun x => (MaassSpectral.K p x:ℂ)) s =
        (1/2:ℂ) * ∫ x in Ioi (0:ℝ), ∫ r : ℝ, doubleKernel s ν r x := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => mellin_integrand_full_line p s hx)
    _ = (1/2:ℂ) * ∫ r : ℝ, ∫ x in Ioi (0:ℝ), doubleKernel s ν r x := by
      rw [integral_integral_swap hi]
    _ = (1/2:ℂ) * (Complex.Gamma s * ∫ r : ℝ, bilateral s ν r) := by
      simp_rw [doubleKernel_integral (by linarith : 0<s.re), integral_const_mul]
    _ = (2:ℂ)^(s-2) * (Complex.Gamma s * Complex.betaIntegral ((s+ν)/2) ((s-ν)/2)) := by
      rw [bilateral_integral]
      calc
        _ = ((1/2:ℂ)*(2:ℂ)^(s-1)) *
            (Complex.Gamma s * Complex.betaIntegral ((s+ν)/2) ((s-ν)/2)) := by ring
        _ = _ := by rw [hpower]
    _ = _ := by
      rw [← hgamma]
      ring

#print axioms actual_mellin_convergent
#print axioms actual_mellin

end MaassMellin
