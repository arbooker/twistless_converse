module

public import MaassActualMellinV1
public import FinitenessGammaIntegrabilityV1
public import Mathlib.Analysis.MellinInversion

set_option autoImplicit false

@[expose] public section

open MeasureTheory Complex

namespace MaassMellin

noncomputable def gammaPair (ν s : ℂ) : ℂ :=
  (2:ℂ)^(s-2) * Complex.Gamma ((s+ν)/2) * Complex.Gamma ((s-ν)/2)

theorem gamma_plus_line (ν : ℂ) (c v : ℝ) :
    (((c:ℂ)+(v:ℂ)*Complex.I)+ν)/2 =
      (((c+ν.re)/2:ℝ):ℂ) + (((v+ν.im)/2:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp

theorem gamma_minus_line (ν : ℂ) (c v : ℝ) :
    (((c:ℂ)+(v:ℂ)*Complex.I)-ν)/2 =
      (((c-ν.re)/2:ℝ):ℂ) + (((v-ν.im)/2:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp

theorem gammaPair_line_continuous {ν : ℂ} {c : ℝ} (hc : |ν.re|<c) :
    Continuous (fun v : ℝ => gammaPair ν ((c:ℂ)+(v:ℂ)*Complex.I)) := by
  have ha : 0<(c+ν.re)/2 := by linarith [neg_abs_le ν.re]
  have hb : 0<(c-ν.re)/2 := by linarith [le_abs_self ν.re]
  have hp : Continuous (fun v : ℝ => (2:ℂ)^(((c:ℂ)+(v:ℂ)*Complex.I)-2)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (two_ne_zero : (2:ℂ)≠0)]
    fun_prop
  unfold gammaPair
  simp_rw [gamma_plus_line, gamma_minus_line]
  exact (hp.mul ((FinitenessGammaIntegrability.gamma_continuous _ ha).comp
    (by fun_prop))).mul ((FinitenessGammaIntegrability.gamma_continuous _ hb).comp (by fun_prop))

theorem gammaPair_vertical {ν : ℂ} {c : ℝ} (hc : |ν.re|<c) :
    VerticalIntegrable (gammaPair ν) c := by
  have ha : 0<(c+ν.re)/2 := by linarith [neg_abs_le ν.re]
  have hb : 0<(c-ν.re)/2 := by linarith [le_abs_self ν.re]
  have hg : Integrable (fun v : ℝ => Complex.Gamma
      ((((c+ν.re)/2:ℝ):ℂ)+(v:ℂ)*Complex.I)) := by
    simpa only [pow_zero, one_mul] using FinitenessGammaIntegrability.integrable _ ha 0
  have hga : Integrable (fun v : ℝ => Complex.Gamma
      ((((c+ν.re)/2:ℝ):ℂ)+(((v+ν.im)/2:ℝ):ℂ)*Complex.I)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (hg.comp_mul_right' (by norm_num : (1/2:ℝ)≠0)).comp_add_right ν.im
  apply (hga.norm.const_mul ((2:ℝ)^(c-2)*Real.Gamma ((c-ν.re)/2))).mono'
    (gammaPair_line_continuous hc).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  have hm := FinitenessGammaDecay.norm_le_real
    (s := (((c-ν.re)/2:ℝ):ℂ)+(((v-ν.im)/2:ℝ):ℂ)*Complex.I)
    (by simpa using hb)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero] at hm
  dsimp only [gammaPair]
  rw [norm_mul, norm_mul]
  have hp : ‖(2:ℂ)^(((c:ℂ)+(v:ℂ)*Complex.I)-2)‖ = (2:ℝ)^(c-2) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2)
      (((c:ℂ)+(v:ℂ)*Complex.I)-2)
  rw [hp, gamma_plus_line, gamma_minus_line]
  nlinarith [mul_le_mul_of_nonneg_left hm
    (mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (c-2)).le
      (norm_nonneg (Complex.Gamma ((((c+ν.re)/2:ℝ):ℂ)+(((v+ν.im)/2:ℝ):ℂ)*Complex.I))))]

theorem actual_K_continuousAt (p : MaassSpectral.Parameter) {x : ℝ} (hx : 0<x) :
    ContinuousAt (fun y => (MaassSpectral.K p y:ℂ)) x := by
  apply Complex.continuous_ofReal.continuousAt.comp
  cases p with
  | principal t => exact (MaassKBessel.K_hasDerivAt t hx).continuousAt
  | exceptional τ hτ =>
    exact (MaassExceptional.K_hasDerivAt (by linarith : |τ|≤1) hx).continuousAt

/-- Pointwise inverse Mellin of the actual kernel, not an assumed inversion interface. -/
theorem actual_inverse_mellin (p : MaassSpectral.Parameter) {c x : ℝ}
    (hc : 1<c) (hx : 0<x) :
    mellinInv c (gammaPair (MaassSpectral.order p)) x = (MaassSpectral.K p x:ℂ) := by
  have he (v:ℝ) : mellin (fun y => (MaassSpectral.K p y:ℂ))
      ((c:ℂ)+(v:ℂ)*Complex.I) = gammaPair (MaassSpectral.order p) ((c:ℂ)+(v:ℂ)*Complex.I) :=
    actual_mellin p (by simpa using hc)
  have hv : VerticalIntegrable (mellin (fun y => (MaassSpectral.K p y:ℂ))) c := by
    apply (gammaPair_vertical ((order_re_bound p).trans (by linarith : (1:ℝ)/2<c))).congr
    exact Filter.Eventually.of_forall (fun v => (he v).symm)
  calc
    _ = mellinInv c (mellin (fun y => (MaassSpectral.K p y:ℂ))) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by dsimp only; rw [he v])
    _ = _ := mellinInv_mellin_eq c _ hx (actual_mellin_convergent p (by simpa using hc))
      hv (actual_K_continuousAt p hx)

#print axioms gammaPair_vertical
#print axioms actual_inverse_mellin

end MaassMellin
