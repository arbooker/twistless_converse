module

public import QuantitativeMaassHyperbolicWeightsV1
public import QuantitativeMaassHigherTimeCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The differentiated radial time integrand of one modulated carrier. -/
def radialTimeCarrier (t : ℝ) (A : ℝ → ℂ) (u : ℝ) : ℂ :=
  timeDerivativeCarrier t (timeDerivativeCarrier t A) u*(reciprocalSinh u:ℂ)-
    timeDerivativeCarrier t A u*(reciprocalSinhSlope u:ℂ)

/-- Absolute integrability of the two weighted terms, including the singular
lower endpoint of the Abel integral. -/
theorem bounded_weight_abel_integrable (g : ℝ → ℂ) (p : ℝ → ℝ)
    (d b t M P : ℝ) (hd : 0<d) (hdb : d≤b) (hM : 0≤M)
    (hgm : Measurable g) (hpm : Measurable p)
    (hg : ∀ u∈Ioc d b,‖g u‖≤M) (hp : ∀ u∈Ioc d b,0≤p u ∧ p u≤P) :
    IntervalIntegrable (fun u => Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(p u:ℂ))*(abelSingularWeight d u:ℂ))
      volume d b := by
  apply abelSingularWeight_amplitude_integrable (fun u => g u*(p u:ℂ)) d b t (M*P) hd hdb
    (hgm.mul (Complex.measurable_ofReal.comp hpm))
  intro u hu
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp u hu).1]
  exact mul_le_mul (hg u hu) (hp u hu).2 (hp u hu).1 hM

/-- Differentiated Abel oscillation loses exactly the two expected hyperbolic
weights. The spectral factor grows as t^(3/2), before radial integration. -/
theorem radialTimeCarrier_abel_decay (A : ℝ → ℂ) (hA : ContDiff ℝ ∞ A)
    (d b L t M : ℝ) (hd : 0<d) (hdb : d≤b) (hlen : b-d≤L)
    (ht : t≠0) (hM : 0≤M)
    (hb : ∀ n : ℕ,n≤3 → ∀ u,‖iteratedDeriv n A u‖≤M) :
    IntervalIntegrable (fun u => timeFrequencyShift t (radialTimeCarrier t A) u*(abelSingularWeight d u:ℂ)) volume d b ∧
    ‖∫ u in d..b,timeFrequencyShift t (radialTimeCarrier t A) u*(abelSingularWeight d u:ℂ)‖≤
      (5+L)*M*((|t|+1)^2*reciprocalSinh d+(|t|+1)*reciprocalSinhSlope d)/
        (Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  let g := timeDerivativeCarrier t (timeDerivativeCarrier t A)
  let h := timeDerivativeCarrier t A
  let C := (|t|+1)^2*M
  let D := (|t|+1)*M
  have hg : ContDiff ℝ ∞ g := timeDerivativeCarrier_smooth t _ (timeDerivativeCarrier_smooth t A hA)
  have hh : ContDiff ℝ ∞ h := timeDerivativeCarrier_smooth t A hA
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hh' : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hC : 0≤C := by dsimp only [C];positivity
  have hD : 0≤D := by dsimp only [D];positivity
  have hgb := timeSecondDerivativeCarrier_bounds t A hA M hb
  have hhb := timeDerivativeCarrier_iterated_bound t A hA 2 M hb
  have hg0 (u : ℝ) : ‖g u‖≤C := by simpa only [iteratedDeriv_zero] using hgb 0 (by omega) u
  have hg1 (u : ℝ) : ‖deriv g u‖≤C := by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hgb 1 le_rfl u
  have hh0 (u : ℝ) : ‖h u‖≤D := by simpa only [iteratedDeriv_zero] using hhb 0 (by omega) u
  have hh1 (u : ℝ) : ‖deriv h u‖≤D := by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hhb 1 (by omega) u
  have hp := abelSingularWeight_reciprocalSinh_decay g (deriv g) d b t C C hd hdb ht hC hC
    hg.continuous.measurable (fun u _ => (hg.differentiable (by simp)).differentiableAt.hasDerivAt)
    (hg'.continuous.intervalIntegrable d b) (fun u _ => hg0 u) (fun u _ => hg1 u)
  have hq := abelSingularWeight_reciprocalSinhSlope_decay h (deriv h) d b t D D hd hdb ht hD hD
    hh.continuous.measurable (fun u _ => (hh.differentiable (by simp)).differentiableAt.hasDerivAt)
    (hh'.continuous.intervalIntegrable d b) (fun u _ => hh0 u) (fun u _ => hh1 u)
  have hip := bounded_weight_abel_integrable g reciprocalSinh d b t C (reciprocalSinh d) hd hdb hC
    hg.continuous.measurable (by unfold reciprocalSinh;fun_prop) (fun u _ => hg0 u) (fun u hu =>
      ⟨reciprocalSinh_nonneg u (hd.trans hu.1),reciprocalSinh_antitone hd (hd.trans hu.1) hu.1.le⟩)
  have hiq := bounded_weight_abel_integrable h reciprocalSinhSlope d b t D (reciprocalSinhSlope d) hd hdb hD
    hh.continuous.measurable (by unfold reciprocalSinhSlope;fun_prop) (fun u _ => hh0 u) (fun u hu =>
      ⟨reciprocalSinhSlope_nonneg u,reciprocalSinhSlope_antitone hd (hd.trans hu.1) hu.1.le⟩)
  have heq : (fun u => timeFrequencyShift t (radialTimeCarrier t A) u*(abelSingularWeight d u:ℂ))=
      (fun u => Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(reciprocalSinh u:ℂ))*(abelSingularWeight d u:ℂ))-
      (fun u => Complex.exp ((t*u:ℝ)*Complex.I)*(h u*(reciprocalSinhSlope u:ℂ))*(abelSingularWeight d u:ℂ)) := by
    funext u
    simp only [timeFrequencyShift,radialTimeCarrier,g,h,Pi.sub_apply,mul_sub,sub_mul]
  rw [heq]
  refine ⟨hip.sub hiq,?_⟩
  change ‖∫ u in d..b,
    Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(reciprocalSinh u:ℂ))*(abelSingularWeight d u:ℂ)-
      Complex.exp ((t*u:ℝ)*Complex.I)*(h u*(reciprocalSinhSlope u:ℂ))*(abelSingularWeight d u:ℂ)‖≤_
  rw [intervalIntegral.integral_sub hip hiq]
  apply (norm_sub_le _ _).trans ((add_le_add hp hq).trans ?_)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp0 := reciprocalSinh_nonneg d hd
  have hq0 := reciprocalSinhSlope_nonneg d
  have hlenp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hC) hp0
  have hlenq := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hD) hq0
  dsimp only [C,D] at *
  nlinarith

#print axioms bounded_weight_abel_integrable
#print axioms radialTimeCarrier_abel_decay

end QuantitativeMaass
