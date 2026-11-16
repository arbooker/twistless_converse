module

public import QuantitativeMaassEulerPhysicalAxisV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Transfer of the two physical axis data to global Fricke reflection. All
smoothness, analyticity and PDE hypotheses of Cauchy uniqueness are discharged
by the actual original-coefficient reconstruction. -/
theorem principalEulerWave_fricke_from_axis {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (σ : ℕ) (χ : ℂ)
    (hvalue : ∀ y : ℝ,0<y → principalEulerWave b r σ (0,y)=
      χ*principalEulerWave b r σ (0,1/(L*y)))
    (hnormal : ∀ y : ℝ,0<y → deriv (fun x => principalEulerWave b r σ (x,y)) 0=
      χ*((-1/(L*y^2):ℝ):ℂ)*deriv (fun x => principalEulerWave b r σ (x,1/(L*y))) 0) :
    ∀ x y : ℝ,0<y → principalEulerWave b r σ (x,y)=
      χ*principalEulerWave b r σ (MaassDifferential.F L x y) := by
  let f := principalEulerWave b r σ
  let g := MaassDifferential.pullback L f
  let lam : ℂ := ((1/4+r^2:ℝ):ℂ)
  have hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2} := principalEulerWave_contDiffOn hb r σ
  have hg : ContDiffOn ℝ ∞ g {z : ℝ × ℝ | 0<z.2} := fricke_pullback_contDiffOn hf L hL
  have hef : planeEigenEquation lam f := planeEigenEquation_of_hyperbolic hf
    (principalEulerWave_hyperbolic hb r σ)
  have heg : planeEigenEquation lam g := by
    apply planeEigenEquation_of_hyperbolic hg
    intro x y hy
    rw [MaassDifferential.hyperbolic_pullback hf hL hy]
    exact principalEulerWave_hyperbolic hb r σ _ _ (MaassDifferential.F_height_pos hL hy)
  have hcg : ContDiffOn ℝ ∞ (fun z => χ*g z) {z : ℝ × ℝ | 0<z.2} := contDiffOn_const.mul hg
  have hecg : planeEigenEquation lam (fun z => χ*g z) := by
    simpa only [zero_mul,add_zero] using planeEigenEquation_linear hg hg heg heg χ 0
  apply planeEigenEquation_cauchy_eq hf hcg hef hecg
  · exact principalEulerWave_analytic_horizontal hb r σ
  · intro y hy
    exact analyticOnNhd_const.mul (principalEulerWave_fricke_analytic_horizontal hb r σ L y hL hy)
  · intro y hy
    change principalEulerWave b r σ (0,y)=χ*principalEulerWave b r σ (MaassDifferential.F L 0 y)
    rw [fricke_axis L y hL hy]
    exact hvalue y hy
  · intro y hy
    have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
    have hh := planeDerivative_linear hg hg χ 0 (1,0) (0,y) hy
    simp only [zero_mul,add_zero] at hh
    rw [hh,fricke_normal_axis hf L y hL hy,
      ←planeDerivative_horizontal hf hU 0 y hy,
      ←planeDerivative_horizontal hf hU 0 (1/(L*y)) (show 0<1/(L*y) by positivity)]
    simpa only [mul_assoc] using hnormal y hy

#print axioms principalEulerWave_fricke_from_axis

end QuantitativeMaass
