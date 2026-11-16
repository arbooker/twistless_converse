module

public import QuantitativeMaassEulerWaveAnalyticV1
public import MaassFrickeGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A pointwise physical tube condition suffices after shrinking the open
coordinate domain; no global tube condition on the rational curves is needed. -/
theorem complexEulerWave_analyticAt_curves {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (X Y : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hX : DifferentiableOn ℂ X D) (hY : DifferentiableOn ℂ Y D)
    (z : ℂ) (hz : z∈D) (hgap : |(X z).im|<(Y z).re) :
    AnalyticAt ℂ (fun w => complexEulerWave b r σ (X w) (Y w)) z := by
  let ρ := fun w => (Y w).re-|(X w).im|
  have hρ : ContinuousOn ρ D :=
    (Complex.continuous_re.comp_continuousOn hY.continuousOn).sub
      (Complex.continuous_im.comp_continuousOn hX.continuousOn).abs
  let U := D∩ρ ⁻¹' Ioi 0
  have hU : IsOpen U := hρ.isOpen_inter_preimage hD isOpen_Ioi
  exact complexEulerWave_analytic_curves hb r σ X Y U hU
    (hX.mono inter_subset_left) (hY.mono inter_subset_left)
    (fun w hw => sub_pos.mp hw.2) z ⟨hz,sub_pos.mpr hgap⟩

/-- The actual Fricke pullback is real analytic in the horizontal variable.
This is derived from rational complex coordinate curves, not assumed as a
regularity property of the reconstruction. -/
theorem principalEulerWave_fricke_analytic_horizontal {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (σ : ℕ)
    (L y : ℝ) (hL : 0<L) (hy : 0<y) :
    AnalyticOnNhd ℝ (fun x => principalEulerWave b r σ (MaassDifferential.F L x y)) univ := by
  let d := fun z : ℂ => (L:ℂ)*(z^2+(y:ℂ)^2)
  let X := fun z : ℂ => -z/d z
  let Y := fun z : ℂ => (y:ℂ)/d z
  let D := {z : ℂ | d z≠0}
  have hd : Continuous d := by fun_prop
  have hD : IsOpen D := isOpen_ne.preimage hd
  have hX : DifferentiableOn ℂ X D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_id.neg.div (by fun_prop) hz
  have hY : DifferentiableOn ℂ Y D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_const (y:ℂ)).div (by fun_prop) hz
  have hXreal : ∀ x : ℝ,X (x:ℂ)=((MaassDifferential.F L x y).1:ℂ) := by
    intro x
    dsimp [X,d,MaassDifferential.F]
    push_cast
    rfl
  have hYreal : ∀ x : ℝ,Y (x:ℂ)=((MaassDifferential.F L x y).2:ℂ) := by
    intro x
    dsimp [Y,d,MaassDifferential.F]
    push_cast
    rfl
  intro x _
  have hx : (x:ℂ)∈D := by
    change (L:ℂ)*((x:ℂ)^2+(y:ℂ)^2)≠0
    have hp : 0<L*(x^2+y^2) := mul_pos hL (MaassDifferential.radius_pos hy)
    exact_mod_cast hp.ne'
  have hgap : |(X (x:ℂ)).im|<(Y (x:ℂ)).re := by
    rw [hXreal,hYreal]
    simpa using (MaassDifferential.F_height_pos (x:=x) hL hy)
  have ha := complexEulerWave_analyticAt_curves hb r σ X Y D hD hX hY (x:ℂ) hx hgap
  have hh : AnalyticAt ℝ (fun u : ℝ => complexEulerWave b r σ (X (u:ℂ)) (Y (u:ℂ))) x :=
    (ha.restrictScalars (𝕜:=ℝ)).comp (Complex.ofRealCLM.analyticAt x)
  have he : (fun u : ℝ => complexEulerWave b r σ (X (u:ℂ)) (Y (u:ℂ)))=
      fun u => principalEulerWave b r σ (MaassDifferential.F L u y) := by
    funext u
    rw [hXreal,hYreal,complexEulerWave_ofReal b r σ _ _ (MaassDifferential.F_height_pos hL hy).le]
  rw [he] at hh
  exact hh

#print axioms complexEulerWave_analyticAt_curves
#print axioms principalEulerWave_fricke_analytic_horizontal

end QuantitativeMaass
