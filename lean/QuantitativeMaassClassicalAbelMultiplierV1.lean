module

public import QuantitativeMaassScalarAbelInitialValueV1
public import QuantitativeMaassScalarCauchyCosineV1
public import QuantitativeMaassMovingWindowsV1
public import QuantitativeMaassContinuousRadialUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- The literal radial Abel convolution has the exact cosine multiplier on
a smooth invariant classical eigenfunction. No global L2 assumption enters. -/
theorem classical_abel_multiplier (N : ℕ) (u : ℝ×ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (r : ℝ)
    (he : ∀ y : ℍ,upperLaplacian u y=(1/4+(r:ℂ)^2)*upperFunction u y)
    (hinv : ∀ γ : gamma N,∀ y,upperFunction u (γ•y)=upperFunction u y)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    scalarAbelConvolution (upperFunction u) x F=
      cosinePacket (coshTimeTest F) r*upperFunction u x := by
  let e : ℂ := 1/4+(r:ℂ)^2
  obtain ⟨c,hcT⟩ := scalarAbel_cauchy u hu e he x
  let v := boundedCauchyPosition ((scalarAbelGenerator e).restrictScalars ℝ) c
  have hv : Continuous v := boundedCauchyPosition_continuous _ c
  have hc2 := scalarAbel_zero_velocity u hu e he x c hcT
  have hc1 : c.1=2*upperFunction u x := by
    have hh := scalarAbel_initial_value N (upperFunction u) (upperFunction_continuous hu) hinv x v hv hcT
    dsimp only [v] at hh
    rw [(boundedCauchy_initial ((scalarAbelGenerator e).restrictScalars ℝ) c).1] at hh
    exact hh
  have hvcos (t : ℝ) (ht : 0≤t) : v t=(Real.cos (r*t):ℂ)*(2*upperFunction u x) := by
    exact (scalarCauchy_cosine r c hc2 t ht).trans (by rw [hc1])
  rw [scalarAbel_originalTest _ (upperFunction_continuous hu) x v hv hcT F hF hc hr R hR hs]
  have hi : Integrable (fun t => coshTimeTest F t*(Real.cos (r*t):ℂ)) :=
    coshCurve_integrable F hF R hR hs _
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hh := integral_even_eq_two_half (fun t => coshTimeTest F t*(Real.cos (r*t):ℂ)) hi
    (fun t => by simp only [coshTimeTest,Real.cosh_neg,mul_neg,Real.cos_neg])
  have hp : cosinePacket (coshTimeTest F) r=(2:ℂ)*
      (∫ t in Ioi (0:ℝ),coshTimeTest F t*(Real.cos (r*t):ℂ)) := by
    simpa only [cosinePacket,mul_comm r,smul_eq_mul] using hh
  rw [hp]
  calc
    _ = ∫ t in Ioi (0:ℝ),(coshTimeTest F t*(Real.cos (r*t):ℂ))*(2*upperFunction u x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hvcos t ht.le]
      ring
    _ = _ := by rw [integral_mul_const]; ring

/-- Exact scalar spectral action for the original polynomial-growth Euler
wave, using its checked classical PDE and translation invariance. -/
theorem principalEuler_abel_multiplier {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    (∫ y : ℍ,abelProfile F (Real.cosh (dist y x))*principalEulerPhysical b r σ y)=
      cosinePacket (coshTimeTest F) r*principalEulerPhysical b r σ x := by
  apply classical_abel_multiplier 0 (principalEulerWave b r σ)
    (principalEulerWave_contDiffOn hb r σ) r
  · intro y
    have h := principalEulerWave_hyperbolic hb r σ y.re y.im y.im_pos
    push_cast at h
    exact h
  · exact principalEulerPhysical_cylinder_invariant b r σ
  · exact hF
  · exact hc
  · exact hr
  · exact hR
  · exact hs

#print axioms classical_abel_multiplier
#print axioms principalEuler_abel_multiplier

end QuantitativeMaass
