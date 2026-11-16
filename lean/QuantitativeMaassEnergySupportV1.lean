module

public import QuantitativeMaassEnergyCovarianceV1
public import QuantitativeMaassGreenUpperV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

def upperEnergy (u v : Point → ℂ) : ℍ → ℂ := upperFunction (hyperbolicEnergy u v)

theorem upper_dir_zero_of_notMem_tsupport {v : Point → ℂ} {z : ℍ}
    (hz : z∉tsupport (upperFunction v)) (w : Point) : dir w v (z.re,z.im)=0 := by
  have hcart : cartesianLift (z.re,z.im)=z := by
    rw [cartesianLift_positive _ z.im_pos]
    rfl
  have ht : Tendsto cartesianLift (𝓝 (z.re,z.im)) (𝓝 z) := by
    simpa only [ContinuousAt,hcart] using cartesianLift_continuousAt (z.re,z.im) z.im_pos
  have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto ht
  have he' : v=ᶠ[𝓝 (z.re,z.im)] 0 := by
    filter_upwards [he,(isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos]
      with W hW hpos
    simpa only [Function.comp_apply,upperFunction_cartesianLift hpos,Pi.zero_apply] using hW
  unfold dir D
  rw [he'.fderiv_eq]
  simp

theorem upperEnergy_support_right (u v : Point → ℂ) :
    Function.support (upperEnergy u v)⊆tsupport (upperFunction v) := by
  intro z hz
  by_contra hn
  have hx := upper_dir_zero_of_notMem_tsupport hn e₁
  have hy := upper_dir_zero_of_notMem_tsupport hn e₂
  exact hz (by simp [upperEnergy,upperFunction,hyperbolicEnergy,X,Y,hx,hy])

theorem upperEnergy_compact_right (u v : Point → ℂ)
    (hc : HasCompactSupport (upperFunction v)) : HasCompactSupport (upperEnergy u v) :=
  hc.of_isClosed_subset isClosed_closure
    (closure_minimal (upperEnergy_support_right u v) isClosed_closure)

theorem upperEnergy_continuous {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) : Continuous (upperEnergy u v) :=
  upperFunction_continuous (hyperbolicEnergy_smooth hu hv)

theorem upperEnergy_integrable {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction v)) : Integrable (upperEnergy u v) :=
  (upperEnergy_continuous hu hv).integrable_of_hasCompactSupport
    (upperEnergy_compact_right u v hc)

theorem upperEnergy_eqOn_right {u v v' : Point → ℂ}
    (he : EqOn v v' {Z : Point | 0<Z.2}) : upperEnergy u v=upperEnergy u v' := by
  funext z
  apply hyperbolicEnergy_congr_right
  exact Filter.eventually_of_mem
    ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos) he

#print axioms upperEnergy_integrable

end QuantitativeMaass
