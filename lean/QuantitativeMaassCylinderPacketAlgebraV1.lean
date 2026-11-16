module

public import QuantitativeMaassCylinderPacketKernelV1
public import QuantitativeMaassPacketCompositionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Reality of the time test gives self-adjointness on the entire
translation-cylinder Hilbert space, including its noncuspidal vectors. -/
theorem cylinderTimePacket_isSelfAdjoint (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s) :
    IsSelfAdjoint (cylinderTimePacket f hf hc) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint 0 f (compactSmoothWaveWeight f hf hc) hr))
      (cylinderAutomorphic v) (cylinderAutomorphic w)

/-- Exact convolution composition on the actual full cylinder L2 space. -/
theorem cylinderTimePacket_convolution (f g : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport (f : ℝ → ℂ)) (hgc : HasCompactSupport (g : ℝ → ℂ))
    (he : Function.Even g) :
    cylinderTimePacket (timeConvolution f g) ((timeConvolution f g).smooth ⊤)
      (timeConvolution_compact f g hfc hgc)=
        (cylinderTimePacket f (f.smooth ⊤) hfc).comp (cylinderTimePacket g (g.smooth ⊤) hgc) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun A : AutomorphicSpace 0 →L[ℂ] AutomorphicSpace 0 =>
    (A (cylinderAutomorphic v)).val) (timeConvolution_wavePacket 0 f g hfc hgc he)

#print axioms cylinderTimePacket_isSelfAdjoint
#print axioms cylinderTimePacket_convolution

end QuantitativeMaass
