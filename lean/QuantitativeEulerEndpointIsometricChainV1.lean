module

public import QuantitativeEulerEndpointIsometricStepV1
public import QuantitativeSpectralDeflationChainV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointIsometricImage
open ContinuousLinearMap QuantitativeSpectralCornerCutRow QuantitativeSpectralDeflationChain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (F : ClosedSubmodule ℂ H) :
    CompleteSpace F.toSubmodule := F.isClosed.completeSpace_coe

def closedImage (U : H →L[ℂ] H) (F : ClosedSubmodule ℂ H)
    (hU : ∀ v∈F,‖U v‖=‖v‖) : ClosedSubmodule ℂ H where
  toSubmodule := imageSpace U F.toSubmodule hU
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (imageSpace U F.toSubmodule hU))).isClosed

theorem closed_image_step (U : H →L[ℂ] H) (F : ClosedSubmodule ℂ H)
    (hU : ∀ v∈F,‖U v‖=‖v‖) (B : H →L[ℂ] H) (c : ℝ) :
    closedImage U (step F (B*U) c) (fun v hv => hU v (nextSpace_le F.toSubmodule (B*U) c hv))=
      step (closedImage U F hU) B c := by
  apply SetLike.coe_injective
  exact congrArg (fun V : Submodule ℂ H => (V : Set H)) (image_step U F.toSubmodule hU B c)

/-- Every actual cut in a packet commutes with an isometry on its initial source. -/
theorem closed_image_chain (U : H →L[ℂ] H) (F : ClosedSubmodule ℂ H)
    (hU : ∀ v∈F,‖U v‖=‖v‖) (B : ℕ → H →L[ℂ] H) (c : ℝ) (n : ℕ) :
    closedImage U (chain F (fun i => B i*U) c n)
      (fun v hv => hU v (chain_antitone F (fun i => B i*U) c (Nat.zero_le n) hv))=
      chain (closedImage U F hU) B c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := closed_image_step U (chain F (fun i => B i*U) c n)
      (fun v hv => hU v (chain_antitone F (fun i => B i*U) c (Nat.zero_le n) hv)) (B n) c
    exact hh.trans (congrArg (fun V => step V (B n) c) ih)

theorem image_chain_projection (U : H →L[ℂ] H) (F : ClosedSubmodule ℂ H)
    (hU : ∀ v∈F,‖U v‖=‖v‖) (B : ℕ → H →L[ℂ] H) (c : ℝ) (n : ℕ) :
    (chain (closedImage U F hU) B c n).toSubmodule.starProjection=
      U*(chain F (fun i => B i*U) c n).toSubmodule.starProjection*star U := by
  have hh := congrArg (fun V : ClosedSubmodule ℂ H => V.toSubmodule.starProjection)
    (closed_image_chain U F hU B c n)
  exact hh.symm.trans (image_projection U _ _)

#print axioms closed_image_step
#print axioms closed_image_chain
#print axioms image_chain_projection
end QuantitativeEulerEndpointIsometricImage
