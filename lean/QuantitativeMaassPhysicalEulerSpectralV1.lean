module

public import QuantitativeMaassCylinderEulerSpectralV1
public import QuantitativeMaassEulerSectorCountV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

/-- The concrete bounded physical operator obtained by zero extension of
the capped translation-cylinder Abel operator. -/
def physicalCappedAbelOperator (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  cylinderZeroExtension.toContinuousLinearMap.comp
    ((cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs) ε hε t).comp
        cylinderZeroExtension.toContinuousLinearMap.adjoint)

/-- The physical operator acts spectrally on the same literal weighted
Euler classes used in the residual-compression counting theorem. -/
theorem physicalCappedAbelOperator_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    physicalCappedAbelOperator F hF hc R hR hs P.ε P.epsilon_pos (P.s+3)
      (principalEulerWeightedLp hN A P r σ hb)=
      cosinePacket (coshTimeTest F) r • principalEulerWeightedLp hN A P r σ hb := by
  let f := principalEulerCylinderLp hN A P r σ hb
  have hj : cylinderZeroExtension.toContinuousLinearMap.adjoint (cylinderZeroExtension f)=f := by
    simpa only [ContinuousLinearMap.comp_apply,one_apply_eq_self,
      LinearIsometry.coe_toContinuousLinearMap] using!
      congrArg (fun B => B f) cylinderZeroExtension.adjoint_comp_self
  rw [←principalEulerCylinderLp_physical hN A P r σ hb]
  change cylinderZeroExtension
    (cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs) P.ε P.epsilon_pos (P.s+3)
      (cylinderZeroExtension.toContinuousLinearMap.adjoint (cylinderZeroExtension f)))=_
  rw [hj,cylinderCappedAbelOperator_original hN A P r σ hb F hF hc hr R hR hs,map_smul]

#print axioms physicalCappedAbelOperator_original

/-- Zero extension and its adjoint preserve the cylinder operator bound. -/
theorem physicalCappedAbelOperator_norm (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    ‖physicalCappedAbelOperator F hF hc R hR hs ε hε t‖≤
      5*(1+(t:ℝ)*R)*Real.exp ((t:ℝ)*R+3)*‖coshWavePacket 0 F hF R hR hs‖ := by
  let B := cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) ε hε t
  have hj : ‖cylinderZeroExtension.toContinuousLinearMap.adjoint‖≤1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using
      cylinderZeroExtension.norm_toContinuousLinearMap_le
  have hb : ‖physicalCappedAbelOperator F hF hc R hR hs ε hε t‖≤‖B‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro v
    change ‖cylinderZeroExtension (B (cylinderZeroExtension.toContinuousLinearMap.adjoint v))‖≤_
    rw [cylinderZeroExtension_norm]
    calc
      _ ≤ ‖B‖*‖cylinderZeroExtension.toContinuousLinearMap.adjoint v‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖cylinderZeroExtension.toContinuousLinearMap.adjoint‖*‖v‖) :=
        mul_le_mul_of_nonneg_left (cylinderZeroExtension.toContinuousLinearMap.adjoint.le_opNorm v) (norm_nonneg B)
      _ ≤ ‖B‖*‖v‖ := mul_le_mul_of_nonneg_left
        (by nlinarith [norm_nonneg v]) (norm_nonneg B)
  exact hb.trans (cylinderCappedAbelOperator_spectral_norm F hF hc hr R hR hs ε hε t)

#print axioms physicalCappedAbelOperator_norm

end QuantitativeMaass
