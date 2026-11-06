module

public import QuantitativeEulerEndpointCutIntertwiningV1
public import QuantitativeEulerEndpointIsometricImageV1
public import QuantitativeSpectralCornerCutRowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointIsometricImage
open ContinuousLinearMap QuantitativeSpectralCornerCutRow QuantitativeSpectralCutRow
open QuantitativeEulerEndpointCutIntertwining

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem next_projection_intertwines (F G : Submodule ℂ H) [CompleteSpace F] [CompleteSpace G]
    (B C T : H →L[ℂ] H) (hT : T*F.starProjection=G.starProjection*T)
    (hgram : (star (restricted G C)*restricted G C)*T=T*(star (restricted F B)*restricted F B))
    (c : ℝ) : T*(nextSpace F B c).starProjection=(nextSpace G C c).starProjection*T := by
  have hh := highAt_projection_intertwines
    (star (restricted F B)*restricted F B) (star (restricted G C)*restricted G C) T
    (IsSelfAdjoint.star_mul_self _) (IsSelfAdjoint.star_mul_self _) hgram (c^2)
  change T*removed (restricted F B) c=removed (restricted G C) c*T at hh
  rw [nextSpace_projection,nextSpace_projection,mul_sub,sub_mul,hT,hh]

theorem image_step_projection (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v∈F,‖U v‖=‖v‖) (B : H →L[ℂ] H) (c : ℝ) :
    (nextSpace (imageSpace U F hU) B c).starProjection=
      U*(nextSpace F (B*U) c).starProjection*star U := by
  let P := F.starProjection
  let G := imageSpace U F hU
  let Q := G.starProjection
  let T := U*P
  have hP : IsStarProjection P := isStarProjection_starProjection (U:=F)
  have hQ : IsStarProjection Q := isStarProjection_starProjection (U:=G)
  have hTT : T*star T=Q := restricted_cogram U F hU
  have hTP : T*P=T := by dsimp only [T]; rw [mul_assoc,hP.isIdempotentElem.eq]
  have hTg : star T*T=P := restricted_gram U F hU
  have hQT : Q*T=T := by rw [←hTT,mul_assoc,hTg,hTP]
  have hR : restricted F (B*U)=B*T := by unfold restricted T P; rw [mul_assoc]
  have hC : restricted G B=B*Q := rfl
  have hi : (star (restricted G B)*restricted G B)*T=T*(star (restricted F (B*U))*restricted F (B*U)) := by
    rw [hR,hC,star_mul,star_mul,hQ.isSelfAdjoint.star_eq]
    calc
      _ = Q*star B*B*T := by simp only [mul_assoc,hQT]
      _ = _ := by rw [←hTT]; simp only [mul_assoc]
  have hstep := next_projection_intertwines F G (B*U) B T (hTP.trans hQT.symm) hi c
  let V := nextSpace F (B*U) c
  let W := nextSpace G B c
  have hPV : P*V.starProjection=V.starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    exact F.starProjection_eq_self_iff.mpr (nextSpace_le F (B*U) c (V.starProjection_apply_mem v))
  have hVP : V.starProjection*P=V.starProjection :=
    V.starProjection_comp_starProjection_of_le (nextSpace_le F (B*U) c)
  have hWQ : W.starProjection*Q=W.starProjection :=
    W.starProjection_comp_starProjection_of_le (nextSpace_le G B c)
  calc
    W.starProjection = W.starProjection*Q := hWQ.symm
    _ = W.starProjection*(T*star T) := by rw [hTT]
    _ = (T*V.starProjection)*star T := by rw [←mul_assoc,←hstep]
    _ = U*V.starProjection*star U := by
      dsimp only [T]
      rw [star_mul,hP.isSelfAdjoint.star_eq]
      calc
        _ = U*(P*V.starProjection)*P*star U := by simp only [mul_assoc]
        _ = _ := by rw [hPV,mul_assoc U V.starProjection P,hVP]

theorem image_step (U : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F]
    (hU : ∀ v∈F,‖U v‖=‖v‖) (B : H →L[ℂ] H) (c : ℝ) :
    imageSpace U (nextSpace F (B*U) c)
      (fun v hv => hU v (nextSpace_le F (B*U) c hv))=
      nextSpace (imageSpace U F hU) B c := by
  have he := image_projection U (nextSpace F (B*U) c)
    (fun v hv => hU v (nextSpace_le F (B*U) c hv))
  have hh := image_step_projection U F hU B c
  have hp : (imageSpace U (nextSpace F (B*U) c)
      (fun v hv => hU v (nextSpace_le F (B*U) c hv))).starProjection=
      (nextSpace (imageSpace U F hU) B c).starProjection := he.trans hh.symm
  ext v
  rw [←Submodule.starProjection_eq_self_iff,←Submodule.starProjection_eq_self_iff,hp]

#print axioms next_projection_intertwines
#print axioms image_step_projection
#print axioms image_step
end QuantitativeEulerEndpointIsometricImage
