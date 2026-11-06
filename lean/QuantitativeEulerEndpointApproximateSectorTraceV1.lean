module

public import QuantitativeEulerEndpointApproximateTraceV1
public import QuantitativeEulerEndpointNestedCountV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace QuantitativeHolomorphic
open scoped InnerProduct
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The actual full coefficient-sector rank is controlled by the weighted
holomorphic trace. Positivity and summability are proved from reconstruction;
the only residual premise concerns actual normalized sector vectors. -/
theorem sector_finrank_mul_le_trace (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : 0≤F) (δ : ℝ)
    (herr : ∀ a,‖F (normalizedSectorCoordinates A hN P h e a)-normalizedSectorCoordinates A hN P h e a‖≤
      δ*‖normalizedSectorCoordinates A hN P h e a‖) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      trace fb (compressedSandwich (normalizedCountReconstruction A hN P h e) F W) := by
  intro P' W fb
  let U := normalizedCountReconstruction A hN P h e
  let C := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P'.s) (P'.s+4) e P'.epsilon_pos (by omega)
  let T := compressedSandwich U F W
  have ht : 0≤T := by
    apply nonneg_iff_isPositive.mpr
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj (U.adjoint.comp W.subtypeL)
    simpa only [T,compressedSandwich,adjoint_comp,adjoint_adjoint,ContinuousLinearMap.comp_assoc] using hh
  have hs : Summable (fun l => (⟪T (fb l),fb l⟫_ℂ).re) :=
    compressedSandwich_summable U F W fb (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos
      (normalizedCountReconstruction_fourier_gram A hN P h e)
  have he : ∀ w∈LinearMap.range C,‖T w-w‖≤δ*‖w‖ := by
    rintro w ⟨a,rfl⟩
    let v := normalizedSectorCoordinates A hN P h e a
    have hu : U v=(C a:Space) := normalizedSectorCoordinates_reconstruct A hN P h e a
    have hx : W.subtypeL.adjoint (U v)=C a := by
      rw [hu,W.adjoint_subtypeL]
      exact W.orthogonalProjectionOnto_mem_subspace_eq_self (C a)
    have hn : ‖v‖=‖C a‖ := by
      rw [←normalizedCountReconstruction_norm A hN P h e v]
      exact congrArg norm hu
    have hp : ‖W.subtypeL.adjoint‖≤1 := by
      rw [adjoint.norm_map]
      apply opNorm_le_bound _ zero_le_one
      intro w
      simp
    calc
      ‖T (C a)-C a‖=‖W.subtypeL.adjoint (U (F v-v))‖ := by
        rw [map_sub,map_sub,hx]
        rfl
      _ ≤ ‖U (F v-v)‖ := (W.subtypeL.adjoint.le_opNorm _).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      _ = ‖F v-v‖ := normalizedCountReconstruction_norm A hN P h e _
      _ ≤ δ*‖v‖ := herr a
      _ = δ*‖C a‖ := by rw [hn]
  let := AsymptoticRamifiedSectors.sector_finiteDimensional hN A P h (h+1+P'.s) e
  have hh := finrank_mul_le_trace fb T ht (LinearMap.range C) δ he hs
  rw [AsymptoticRamifiedSectors.cylinderMap_finrank] at hh
  exact hh

#print axioms sector_finrank_mul_le_trace
end QuantitativeEulerEndpointApproximateTrace
