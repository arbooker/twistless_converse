module

public import QuantitativeMaassCountingCapReconstructionV1
public import QuantitativeMaassFullRegularSourceV1
public import QuantitativeMaassWeightedTargetProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticSectorSigns QuantitativeNewGap QuantitativeHolomorphic
open QuantitativeMaass.EulerHilbert.FullTerminal
open FinitenessCertificate FinitenessGlobalHeight
open scoped lp
namespace QuantitativeMaass.CountingMetric
theorem extended_isometry_cogram_fixes {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U S : V→L[ℂ]H) (hU : U.adjoint.comp U=1) (hS : S.adjoint.comp S=1)
    (u : H) (hu : u∈U.range) :
    (U.comp S.adjoint) ((U.comp S.adjoint).adjoint u)=u := by
  obtain ⟨v,rfl⟩ := hu
  rw [adjoint_comp,adjoint_adjoint]
  change U ((S.adjoint.comp S) ((U.adjoint.comp U) v))=U v
  rw [hS,hU]
  rfl

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A)

theorem countingCapLift_normalized_range (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e) :
    let P' := AsymptoticReconstructedCount.parameters A P
    countingCapLift N P'.epsilon_pos (by omega : 1≤P'.s+3) z f∈
      (normalizedRegularReconstruction A hN P e z).range := by
  intro P'
  let B := countReconstructionBound A P
  let R := regularReconstruction A hN P e z
  have hB : 0<B := zero_lt_one.trans_le (countReconstructionBound_one_le A P)
  have hb := scaled_reconstruction_bounds R hB
    (regularReconstruction_bounds A hN P e z).1 (regularReconstruction_bounds A hN P e z).2
  change _∈(normalizedReconstruction (B⁻¹ • R)).range
  rw [normalizedEmbedding_range _ (sq_pos_of_pos (inv_pos.mpr hB)) hb.2]
  let u := countingCapLift N P'.epsilon_pos (by omega : 1≤P'.s+3) z f
  let v := AsymptoticOrbitRegion.restrict (AsymptoticCertificateOperators.highStrip P'.ε) z u
  refine ⟨B • v,?_⟩
  change (B⁻¹ : ℝ) • R (B • v)=u
  rw [map_smul_of_tower,smul_smul,inv_mul_cancel₀ hB.ne',one_smul]
  exact countingCapLift_common_extension A hN P e z hz f hf

/-- The normalized reconstruction cogram fixes the actual canonical cap
lift; no containment or reconstruction hypothesis remains. -/
theorem countingCapLift_normalized_cogram (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let u : AsymptoticRegularCompactBranch.Space := countingCapLift N P'.epsilon_pos (by omega : 1≤P'.s+3) z f
    let R : AsymptoticRegularCompactBranch.Space→L[ℂ]AsymptoticRegularCompactBranch.Space :=
      normalizedRegularAmbient A hN P e z
    R (R.adjoint u)=u := by
  intro P' u R
  apply extended_isometry_cogram_fixes
    (normalizedRegularReconstruction A hN P e z)
    (AsymptoticRegularReconstruction.TerminalSpace A P' z).subtypeL
  · exact (norm_map_iff_adjoint_comp_self _).mp (normalizedRegularReconstruction_norm A hN P e z)
  · exact AsymptoticOrbitRegion.adjoint_comp_subtype _ z
  · exact countingCapLift_normalized_range A hN P e z hz f hf

#print axioms countingCapLift_normalized_range
#print axioms countingCapLift_normalized_cogram
end QuantitativeMaass.CountingMetric
