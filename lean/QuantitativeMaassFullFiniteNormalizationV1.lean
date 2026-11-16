module

public import QuantitativeMaassFullFiniteReconstructionV1
public import QuantitativeMaassNormalizationScaleV1
public import QuantitativeHolomorphicNewtonContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Finite Newton normalization of the genuine full weight-zero truncation. -/
def finiteNormalizedReconstruction (e : Sector N) (n d J : ℕ) :=
  polynomialNormalizedReconstruction
    ((countReconstructionBound A P)⁻¹ • finiteReconstruction A hN P e d J) n

theorem finiteNormalizedReconstruction_norm (e : Sector N) (n d J : ℕ) :
    ‖finiteNormalizedReconstruction A hN P e n d J‖≤1 := by
  exact polynomialNormalizedReconstruction_norm_le _
    (scaled_norm_le_one _ (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
      (finiteReconstruction_norm_le A hN P e d J)) n

/-- The exact original normalization is approximated in operator norm with
explicit fold, depth and Newton errors. All bounds hold at weight zero. -/
theorem finiteNormalizedReconstruction_error (e : Sector N) (n d J : ℕ) (hJ : 0<J) :
    ‖finiteNormalizedReconstruction A hN P e n d J-normalized A hN P e‖≤
      countReconstructionError A P d J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
        (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P) := by
  let R := reconstruction A hN P e
  let V := finiteReconstruction A hN P e d J
  let c := (countReconstructionBound A P)⁻¹
  have hB : 0<countReconstructionBound A P :=
    zero_lt_one.trans_le (countReconstructionBound_one_le A P)
  have hc : 0<c := inv_pos.mpr hB
  have hR := scaled_reconstruction_bounds R hB (reconstruction_norm_le A hN P e)
    (reconstruction_norm_ge A hN P e)
  have hV : ‖c • V‖≤1 := scaled_norm_le_one V hB (finiteReconstruction_norm_le A hN P e d J)
  have hδ : ‖c • V-c • R‖≤countReconstructionError A P d J :=
    scaled_difference_norm_le R V hc.le
      (inv_le_one_of_one_le₀ (countReconstructionBound_one_le A P))
      (finiteReconstruction_error A hN P e d J hJ)
  have he := finite_polynomial_normalization_closed_error (c • R) (c • V)
    (countGramLower_pos A P) (countGramLower_le_one A P) hR.2 hR.1
    (hV.trans (by norm_num)) hδ n
  have hn : normalizedReconstruction (c • R)=normalizedReconstruction R := by
    apply normalizedReconstruction_positive_smul R (by norm_num : (0:ℝ)<1) hc
    intro x
    simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg x)
      (reconstruction_norm_ge A hN P e x) 2
  rw [hn] at he
  exact he

/-- The same polynomial is lifted into the actual physical Hilbert space. -/
def finitePhysicalReconstruction (e : Sector N) (n d J : ℕ) :=
  AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
    (finiteNormalizedReconstruction A hN P e n d J)

theorem finitePhysicalReconstruction_error (e : Sector N) (n d J : ℕ) (hJ : 0<J) :
    ‖finitePhysicalReconstruction A hN P e n d J-
      (physicalIsometry A hN P e).toContinuousLinearMap‖≤
      countReconstructionError A P d J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
        (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P) := by
  have he : finitePhysicalReconstruction A hN P e n d J-
      (physicalIsometry A hN P e).toContinuousLinearMap=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        (finiteNormalizedReconstruction A hN P e n d J-normalized A hN P e) := by
    apply ContinuousLinearMap.ext
    intro x
    change AsymptoticCylinderLift.lift (finiteNormalizedReconstruction A hN P e n d J x)-
      AsymptoticCylinderLift.lift (normalized A hN P e x)=
      AsymptoticCylinderLift.lift
        (finiteNormalizedReconstruction A hN P e n d J x-normalized A hN P e x)
    exact (AsymptoticCylinderLift.lift.map_sub _ _).symm
  rw [he]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right
    (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)).trans
  rw [one_mul]
  exact finiteNormalizedReconstruction_error A hN P e n d J hJ

#print axioms finiteNormalizedReconstruction_norm
#print axioms finiteNormalizedReconstruction_error
#print axioms finitePhysicalReconstruction_error
end QuantitativeMaass.EulerHilbert.FullTerminal
