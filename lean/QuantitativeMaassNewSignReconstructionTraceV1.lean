module

public import QuantitativeMaassNewSignReconstructionV1
public import QuantitativeMaassContractionTraceErrorV1
public import QuantitativeHolomorphicNewtonContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson QuantitativeHolomorphic QuantitativeNinaMaass
namespace QuantitativeMaass
open Weighted (cutoffWordBand)
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- Ambient polynomial reconstruction on the original unit input band. -/
def newSignAmbientReconstruction {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (t L : ℝ) (n : ℕ) : cutoffWordBand S t L 0 →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
    ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) (inverseSqrtPolynomial n)).comp
      (cutoffWordBand S t L 0).subtypeL)

theorem newSignAmbientReconstruction_norm {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (t L : ℝ) (n : ℕ) : ‖newSignAmbientReconstruction S hδ hν χ t L n‖≤1 := by
  have hn := polynomialNormalizedReconstruction_norm_le
    (newSignExtendedWeightedEmbedding N hN hδ hν χ)
    (newSignExtendedWeightedEmbedding_norm N hN hδ hν χ) n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hh := (polynomialNormalizedReconstruction (newSignExtendedWeightedEmbedding N hN hδ hν χ) n).le_of_opNorm_le hn x.val
  simp only [polynomialNormalizedReconstruction,newSignExtendedWeightedEmbedding_gram,
    ContinuousLinearMap.comp_apply,one_mul] at hh ⊢
  change ‖(newSignExtendedWeightedEmbedding N hN hδ hν χ)
    ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) (inverseSqrtPolynomial n)) x.val)‖≤‖x.val‖
  exact hh

theorem newSignBandReconstruction_norm {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (t L B : ℝ) (n : ℕ) : ‖newSignBandReconstruction S hδ hν χ t L B n‖≤1 := by
  let K := S.band (t-B) (t+B)
  let R := (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp K.subtypeL
  have hR : ‖R‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    exact (newSignExtendedWeightedEmbedding N hN hδ hν χ).le_of_opNorm_le
      (newSignExtendedWeightedEmbedding_norm N hN hδ hν χ) x.val
  have hn := polynomialNormalizedReconstruction_norm_le R hR n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hh := (polynomialNormalizedReconstruction R n).le_of_opNorm_le hn (K.orthogonalProjectionOnto x.val)
  simp only [one_mul] at hh ⊢
  exact hh.trans (K.norm_orthogonalProjectionOnto_apply_le x.val)

/-- Trace comparison for the actual reconstructions; both are contractions
by the Newton spectral invariant, including when the Gram has a kernel. -/
theorem newSign_reconstruction_trace_error {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (t L B : ℝ) (n : ℕ) (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0))
    (T : Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0)) (hT : ‖T‖≤1) :
    (∑ i,((inner ℂ (T (newSignAmbientReconstruction S hδ hν χ t L n (v i)))
      (newSignAmbientReconstruction S hδ hν χ t L n (v i))).re-
      (inner ℂ (T (newSignBandReconstruction S hδ hν χ t L B n (v i)))
      (newSignBandReconstruction S hδ hν χ t L B n (v i))).re))^2≤
      16*(Module.finrank ℂ (cutoffWordBand S t L 0):ℝ)*finiteSourceEnergy v
        (newSignAmbientReconstruction S hδ hν χ t L n-newSignBandReconstruction S hδ hν χ t L B n) := by
  have hu (i : ι) : ‖newSignAmbientReconstruction S hδ hν χ t L n (v i)‖≤1 := by
    simpa only [v.orthonormal.norm_eq_one i,one_mul] using
      (newSignAmbientReconstruction S hδ hν χ t L n).le_of_opNorm_le
        (newSignAmbientReconstruction_norm S hδ hν χ t L n) (v i)
  have hv (i : ι) : ‖newSignBandReconstruction S hδ hν χ t L B n (v i)‖≤1 := by
    simpa only [v.orthonormal.norm_eq_one i,one_mul] using
      (newSignBandReconstruction S hδ hν χ t L B n).le_of_opNorm_le
        (newSignBandReconstruction_norm S hδ hν χ t L B n) (v i)
  have hh := contraction_quadratic_trace_error T hT
    (fun i => newSignBandReconstruction S hδ hν χ t L B n (v i))
    (fun i => newSignAmbientReconstruction S hδ hν χ t L n (v i)) hv hu
  rw [Module.finrank_eq_card_basis v.toBasis]
  exact hh

#print axioms newSignAmbientReconstruction_norm
#print axioms newSignBandReconstruction_norm
#print axioms newSign_reconstruction_trace_error
end QuantitativeMaass
