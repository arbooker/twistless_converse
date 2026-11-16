module

public import QuantitativeMaassEmbeddingSubspaceNewtonV1
public import QuantitativeMaassNewSignGramPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter MeasureTheory AsymptoticClassicalPetersson QuantitativeHolomorphic QuantitativeNinaMaass
open scoped Topology

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- The genuine weighted embedding after projection to the new/sign source. -/
def newSignExtendedWeightedEmbedding (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    localCuspidalSpace N hN →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (normalizedCuspidalWeightedEmbedding N hN hδ hν).comp
    (cuspidalNewSignSpace N hN χ).starProjection

theorem newSignExtendedWeightedEmbedding_gram (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    (newSignExtendedWeightedEmbedding N hN hδ hν χ).adjoint.comp
      (newSignExtendedWeightedEmbedding N hN hδ hν χ)=newSignWeightedGram N hN hδ hν χ := by
  rw [newSignExtendedWeightedEmbedding,normalizedCuspidalWeightedEmbedding_restricted_gram,
    (isSelfAdjoint_starProjection (cuspidalNewSignSpace N hN χ)).adjoint_eq]
  rfl

theorem newSignExtendedWeightedEmbedding_norm (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    ‖newSignExtendedWeightedEmbedding N hN hδ hν χ‖≤1 := by
  have hh := ContinuousLinearMap.norm_adjoint_comp_self (newSignExtendedWeightedEmbedding N hN hδ hν χ)
  rw [newSignExtendedWeightedEmbedding_gram] at hh
  nlinarith [newSignWeightedGram_norm N hN hδ hν χ,
    norm_nonneg (newSignExtendedWeightedEmbedding N hN hδ hν χ)]

/-- The actual finite-band normalized reconstruction, restricted to the
original unit input band. -/
def newSignBandReconstruction {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (n : ℕ) :
    cutoffWordBand S t L 0 →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (polynomialNormalizedReconstruction
    ((newSignExtendedWeightedEmbedding N hN hδ hν χ).comp (S.band (t-B) (t+B)).subtypeL) n).comp
      ((S.band (t-B) (t+B)).orthogonalProjectionOnto.comp (cutoffWordBand S t L 0).subtypeL)

theorem newSignBandReconstruction_eq {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (hB : 1≤B) (n : ℕ) :
    newSignBandReconstruction S hδ hν χ t L B n=
      (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
        ((Polynomial.aeval ((quotientWeightOuterProjection S t B).comp
          (newSignWeightedGram N hN hδ hν χ)) (inverseSqrtPolynomial n)).comp
            (cutoffWordBand S t L 0).subtypeL) := by
  symm
  rw [←newSignExtendedWeightedEmbedding_gram N hN hδ hν χ]
  apply embedding_subspace_newton
  intro x
  exact cuspEnergyBand_mono S (by linarith : t-B≤t-1) (by linarith : t+1≤t+B) x.property

/-- The actual finite-band reconstruction and the ambient actual Gram
polynomial have negligible weighted error on the original unit source band.
No inverse-square-root assertion on the whole cusp space is made. -/
theorem weighted_newSign_reconstruction_compression (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (W : ℝ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,0<D ∧ ∃ F : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*fourthRootScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,
        ∀ B : ℝ,cutoffWordRadius (Real.exp (D*fourthRootScale t))
          (inverseSqrtPolynomial (bandNewtonDepth t)).natDegree≤B →
        ∀ {ι : Type*} [Fintype ι]
          (v : OrthonormalBasis ι ℂ (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0)),
        finiteSourceEnergy v
          ((newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
            ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ)
              (inverseSqrtPolynomial (bandNewtonDepth t))).comp
                (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0).subtypeL)-
          newSignBandReconstruction S hδ hν χ t (Real.exp (D*fourthRootScale t)) B
            (bandNewtonDepth t))≤F t := by
  obtain ⟨D,hD,F,hF,hbound⟩ := weighted_newSignGram_newton_compression N hN S hδ hν χ W ε hε hproduct
  refine ⟨D,hD,F,hF,?_⟩
  filter_upwards [hbound] with t ht
  intro B hB ι _ v
  have hB1 : 1≤B := by
    rw [Weighted.cutoffWordRadius_eq] at hB
    nlinarith [mul_nonneg (Nat.cast_nonneg (inverseSqrtPolynomial (bandNewtonDepth t)).natDegree :
      (0:ℝ)≤(inverseSqrtPolynomial (bandNewtonDepth t)).natDegree)
      (show 0≤Real.exp (D*fourthRootScale t)+2 by positivity)]
  rw [newSignBandReconstruction_eq S hδ hν χ _ _ B hB1,←ContinuousLinearMap.comp_sub]
  have hn : ‖newSignExtendedWeightedEmbedding N hN hδ hν χ‖^2≤1 := by
    nlinarith [newSignExtendedWeightedEmbedding_norm N hN hδ hν χ,
      norm_nonneg (newSignExtendedWeightedEmbedding N hN hδ hν χ)]
  exact (finiteSourceEnergy_left v _ _).trans
    (((mul_le_mul_of_nonneg_right hn (finiteSourceEnergy_nonneg v _)).trans_eq (one_mul _)).trans
      (ht B hB v))

#print axioms newSignExtendedWeightedEmbedding_gram
#print axioms newSignExtendedWeightedEmbedding_norm
#print axioms newSignBandReconstruction_eq
#print axioms weighted_newSign_reconstruction_compression

end QuantitativeMaass
