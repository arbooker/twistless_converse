module

public import QuantitativeMaassSectorParityBandFilterV1
public import QuantitativeMaassNormalizedWeightedEmbeddingV1
public import QuantitativeMaassCompressedTargetApproxV1
public import QuantitativeMaassNewtonCostV1
public import QuantitativeMaassFiniteSourceEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open Filter QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology
namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _


variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (a b σ : ℝ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

/-- The actual normalized cylinder embedding restricted to a fixed-parity band. -/
def parityBandWeightedEmbedding :
    T.parityBand a b σ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (normalizedCuspidalWeightedEmbedding N hN hδ hν).comp
    ((T.band a b).subtypeL.comp (T.parityBand a b σ).subtypeL)

theorem parityBandWeightedEmbedding_norm :
    ‖parityBandWeightedEmbedding N hN T a b σ hδ hν‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hh := (normalizedCuspidalWeightedEmbedding N hN hδ hν).le_opNorm x.val.val
  have hn := mul_le_mul_of_nonneg_right
    (normalizedCuspidalWeightedEmbedding_norm N hN hδ hν) (norm_nonneg x.val.val)
  exact hh.trans hn

/-- This Gram includes the cusp projection and both actual band inclusions. -/
def parityBandWeightedGram : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  (parityBandWeightedEmbedding N hN T a b σ hδ hν).adjoint.comp
    (parityBandWeightedEmbedding N hN T a b σ hδ hν)

theorem parityBandWeightedGram_norm :
    ‖parityBandWeightedGram N hN T a b σ hδ hν‖≤1 := by
  have hh := ContinuousLinearMap.norm_adjoint_comp_self
    (parityBandWeightedEmbedding N hN T a b σ hδ hν)
  have hn := parityBandWeightedEmbedding_norm N hN T a b σ hδ hν
  change ‖(parityBandWeightedEmbedding N hN T a b σ hδ hν).adjoint.comp
    (parityBandWeightedEmbedding N hN T a b σ hδ hν)‖≤1
  rw [hh]
  nlinarith [norm_nonneg (parityBandWeightedEmbedding N hN T a b σ hδ hν)]

theorem parityBandWeightedGram_eq :
    parityBandWeightedGram N hN T a b σ hδ hν=
      ((T.band a b).subtypeL.comp (T.parityBand a b σ).subtypeL).adjoint.comp
        ((normalizedCuspidalQuotientWeight N hN hδ hν).comp
          ((T.band a b).subtypeL.comp (T.parityBand a b σ).subtypeL)) :=
  normalizedCuspidalWeightedEmbedding_restricted_gram N hN hδ hν _

/-- Restricting to the sector before normalization gives exactly the
ambient compressed polynomial followed by the adjoint sector inclusion. -/
theorem parityBandWeightedEmbedding_sector_transport (e : Sector N) (n : ℕ) :
    (parityBandWeightedEmbedding N hN T a b σ hδ hν).comp
      (compressedNewtonPolynomial (parityBandWeightedGram N hN T a b σ hδ hν)
        (sectorParityBandSpace T a b σ e).starProjection n)=
      (QuantitativeHolomorphic.polynomialNormalizedReconstruction
        ((parityBandWeightedEmbedding N hN T a b σ hδ hν).comp
          (sectorParityBandSpace T a b σ e).subtypeL) n).comp
        (sectorParityBandSpace T a b σ e).subtypeL.adjoint := by
  let K := sectorParityBandSpace T a b σ e
  have hJ : K.subtypeL.adjoint.comp K.subtypeL=1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
    rfl
  have hP : K.subtypeL.comp K.subtypeL.adjoint=K.starProjection := by
    rw [Submodule.adjoint_subtypeL]
    rfl
  have hh := compressedNewtonPolynomial_transport
    (parityBandWeightedEmbedding N hN T a b σ hδ hν) K.subtypeL hJ n
  exact (congrArg (fun P : T.parityBand a b σ →L[ℂ] T.parityBand a b σ =>
    (parityBandWeightedEmbedding N hN T a b σ hδ hν).comp
      (compressedNewtonPolynomial (parityBandWeightedGram N hN T a b σ hδ hν) P n)) hP.symm).trans hh

#print axioms parityBandWeightedEmbedding_norm
#print axioms parityBandWeightedGram_norm
#print axioms parityBandWeightedGram_eq
#print axioms parityBandWeightedEmbedding_sector_transport
end QuantitativeMaass
