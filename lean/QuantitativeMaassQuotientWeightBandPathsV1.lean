module

public import QuantitativeMaassQuotientWeightBandStepsV1
public import QuantitativeMaassCutoffBandPathsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

/-- Successive spectral compressions of the normalized literal cuspidal Gram. -/
def quotientWeightBandPath {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) :
    (n : ℕ) → cutoffWordBand S t L 0 →L[ℂ] cutoffWordBand S t L n
  | 0 => ContinuousLinearMap.id ℂ _
  | n+1 => (quotientWeightBandStep S hδ hν t (cutoffWordRadius L n) L).comp
      (quotientWeightBandPath S hδ hν t L n)

/-- The same normalized Gram word without the intermediate band projections.
The cuspidal projection remains part of every factor. -/
def quotientWeightAmbientPath {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) :
    ℕ → cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN
  | 0 => (cutoffWordBand S t L 0).subtypeL
  | n+1 => (normalizedCuspidalQuotientWeight N hN hδ hν).comp (quotientWeightAmbientPath S hδ hν t L n)

def quotientWeightBandPathAmbient {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) (n : ℕ) :
    cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN :=
  (cutoffWordBand S t L n).subtypeL.comp (quotientWeightBandPath S hδ hν t L n)

theorem quotientWeightBandPath_norm {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) (n : ℕ) :
    ‖quotientWeightBandPath S hδ hν t L n‖≤1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    have hs := quotientWeightBandStep_norm S hδ hν t (cutoffWordRadius L n) L
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg (quotientWeightBandStep S hδ hν t (cutoffWordRadius L n) L),
      norm_nonneg (quotientWeightBandPath S hδ hν t L n)]

theorem quotientWeightBandPath_defect {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) (n : ℕ) (x : cutoffWordBand S t L 0) :
    normalizedCuspidalQuotientWeight N hN hδ hν (quotientWeightBandPathAmbient S hδ hν t L n x)-
      quotientWeightBandPathAmbient S hδ hν t L (n+1) x=
      (quotientWeightNormalization δ:ℂ) • quotientWeightNestedRemainder S hδ hν t (cutoffWordRadius L n) L
        ((quotientWeightBandPath S hδ hν t L n x).val:AutomorphicSpace N) :=
  quotientWeightBandStep_defect S hδ hν t (cutoffWordRadius L n) L (quotientWeightBandPath S hδ hν t L n x)

#print axioms quotientWeightBandPath_norm
#print axioms quotientWeightBandPath_defect

end QuantitativeMaass
