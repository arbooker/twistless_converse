module

public import QuantitativeMaassQuotientWeightWordCountV1
public import QuantitativeMaassFixedCompressionEnergyV1

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

/-- Inclusion of actual spectral bands from interval containment. -/
theorem cuspEnergyBand_mono {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {a b c d : ℝ} (ha : c≤a) (hb : b≤d) : S.band a b≤S.band c d := by
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  refine ⟨⟨i.val,?_,?_⟩,rfl⟩
  · exact i.property.1
  · exact ⟨ha.trans i.property.2.1,i.property.2.2.trans hb⟩

def quotientWeightOuterProjection {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (t B : ℝ) : localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  let : FiniteDimensional ℂ (S.band (t-B) (t+B)) := S.band_finiteDimensional _ _
  (S.band (t-B) (t+B)).starProjection

theorem quotientWeightOuterProjection_norm {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (t B : ℝ) : ‖quotientWeightOuterProjection S t B‖≤1 := by
  let : FiniteDimensional ℂ (S.band (t-B) (t+B)) := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(S.band (t-B) (t+B)).starProjection x‖≤1*‖x‖
  simpa only [one_mul] using (S.band (t-B) (t+B)).norm_starProjection_apply_le x

/-- Repeated compression to one fixed outer band, as required by polynomial
functional calculus on the restricted Gram. -/
def quotientWeightFixedPath {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L B : ℝ) :
    ℕ → cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN
  | 0 => (cutoffWordBand S t L 0).subtypeL
  | n+1 => ((quotientWeightOuterProjection S t B).comp
      (normalizedCuspidalQuotientWeight N hN hδ hν)).comp
        (quotientWeightFixedPath S hδ hν t L B n)

theorem quotientWeightFixedPath_norm {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L B : ℝ) (n : ℕ) :
    ‖quotientWeightFixedPath S hδ hν t L B n‖≤1 := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x.val‖≤1*‖x‖
    simp
  | succ n ih =>
    have ha := normalizedCuspidalQuotientWeight_norm N hN hδ hν
    have hp := quotientWeightOuterProjection_norm S t B
    have hpa : ‖(quotientWeightOuterProjection S t B).comp
        (normalizedCuspidalQuotientWeight N hN hδ hν)‖≤1 := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      nlinarith [norm_nonneg (quotientWeightOuterProjection S t B),
        norm_nonneg (normalizedCuspidalQuotientWeight N hN hδ hν)]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg ((quotientWeightOuterProjection S t B).comp
      (normalizedCuspidalQuotientWeight N hN hδ hν)),
      norm_nonneg (quotientWeightFixedPath S hδ hν t L B n)]

theorem quotientWeightOuterProjection_fixes_path {N : ℕ} {hN : 0<N}
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (t L B : ℝ) (j : ℕ) (hj : cutoffWordRadius L j≤B) :
    (quotientWeightOuterProjection S t B).comp
      (quotientWeightBandPathAmbient S hδ hν t L j)=
        quotientWeightBandPathAmbient S hδ hν t L j := by
  let : FiniteDimensional ℂ (S.band (t-B) (t+B)) := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.ext
  intro x
  change (S.band (t-B) (t+B)).starProjection
    (quotientWeightBandPathAmbient S hδ hν t L j x)=quotientWeightBandPathAmbient S hδ hν t L j x
  apply (S.band (t-B) (t+B)).starProjection_eq_self_iff.mpr
  exact cuspEnergyBand_mono S (by linarith) (by linarith)
    (quotientWeightBandPath S hδ hν t L j x).property

#print axioms cuspEnergyBand_mono
#print axioms quotientWeightOuterProjection_norm
#print axioms quotientWeightFixedPath_norm
#print axioms quotientWeightOuterProjection_fixes_path

end QuantitativeMaass
