module

public import QuantitativeMaassQuotientWeightNestedEnergyV1
public import QuantitativeMaassQuotientWeightContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

/-- One normalized actual Gram factor followed by a genuine enlarged-band projection. -/
def quotientWeightBandStep {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t B L : ℝ) :
    S.band (t-B) (t+B) →L[ℂ] S.band (t-(B+L+2)) (t+(B+L+2)) :=
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  V.orthogonalProjectionOnto.comp
    ((normalizedCuspidalQuotientWeight N hN hδ hν).comp (S.band (t-B) (t+B)).subtypeL)

theorem quotientWeightBandStep_norm {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t B L : ℝ) :
    ‖quotientWeightBandStep S hδ hν t B L‖≤1 := by
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  apply (V.norm_orthogonalProjectionOnto_apply_le _).trans
  exact (normalizedCuspidalQuotientWeight N hN hδ hν).le_of_opNorm_le
    (normalizedCuspidalQuotientWeight_norm N hN hδ hν) x.val

theorem quotientWeightBandStep_defect {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t B L : ℝ)
    (x : S.band (t-B) (t+B)) :
    normalizedCuspidalQuotientWeight N hN hδ hν x.val-(quotientWeightBandStep S hδ hν t B L x).val=
      (quotientWeightNormalization δ:ℂ) • quotientWeightNestedRemainder S hδ hν t B L
        (x.val:AutomorphicSpace N) := by
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  change (quotientWeightNormalization δ:ℂ) • cuspidalQuotientWeight N hN hδ hν (x.val:AutomorphicSpace N)-
      (V.orthogonalProjectionOnto ((quotientWeightNormalization δ:ℂ) •
        cuspidalQuotientWeight N hN hδ hν (x.val:AutomorphicSpace N))).val=
    (quotientWeightNormalization δ:ℂ) • (cuspidalQuotientWeight N hN hδ hν (x.val:AutomorphicSpace N)-
      V.starProjection (cuspidalQuotientWeight N hN hδ hν (x.val:AutomorphicSpace N)))
  rw [map_smul]
  exact (smul_sub _ _ _).symm

/-- The normalized step retains the proved leakage bound after any bounded
map into the input band. -/
theorem quotientWeightBandStep_defect_energy {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (v : OrthonormalBasis ι ℂ E) (t B L : ℝ) (hL : 0<L) (ht : B+L+2≤t)
    (T : E →L[ℂ] S.band (t-B) (t+B)) :
    (∑ i,‖normalizedCuspidalQuotientWeight N hN hδ hν (T (v i)).val-
      (quotientWeightBandStep S hδ hν t B L (T (v i))).val‖^2)≤
      ‖T‖^2*(16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)/L^2) := by
  apply le_trans _ (quotientWeightNestedRemainder_precompose_energy S hδ hν v t B L hL ht T)
  apply Finset.sum_le_sum
  intro i _
  rw [quotientWeightBandStep_defect]
  exact pow_le_pow_left₀ (norm_nonneg _) (quotientWeightNormalization_smul_norm_le δ _) 2

#print axioms quotientWeightBandStep_norm
#print axioms quotientWeightBandStep_defect
#print axioms quotientWeightBandStep_defect_energy

end QuantitativeMaass
