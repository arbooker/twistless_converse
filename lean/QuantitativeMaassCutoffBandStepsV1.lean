module

public import QuantitativeMaassNestedCutoffOperatorEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem cuspidalCutoff_norm_le (N : ℕ) (hN : 0<N) (b : Cutoff N) :
    ‖cuspidalCutoff N hN b‖≤b.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg
  intro x
  apply ((localCuspidalSpace N hN).norm_orthogonalProjectionOnto_apply_le _).trans
  exact (quotientLocalization N b.value b.smooth).le_of_opNorm_le
    (quotientLocalization_norm N b.value b.smooth b.invariant b.bound_nonneg
      b.value_bound b.gradient_bound) x

/-- The actual bounded cutoff on the cuspidal space includes its cusp
projection, rather than assuming multiplication preserves that space. -/
def cuspidalCutoffEndomorphism (N : ℕ) (hN : 0<N) (b : Cutoff N) :
    localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (cuspidalCutoff N hN b).comp (localCuspidalSpace N hN).subtypeL

theorem cuspidalCutoffEndomorphism_norm_le (N : ℕ) (hN : 0<N) (b : Cutoff N) :
    ‖cuspidalCutoffEndomorphism N hN b‖≤b.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg
  intro x
  exact (cuspidalCutoff N hN b).le_of_opNorm_le (cuspidalCutoff_norm_le N hN b) x.val

/-- One actual cutoff followed by projection onto the enlarged band. -/
def cutoffBandStep {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : Cutoff N) (t B L : ℝ) :
    S.band (t-B) (t+B) →L[ℂ] S.band (t-(B+L+2)) (t+(B+L+2)) :=
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  V.orthogonalProjectionOnto.comp
    ((cuspidalCutoffEndomorphism N hN b).comp (S.band (t-B) (t+B)).subtypeL)

theorem cutoffBandStep_norm_le {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : Cutoff N) (t B L : ℝ) : ‖cutoffBandStep S b t B L‖≤b.bound := by
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  apply ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg
  intro x
  apply (V.norm_orthogonalProjectionOnto_apply_le _).trans
  exact (cuspidalCutoffEndomorphism N hN b).le_of_opNorm_le
    (cuspidalCutoffEndomorphism_norm_le N hN b) x.val

theorem cutoffBandStep_defect {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : Cutoff N) (t B L : ℝ) (x : S.band (t-B) (t+B)) :
    cuspidalCutoffEndomorphism N hN b x.val-(cutoffBandStep S b t B L x).val=
      nestedBandRemainder S b t B L (x.val:AutomorphicSpace N) := rfl

#print axioms cuspidalCutoff_norm_le
#print axioms cuspidalCutoffEndomorphism_norm_le
#print axioms cutoffBandStep_norm_le
#print axioms cutoffBandStep_defect

end QuantitativeMaass.Weighted
