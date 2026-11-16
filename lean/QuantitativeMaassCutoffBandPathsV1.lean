module

public import QuantitativeMaassCutoffBandStepsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
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

def cutoffWordRadius (L : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => cutoffWordRadius L n+L+2

theorem cutoffWordRadius_eq (L : ℝ) (n : ℕ) :
    cutoffWordRadius L n=1+(n:ℝ)*(L+2) := by
  induction n with
  | zero => simp [cutoffWordRadius]
  | succ n ih => simp only [cutoffWordRadius,ih,Nat.cast_add,Nat.cast_one]; ring

abbrev cutoffWordBand {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (t L : ℝ) (n : ℕ) := S.band (t-cutoffWordRadius L n) (t+cutoffWordRadius L n)

/-- Successive genuine band compressions, with a larger band at every step. -/
def cutoffBandPath {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (t L : ℝ) :
    (n : ℕ) → cutoffWordBand S t L 0 →L[ℂ] cutoffWordBand S t L n
  | 0 => ContinuousLinearMap.id ℂ _
  | n+1 => (cutoffBandStep S (b n) t (cutoffWordRadius L n) L).comp
      (cutoffBandPath S b t L n)

/-- The same word without the intermediate spectral projections. The
cuspidal projection remains part of each cutoff factor. -/
def cutoffAmbientPath {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (t L : ℝ) :
    ℕ → cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN
  | 0 => (cutoffWordBand S t L 0).subtypeL
  | n+1 => (cuspidalCutoffEndomorphism N hN (b n)).comp (cutoffAmbientPath S b t L n)

def cutoffBandPathAmbient {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (t L : ℝ) (n : ℕ) :
    cutoffWordBand S t L 0 →L[ℂ] localCuspidalSpace N hN :=
  (cutoffWordBand S t L n).subtypeL.comp (cutoffBandPath S b t L n)

theorem cutoffBandPath_norm_le {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (hb : ∀ j,(b j).bound≤1) (t L : ℝ) (n : ℕ) :
    ‖cutoffBandPath S b t L n‖≤1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    have hs := (cutoffBandStep_norm_le S (b n) t (cutoffWordRadius L n) L).trans (hb n)
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg (cutoffBandStep S (b n) t (cutoffWordRadius L n) L),
      norm_nonneg (cutoffBandPath S b t L n)]

theorem cutoffBandPath_defect {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (t L : ℝ) (n : ℕ) (x : cutoffWordBand S t L 0) :
    cuspidalCutoffEndomorphism N hN (b n) (cutoffBandPathAmbient S b t L n x)-
      cutoffBandPathAmbient S b t L (n+1) x=
      nestedBandRemainder S (b n) t (cutoffWordRadius L n) L
        ((cutoffBandPath S b t L n x).val:AutomorphicSpace N) :=
  cutoffBandStep_defect S (b n) t (cutoffWordRadius L n) L (cutoffBandPath S b t L n x)

#print axioms cutoffWordRadius_eq
#print axioms cutoffBandPath_norm_le
#print axioms cutoffBandPath_defect

end QuantitativeMaass.Weighted
