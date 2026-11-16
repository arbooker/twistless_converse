module

public import QuantitativeMaassStrongLocalNewFilterV1
public import QuantitativeMaassDivisorNewBandFilterV1
public import QuantitativeMaassTotalNewBandApproximationV1
public import AsymptoticClassicalNewDimensionAdmissibleV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped Topology
open QuantitativeNinaMaass
namespace QuantitativeMaass.Strong

local instance (N : ℕ) (hN : 0 < N) :
    NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

local instance (N : ℕ) (hN : 0 < N) :
    InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (U : Submodule ℂ (S.parityBand a b σ)) : U.HasOrthogonalProjection := by
  let : CompleteSpace U := FiniteDimensional.complete ℂ _
  infer_instance



theorem divisorSimpleNewBandFilter_weighted_energy {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0<M} {hN : 0<N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (p : ℕ) [Fact p.Prime] (hpMN : p*M=N) (hpM : ¬p∣M)
    (σ D W : ℝ) (hD : 0≤D)
    (b : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in Filter.atTop,0<ε t)
    (hproduct : Filter.Tendsto (fun t => ε t*slowScale t) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun t => Real.exp (W*strongScale t)*finiteBandEnergy (b t)
      (divisorSimpleNewBandFilter S T hMN p (t-Real.exp (D*strongScale t))
        (t+Real.exp (D*strongScale t)) σ (growingLVDegree t)-
        (S.traceNewParityBand T hMN (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ).starProjection)/(t*ε t))
      Filter.atTop (nhds 0) := by
  subst N
  simpa only [divisorSimpleNewBandFilter_eq] using
    simpleNewBandFilter_weighted_energy S p T hpM σ D W hD b ε hε hproduct


#print axioms divisorSimpleNewBandFilter_weighted_energy
end QuantitativeMaass.Strong
