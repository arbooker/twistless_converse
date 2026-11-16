module

public import QuantitativeMaassStrongWideFilterEnergyV1
public import QuantitativeMaassLocalNewBandFilterV1
public import QuantitativeMaassOldFilterContractionV1
public import QuantitativeArithmeticRepeatedTwoBandsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open scoped Topology
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


theorem simpleNewBandFilter_weighted_energy {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (σ D W : ℝ) (hD : 0≤D)
    (b : (t : ℝ) → OrthonormalBasis
      (Fin (finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*
      finiteBandEnergy (b t)
        (simpleNewBandFilter S p T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ (growingLVDegree t)-
          (S.traceNewParityBand T (Nat.dvd_mul_left M p)
            (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ).starProjection)/(t*ε t))
      atTop (𝓝 0) := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  have hk (a c : ℝ) := oldBandSum_kernel S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv a c σ
  simpa only [simpleNewBandFilter,hk] using
    weighted_wide_physical_old_filter_energy S p T hpM σ D W hD b ε hε hproduct


#print axioms simpleNewBandFilter_weighted_energy
end QuantitativeMaass.Strong
