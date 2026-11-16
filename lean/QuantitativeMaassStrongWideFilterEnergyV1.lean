module

public import QuantitativeMaassStrongWideFilterLimitV1
public import QuantitativeMaassFiniteFilterEnergyV1
public import QuantitativeMaassStrongWidePhysicalFilterV1

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open scoped Topology SchwartzMap FourierTransform

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

/-- The actual old-band filter error has the same weighted decay as its
trace excess, on an exponentially growing band, in every choice of orthonormal band bases. -/
theorem weighted_wide_physical_old_filter_energy {M : ℕ} [NeZero M] {hM : 0<M}
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
        (((1-(1/2:ℂ) • oldBandSum S p T (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ)^
          (growingLVDegree t)).toContinuousLinearMap-
          (oldBandSum S p T (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ).ker.starProjection)/(t*ε t))
      atTop (𝓝 0) := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  apply squeeze_zero' _ _ (weighted_wide_physical_old_filter_trace_approximation
    S p T hpM σ D W hD ε hε hproduct)
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (finiteBandEnergy_nonneg _ _))
      (mul_pos ht he).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    apply div_le_div_of_nonneg_right _ (mul_pos ht he).le
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    obtain ⟨hA,hAA,hB,hBB⟩ := oldBand_projections S p T hpM
      (Nat.gcdA p M) (Nat.gcdB p M) huv (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ
    have hh := finiteBandEnergy_half_filter_le
      (oldBandSum S p T (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ)
      (oldBandSum_symmetric S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv
        (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ)
      (fun i => two_projection_spectrum_bounds _ _ hA hB hAA hBB i)
      (growingLVDegree t) (b t)
    have hk := congrArg
      (fun U : Submodule ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ) => (finrank ℂ U : ℝ))
      (oldBandSum_kernel S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv
        (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ)
    exact (hh.trans (sub_le_sub_left hk.symm.le _)).trans (le_abs_self _)

#print axioms weighted_wide_physical_old_filter_energy

end QuantitativeMaass.Strong
