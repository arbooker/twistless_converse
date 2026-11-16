module

public import QuantitativeMaassWeightedWideFilterLimitV1
public import QuantitativeMaassLowRankFilterLowerV1

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option diagnostics true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open scoped Topology SchwartzMap FourierTransform

namespace QuantitativeMaass

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



/-- For every good prime the physical two-old-projection polynomial has
trace equal to the actual local-new dimension up to an error which stays
o(t epsilon(t)) after every fixed exponential fourth-root-scale weight, even on exponentially growing spectral bands.
The smoothing kernel, threshold, Bezout data and all error bounds are
constructed, rather than assumed. -/
theorem weighted_wide_physical_old_filter_trace_approximation {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (σ D W : ℝ) (hD : 0≤D)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      Real.exp (W*fourthRootScale t)*|(LinearMap.trace ℂ (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ)
        ((1-(1/2:ℂ) • oldBandSum S p T (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ)^(growingMomentDegree t))).re-
        (finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ):ℝ)|/(t*ε t))
      atTop (𝓝 0) := by
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  have hMp : (M:ZMod p)≠0 := fun h => hpM ((ZMod.natCast_eq_zero_iff M p).mp h)
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  let ρ : ℝ := 2*Real.sqrt (p:ℝ)/((p:ℝ)+1)
  have hp1 : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs : 1<Real.sqrt (p:ℝ) := by
    nlinarith [Real.sq_sqrt (show 0≤(p:ℝ) by positivity),Real.sqrt_nonneg (p:ℝ)]
  have hρ : ρ<1 := by
    apply (div_lt_one (by positivity : 0<(p:ℝ)+1)).mpr
    nlinarith [Real.sq_sqrt (show 0≤(p:ℝ) by positivity),sq_pos_of_pos (sub_pos.mpr hs)]
  obtain ⟨g,hg,hlim,hupper⟩ := weighted_wide_oldBand_filter_trace_upper_asymptotic S p T hpM hMp
    (Nat.gcdA p M) (Nat.gcdB p M) huv K he hc hK hm σ ((ρ+1)/2)
    (by change ρ<(ρ+1)/2;linarith) (by linarith) D hD W ε hε hproduct
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    obtain ⟨hA,hAA,hB,hBB⟩ := oldBand_projections S p T hpM (Nat.gcdA p M) (Nat.gcdB p M)
      huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ
    have hlower := half_filter_trace_kernel_lower (oldBandSum S p T (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ)
      (oldBandSum_symmetric S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ)
      (fun i => (two_projection_spectrum_bounds _ _ hA hB hAA hBB i).2) (growingMomentDegree t)
    have hk := congrArg (fun U : Submodule ℂ (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ) => (finrank ℂ U : ℝ))
      (oldBandSum_kernel S p T hpM (Nat.gcdA p M) (Nat.gcdB p M) huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ)
    have hlow := hk.symm.le.trans hlower
    have hscalar (a b c : ℝ) (hl : b≤a) (hu : a≤b+c) : |a-b|≤c := by
      rw [abs_of_nonneg (sub_nonneg.mpr hl)]
      linarith only [hu]
    exact hscalar _ _ _ hlow (hupper t)

#print axioms weighted_wide_physical_old_filter_trace_approximation

end QuantitativeMaass
