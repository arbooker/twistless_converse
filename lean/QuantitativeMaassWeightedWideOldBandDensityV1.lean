module

public import QuantitativeMaassOldBandGramV1
public import QuantitativeMaassWeightedWideBandDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open QuantitativeArithmeticExceptionalOldSpace QuantitativeArithmeticExceptionalMoments
open QuantitativeArithmeticMaassExceptionalBands
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



/-- The actual small positive old-spectrum rank is negligible at the
original shrinking-window scale even on exponentially growing bands, with no physical spectral-gap premise. -/
theorem weighted_wide_oldBand_smallPositive_density {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (hMp : (M:ZMod p)≠0)
    (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (σ η : ℝ)
    (hη : 2*Real.sqrt (p:ℝ)/((p:ℝ)+1)<η)
    (D : ℝ) (hD : 0≤D) (W : ℝ) (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*fourthRootScale t)*(finrank ℂ (smallPositiveSpace
      ((oldBand_projections S p T hpM u v huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ).1.add
        (oldBand_projections S p T hpM u v huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ).2.2.1) (1-η)):ℝ)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := (weighted_wide_normalized_hecke_band_exceptional_density S p hpM hMp u v huv
    K he hc hK hm σ η hη D hD W ε hε hproduct).const_mul 2
  simp only [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    have hr := Nat.cast_le (α := ℝ).mpr
      (oldBand_smallPositive_rank S p T hpM u v huv (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ η)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hr
    have hrw := mul_le_mul_of_nonneg_left hr (Real.exp_pos (W*fourthRootScale t)).le
    apply (div_le_div_of_nonneg_right hrw (mul_nonneg ht.le he.le)).trans_eq
    ring

#print axioms weighted_wide_oldBand_smallPositive_density

end QuantitativeMaass
