module

public import QuantitativeMaassOldBandFilterV1
public import QuantitativeMaassStrongWideBandDensityV1
public import QuantitativeMaassBandWideCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open QuantitativeArithmeticExceptionalMoments QuantitativeArithmeticMaassExceptionalBands
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



/-- A concrete polynomial in the two physical old projections approximates
the actual local-new trace from above, with an error negligible at the
original shrinking-window scale on an exponentially growing band. No positive spectral gap is required. -/
theorem weighted_wide_oldBand_filter_trace_upper_asymptotic {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (hMp : (M:ZMod p)≠0)
    (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (σ η : ℝ)
    (hη : 2*Real.sqrt (p:ℝ)/((p:ℝ)+1)<η) (hη1 : η<1)
    (B : ℝ) (hB : 0≤B) (W : ℝ) (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ g : ℝ → ℝ,(∀ t,0≤g t) ∧ Tendsto (fun t => Real.exp (W*strongScale t)*g t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ t, (LinearMap.trace ℂ (T.parityBand (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ)
        ((1-(1/2:ℂ) • oldBandSum S p T (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ)^(growingLVDegree t))).re ≤
        (finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ):ℝ)+g t := by
  let D (t : ℝ) : ℝ := finrank ℂ (exceptionalSpace
    (normalizedBandHecke_symmetric S p hpM u v huv (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ) η)
  let n (t : ℝ) : ℝ := finrank ℂ (T.parityBand (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ)
  let q : ℝ := 1-(1-η)/2
  have hη0 : 0≤η := (by positivity : 0≤2*Real.sqrt (p:ℝ)/((p:ℝ)+1)).trans hη.le
  have hq : 0<q := by dsimp only [q];linarith
  have hq1 : q<1 := by dsimp only [q];linarith
  have hD : Tendsto (fun t => Real.exp (W*strongScale t)*D t/(t*ε t)) atTop (𝓝 0) :=
    weighted_wide_normalized_hecke_band_exceptional_density S p hpM hMp u v huv K he hc hK hm σ η hη B hB W ε hε hproduct
  obtain ⟨C,hC,hcount⟩ := parityBand_wide_finrank_bound (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
  have hn : Tendsto (fun t => Real.exp (W*strongScale t)*q^(growingLVDegree t)*n t/(t*ε t)) atTop (𝓝 0) := by
    have hd := (weighted_growingMomentDegree_decay ε q (W+B) hq hq1 hε hproduct).const_mul C
    simp only [mul_zero] at hd
    apply squeeze_zero' _ _ hd
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
      dsimp only [n]
      positivity
    · filter_upwards [hε,eventually_ge_atTop (6:ℝ),exponential_band_width_quarter B hB] with t he ht hw
      have ht0 : 0<t := by linarith
      calc
        _ ≤ Real.exp (W*strongScale t)*q^(growingLVDegree t)*(C*t*Real.exp (B*strongScale t))/(t*ε t) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcount T σ t (Real.exp (B*strongScale t)) ht hw.1 hw.2)
            (mul_nonneg (Real.exp_pos _).le (pow_nonneg hq.le _))) (by positivity)
        _ = C*(Real.exp ((W+B)*strongScale t)*q^(growingLVDegree t)/ε t) := by
          rw [add_mul,Real.exp_add]
          field_simp
  refine ⟨fun t => 2*D t+q^(growingLVDegree t)*n t,?_,?_,?_⟩
  · intro t
    dsimp only [D,n]
    positivity
  · have hh := (hD.const_mul 2).add hn
    simp only [mul_zero,add_zero] at hh
    convert hh using 1
    funext t
    ring
  · intro t
    have hh := oldBand_filter_trace S p T hpM u v huv (t-Real.exp (B*strongScale t)) (t+Real.exp (B*strongScale t)) σ η hη0 hη1.le
      (growingLVDegree t)
    dsimp only [D,n,q]
    linarith only [hh]

#print axioms weighted_wide_oldBand_filter_trace_upper_asymptotic

end QuantitativeMaass.Strong
