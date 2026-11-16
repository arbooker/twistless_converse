module

public import QuantitativeMaassStrongDivisorNewFilterV1
public import QuantitativeMaassAdmissibleNewBandFilterV1
public import QuantitativeMaassTotalNewBandLimitV1

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology
namespace QuantitativeMaass.Strong

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance

variable (N : ℕ) [NeZero N] (hN : 0<N)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (a b σ : ℝ)



/-- Every local error tends to zero at the original window schedule,
including the repeated-prime case where the error is identically zero. -/
theorem admissibleLocalNewBandFilter_weighted_energy (hAd : GridAdmissibleGap.Admissible N)
    (p : ↥N.primeFactors) (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*finiteBandEnergy (basis t)
      (admissibleLocalNewBandFilter N hN T S (t-Real.exp (D*strongScale t))
        (t+Real.exp (D*strongScale t)) σ (growingLVDegree t) p-
        (localNewBand N hN T S (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ p).starProjection)/(t*ε t)) atTop (𝓝 0) := by
  classical
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hpN := Nat.dvd_of_mem_primeFactors p.property
  let : Fact p.val.Prime := ⟨hp⟩
  by_cases h : p.val∣N/p.val
  · have hp2 := (admissible_prime_filter_cases N p.val hAd hp hpN).resolve_left (not_not.mpr h)
    have he : 2*(N/p.val)=N := by rw [←hp2.1];exact Nat.mul_div_cancel' hpN
    have hd : 2∣N/p.val := by simpa only [hp2.1] using h
    have hex (a b : ℝ) := divisorRepeatedTwoNewBandFilter_exact (S p) T
      (Nat.div_dvd_of_dvd hpN) he hd a b σ
    simpa only [admissibleLocalNewBandFilter,ite_eq_left h,hex,localNewBand,sub_self,
      finiteBandEnergy,zero_apply,norm_zero,zero_pow (by decide : 2≠0),
      Finset.sum_const_zero,mul_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0))
  · simpa only [admissibleLocalNewBandFilter,ite_eq_right h,localNewBand] using
      divisorSimpleNewBandFilter_weighted_energy (S p) T (Nat.div_dvd_of_dvd hpN)
        p.val (Nat.mul_div_cancel' hpN) h σ D W hD basis ε hε hproduct


/-- The explicit finite polynomial product approximates the actual full
new projection at every admissible level, with the original epsilon
condition and any fixed exponential weight in the triple-logarithmic scale. -/
theorem admissibleTotalNewBandFilter_weighted_energy (hAd : GridAdmissibleGap.Admissible N)
    (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*finiteBandEnergy (basis t)
      (admissibleTotalNewBandFilter N hN T S (t-Real.exp (D*strongScale t))
        (t+Real.exp (D*strongScale t)) σ (growingLVDegree t)-
        (totalNewBand N hN T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ).starProjection)/(t*ε t)) atTop (𝓝 0) := by
  have hw : ∀ᶠ t in atTop,0≤Real.exp (W*strongScale t)/(t*ε t) := by
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t htε ht
    exact div_nonneg (Real.exp_pos _).le (mul_pos ht htε).le
  have hl := totalNewBandApproximation_weighted_limit N hN T S
    (fun t => t-Real.exp (D*strongScale t)) (fun t => t+Real.exp (D*strongScale t))
    (fun t => Real.exp (W*strongScale t)/(t*ε t)) σ hw basis
    (fun t => admissibleLocalNewBandFilter N hN T S (t-Real.exp (D*strongScale t))
      (t+Real.exp (D*strongScale t)) σ (growingLVDegree t))
    (fun t => admissibleLocalNewBandFilter_norm N hN T S _ _ σ hAd (growingLVDegree t))
    (fun p => by
      simpa only [div_mul_eq_mul_div] using
        admissibleLocalNewBandFilter_weighted_energy N hN T S σ hAd p D W hD basis ε hε hproduct)
  simpa only [admissibleTotalNewBandFilter,div_mul_eq_mul_div] using hl


#print axioms admissibleLocalNewBandFilter_weighted_energy
#print axioms admissibleTotalNewBandFilter_weighted_energy
end QuantitativeMaass.Strong
