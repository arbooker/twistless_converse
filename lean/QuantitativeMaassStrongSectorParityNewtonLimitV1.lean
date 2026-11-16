module

public import QuantitativeMaassSectorParityNewtonLimitV1
public import QuantitativeMaassStrongNewtonCostV1
public import QuantitativeMaassStrongCanonicalSectorFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open Filter QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
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



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _


/-- Exponential weighted decay absorbs the explicit normalization cost. -/
theorem weighted_newton_error_limit (f g ε : ℝ → ℝ) (W : ℝ)
    (hf : ∀ t,0≤f t) (hg : ∀ t,0≤g t)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hfg : ∀ᶠ t in atTop,g t≤
      (2*((6:ℝ)^(2*(4^(bandNewtonDepth t)))+
        10*((3^(bandNewtonDepth t):ℕ):ℝ)*(9:ℝ)^(2*(4^(bandNewtonDepth t)))))*f t)
    (hlim : Tendsto (fun t => Real.exp ((W+2*Real.log 5346)*strongScale t)*
      f t/(t*ε t)) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*strongScale t)*g t/(t*ε t)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hg t)) (mul_pos ht he).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),hfg,bandNewtonDepth_weighted_cost] with t he ht heq hc
    apply div_le_div_of_nonneg_right _ (mul_pos ht he).le
    calc
      _ ≤ Real.exp (W*strongScale t)*
          (Real.exp ((2*Real.log 5346)*strongScale t)*f t) :=
        mul_le_mul_of_nonneg_left (heq.trans (mul_le_mul_of_nonneg_right hc (hf t)))
          (Real.exp_pos _).le
      _ = _ := by rw [←mul_assoc,←Real.exp_add,←add_mul]

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (σ : ℝ) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

/-- The explicit sector filter can replace the exact projection inside the
actual weighted normalization at the growing Newton depth. -/
theorem sectorParityBandFilter_newton_weighted_energy
    (hAd : GridAdmissibleGap.Admissible N) (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*finiteBandEnergy (basis t)
      (compressedNewtonPolynomial
        (parityBandWeightedGram N hN T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ hδ hν)
        (sectorParityBandFilter N hN T S (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ e (growingLVDegree t)) (bandNewtonDepth t)-
      compressedNewtonPolynomial
        (parityBandWeightedGram N hN T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ hδ hν)
        (sectorParityBandSpace T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ e).starProjection (bandNewtonDepth t))/(t*ε t)) atTop (𝓝 0) := by
  have hlim := canonicalSectorParityBandFilter_weighted_energy N hN T S σ e hAd D
    (W+2*Real.log 5346) hD basis ε hε hproduct
  have heq (a b : ℝ) := sectorParityBandSpace_eq_canonical T a b σ e hAd
  simp only [←heq] at hlim
  apply weighted_newton_error_limit _ _ ε W (fun _ => finiteBandEnergy_nonneg _ _)
    (fun _ => finiteBandEnergy_nonneg _ _) hε _ hlim
  apply Filter.Eventually.of_forall
  intro t
  apply compressedNewtonPolynomial_energy
  · exact parityBandWeightedGram_norm N hN T _ _ σ hδ hν
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using
      (sectorParityBandSpace T _ _ σ e).norm_starProjection_apply_le x
  · exact sectorParityBandFilter_norm N hN T S _ _ σ e hAd _

/-- The error remains negligible after the actual cylinder embedding. -/
theorem sectorParityBandFilter_reconstruction_weighted_energy
    (hAd : GridAdmissibleGap.Admissible N) (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*finiteSourceEnergy (basis t)
      ((parityBandWeightedEmbedding N hN T (t-Real.exp (D*strongScale t))
          (t+Real.exp (D*strongScale t)) σ hδ hν).comp
        (compressedNewtonPolynomial
          (parityBandWeightedGram N hN T (t-Real.exp (D*strongScale t))
            (t+Real.exp (D*strongScale t)) σ hδ hν)
          (sectorParityBandFilter N hN T S (t-Real.exp (D*strongScale t))
            (t+Real.exp (D*strongScale t)) σ e (growingLVDegree t)) (bandNewtonDepth t)-
        compressedNewtonPolynomial
          (parityBandWeightedGram N hN T (t-Real.exp (D*strongScale t))
            (t+Real.exp (D*strongScale t)) σ hδ hν)
          (sectorParityBandSpace T (t-Real.exp (D*strongScale t))
            (t+Real.exp (D*strongScale t)) σ e).starProjection (bandNewtonDepth t)))/(t*ε t))
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _
    (sectorParityBandFilter_newton_weighted_energy N hN T S σ e hδ hν hAd D W hD basis ε hε hproduct)
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (finiteSourceEnergy_nonneg _ _)) (mul_pos ht he).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    apply div_le_div_of_nonneg_right _ (mul_pos ht he).le
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply (finiteSourceEnergy_left (basis t) _ _).trans
    have hn := parityBandWeightedEmbedding_norm N hN T
      (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ hδ hν
    have hn2 : ‖parityBandWeightedEmbedding N hN T
        (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ hδ hν‖^2≤1 := by
      nlinarith [norm_nonneg (parityBandWeightedEmbedding N hN T
        (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ hδ hν)]
    simpa only [one_mul,finiteSourceEnergy,finiteBandEnergy] using mul_le_mul_of_nonneg_right hn2 (finiteSourceEnergy_nonneg (basis t) _)

#print axioms weighted_newton_error_limit
#print axioms sectorParityBandFilter_newton_weighted_energy
#print axioms sectorParityBandFilter_reconstruction_weighted_energy
end QuantitativeMaass.Strong
