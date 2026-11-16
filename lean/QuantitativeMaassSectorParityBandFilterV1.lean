module

public import QuantitativeMaassSectorParityBandProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology
namespace QuantitativeMaass

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


variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (a b σ : ℝ) (e : Sector N)

/-- Explicit local-new polynomials followed by the finite half-sum sign factors. -/
def sectorParityBandFilter (m : ℕ) : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  admissibleTotalNewBandFilter N hN T S a b σ m*sectorParitySignProduct T a b σ e

theorem sectorParityBandFilter_norm (hAd : GridAdmissibleGap.Admissible N) (m : ℕ) :
    ‖sectorParityBandFilter N hN T S a b σ e m‖≤1 := by
  have hA := admissibleTotalNewBandFilter_norm N hN T S a b σ hAd m
  have hB := sectorParitySignProduct_norm T a b σ e
  apply (norm_mul_le _ _).trans
  nlinarith [norm_nonneg (sectorParitySignProduct T a b σ e)]

/-- Adding the exact finite signs does not increase the squared local-new error. -/
theorem sectorParityBandFilter_energy {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℂ (T.parityBand a b σ)) (m : ℕ) :
    finiteBandEnergy basis (sectorParityBandFilter N hN T S a b σ e m-
      (sectorParityBandSpace T a b σ e).starProjection) ≤
      finiteBandEnergy basis (admissibleTotalNewBandFilter N hN T S a b σ m-
        (totalNewBand N hN T a b σ).starProjection) := by
  rw [sectorParityBandSpace_projection]
  change finiteBandEnergy basis
    (admissibleTotalNewBandFilter N hN T S a b σ m*sectorParitySignProduct T a b σ e-
      (totalNewBand N hN T a b σ).starProjection*sectorParitySignProduct T a b σ e)≤_
  rw [←sub_mul]
  apply (finiteBandEnergy_right basis _ _).trans
  have hn : ‖sectorParitySignProduct T a b σ e‖^2≤1 := by
    nlinarith [sectorParitySignProduct_norm T a b σ e,norm_nonneg (sectorParitySignProduct T a b σ e)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn
    (finiteBandEnergy_nonneg basis (admissibleTotalNewBandFilter N hN T S a b σ m-
      (totalNewBand N hN T a b σ).starProjection))

/-- Weighted approximation of the original canonical sector on each
actual growing fixed-parity band, with all local errors discharged. -/
theorem canonicalSectorParityBandFilter_weighted_energy (hAd : GridAdmissibleGap.Admissible N)
    (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*fourthRootScale t)*finiteBandEnergy (basis t)
      (sectorParityBandFilter N hN T S (t-Real.exp (D*fourthRootScale t))
        (t+Real.exp (D*fourthRootScale t)) σ e (growingMomentDegree t)-
        ((completedNewSignSpace N hN (sectorCharacter N hN e)).comap
          (inclusion T (t-Real.exp (D*fourthRootScale t))
            (t+Real.exp (D*fourthRootScale t)) σ)).starProjection)/(t*ε t)) atTop (𝓝 0) := by
  have heq (a b : ℝ) := sectorParityBandSpace_eq_canonical T a b σ e hAd
  simp only [←heq]
  apply squeeze_zero' _ _ (admissibleTotalNewBandFilter_weighted_energy N hN T S σ hAd D W hD basis ε hε hproduct)
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (finiteBandEnergy_nonneg _ _)) (mul_pos ht he).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    apply div_le_div_of_nonneg_right _ (mul_pos ht he).le
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact sectorParityBandFilter_energy N hN T S _ _ σ e (basis t) (growingMomentDegree t)

#print axioms sectorParityBandFilter_norm
#print axioms sectorParityBandFilter_energy
#print axioms canonicalSectorParityBandFilter_weighted_energy
end QuantitativeMaass
