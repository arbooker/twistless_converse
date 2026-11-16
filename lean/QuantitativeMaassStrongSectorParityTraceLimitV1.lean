module

public import QuantitativeMaassSectorParityTraceLimitV1
public import QuantitativeMaassStrongSectorParityNewtonLimitV1
public import QuantitativeMaassStrongTraceMajorantV1

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


/-- The explicit quadratic reconstruction norm cost is exponential only
in the fourth-root scale. -/
theorem bandNewtonDepth_quadratic_cost :
    ∀ᶠ t in atTop,((6:ℝ)^(4^(bandNewtonDepth t)))^2≤
      Real.exp ((4*Real.log 6)*strongScale t) := by
  filter_upwards [bandNewtonDepth_cost_bound] with t ht
  have he : ((6:ℝ)^(4^(bandNewtonDepth t)))^2=
      Real.exp ((2*((4^(bandNewtonDepth t):ℕ):ℝ))*Real.log 6) := by
    have hp : (6:ℝ)^(4^(bandNewtonDepth t))=
        Real.exp (((4^(bandNewtonDepth t):ℕ):ℝ)*Real.log 6) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<6)]
    rw [hp,←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right ht (Real.log_nonneg (by norm_num : (1:ℝ)≤6))
  push_cast
  nlinarith only [hh]

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (σ : ℝ) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

theorem sectorParityReconstructionError_weighted_limit
    (hAd : GridAdmissibleGap.Admissible N) (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*sectorParityReconstructionError N hN T S σ e hδ hν
      (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) (basis t)
      (growingLVDegree t) (bandNewtonDepth t)/(t*ε t)) atTop (𝓝 0) := by
  simpa only [sectorParityReconstructionError,parityBandReconstruction,←ContinuousLinearMap.comp_sub] using
    sectorParityBandFilter_reconstruction_weighted_energy N hN T S σ e hδ hν hAd D W hD basis ε hε hproduct

/-- Every contractive quadratic observation of the actual reconstruction
has negligible replacement error, with any fixed exponential weight. -/
theorem sectorParityReconstructionTrace_weighted_limit
    (hAd : GridAdmissibleGap.Admissible N) (D W : ℝ) (hD : 0≤D)
    (basis : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ))
    (A : ℝ → Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0))
    (hA : ∀ t,‖A t‖≤1) (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*sectorParityReconstructionTrace N hN T S σ e hδ hν
      (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) (basis t) (A t)
      (growingLVDegree t) (bandNewtonDepth t)/(t*ε t)) atTop (𝓝 0) := by
  let E := fun t => sectorParityReconstructionError N hN T S σ e hδ hν
    (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) (basis t)
    (growingLVDegree t) (bandNewtonDepth t)
  let M := fun t => Real.exp ((D+4*Real.log 6)*strongScale t)*E t
  obtain ⟨C,hC,hcount⟩ := parityBand_wide_finrank_bound N hN
  have hM : Tendsto (fun t => Real.exp ((2*W+1)*strongScale t)*M t/(t*ε t)) atTop (𝓝 0) := by
    have hh := sectorParityReconstructionError_weighted_limit N hN T S σ e hδ hν hAd D
      ((2*W+1)+(D+4*Real.log 6)) hD basis ε hε hproduct
    convert hh using 1
    ext t
    dsimp only [M,E]
    rw [←mul_assoc,←Real.exp_add,←add_mul]
  have hmajor := weighted_trace_majorant ε M (16*C) W (by positivity) hε hproduct hM
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hmajor
  filter_upwards [hε,eventually_ge_atTop (6:ℝ),exponential_band_width_quarter D hD,
    bandNewtonDepth_quadratic_cost] with t he ht hw hk
  have ht0 : 0<t := by linarith
  have hE0 : 0≤E t := sectorParityReconstructionError_nonneg N hN T S σ e hδ hν _ _ _ _ _
  have hM0 : 0≤M t := mul_nonneg (Real.exp_pos _).le hE0
  have hd := hcount T σ t (Real.exp (D*strongScale t)) ht hw.1 hw.2
  have hf := sectorParityReconstructionTrace_square N hN T S σ e hδ hν hAd _ _ (basis t) (A t) (hA t)
    (growingLVDegree t) (bandNewtonDepth t)
  simp only [Fintype.card_fin] at hf
  have hb : (sectorParityReconstructionTrace N hN T S σ e hδ hν
      (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) (basis t) (A t)
      (growingLVDegree t) (bandNewtonDepth t))^2≤16*C*t*|M t| := by
    apply hf.trans
    change 16*((6:ℝ)^(4^(bandNewtonDepth t)))^2*
      (Module.finrank ℂ (T.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ):ℝ)*E t≤_
    calc
      _ ≤ 16*Real.exp ((4*Real.log 6)*strongScale t)*
          (C*t*Real.exp (D*strongScale t))*E t := by gcongr
      _ = _ := by
        rw [abs_of_nonneg hM0]
        dsimp only [M]
        rw [add_mul,Real.exp_add]
        ring
  have hab : |sectorParityReconstructionTrace N hN T S σ e hδ hν
      (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) (basis t) (A t)
      (growingLVDegree t) (bandNewtonDepth t)|≤Real.sqrt (16*C*t*|M t|) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (show 0≤16*C*t*|M t| by positivity)]
    exact hb
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht0 he)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le) (mul_pos ht0 he).le

#print axioms bandNewtonDepth_quadratic_cost
#print axioms sectorParityReconstructionError_weighted_limit
#print axioms sectorParityReconstructionTrace_weighted_limit
end QuantitativeMaass.Strong
