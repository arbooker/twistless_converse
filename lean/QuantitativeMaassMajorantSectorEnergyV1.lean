module

public import QuantitativeMaassMajorantColumnsV1
public import QuantitativeArithmeticMaassMovingSectorFilterV1
public import QuantitativeMaassStrongSectorParityTraceLimitV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open QuantitativeNinaMaass AsymptoticClassicalPetersson AsymptoticSectorSigns
open QuantitativeNewGap QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

namespace Scheduled
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



local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (σ : ℝ) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

/-- The finite local-new/sign filter converges to the true canonical sector
on the literal enlarged normalized majorant columns. -/
theorem originalMajorant_canonicalSector_energy_limit
    (hAd : GridAdmissibleGap.Admissible N) (B W C D : ℝ) (hB : 0≤B) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      let a := t-Real.exp (B*Strong.strongScale t)
      let b := t+Real.exp (B*Strong.strongScale t)
      let E := sectorParityBandFilter N hN T S a b σ e (growingLVDegree t)-
        (sectorParityBandSpace T a b σ e).starProjection
      let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      Real.exp (W*Strong.strongScale t)*
        (∫ z,‖E ((T.parityBand a b σ).orthogonalProjectionOnto
          (WideInput.bandTransfer T t (Real.exp (B*Strong.strongScale t)) A
            (originalMajorantColumn K hc he ε t z)))‖^2 ∂quotientMeasure 0)/(t*ε t)) atTop (𝓝 0) := by
  let basis := fun t => stdOrthonormalBasis ℂ
    (T.parityBand (t-Real.exp (B*Strong.strongScale t)) (t+Real.exp (B*Strong.strongScale t)) σ)
  have hlim := Strong.canonicalSectorParityBandFilter_weighted_energy N hN T S σ e
    hAd B (W+35) hB basis ε (hε.mono (fun _ h => h.1)) hp
  have heq (a b : ℝ) := sectorParityBandSpace_eq_canonical T a b σ e hAd
  simp only [←heq] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t ht ht1
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (by linarith) ht.1.le)
  · filter_upwards [originalMajorant_band_column_operator_norm K hc he ε hε hp hδ C hC,
      hε,eventually_ge_atTop (1:ℝ)] with t hn ht ht1
    have ht0 : 0<t := by linarith
    let a := t-Real.exp (B*Strong.strongScale t)
    let b := t+Real.exp (B*Strong.strongScale t)
    let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
    let c := fun z => WideInput.bandTransfer T t (Real.exp (B*Strong.strongScale t)) A
      (originalMajorantColumn K hc he ε t z)
    have hcol := WideInput.bandTransfer_column_memLp T t (Real.exp (B*Strong.strongScale t)) A
      (originalMajorantColumn K hc he ε t) (originalMajorant_cutoff_memLp N hδ C D K hc he ε t)
    let E := sectorParityBandFilter N hN T S a b σ e (growingLVDegree t)-
      (sectorParityBandSpace T a b σ e).starProjection
    have hb := finiteSourceEnergy_contracted_column_bound (quotientMeasure 0) c hcol
      (T.parityBand a b σ).orthogonalProjectionOnto
      (T.parityBand a b σ).orthogonalProjectionOnto_norm_le (basis t) E
    have hb' := hb.trans (mul_le_mul_of_nonneg_right
      (hn N hN T (Real.exp (B*Strong.strongScale t)) D) (finiteSourceEnergy_nonneg (basis t) E))
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb' (Real.exp_pos (W*Strong.strongScale t)).le)
      (mul_pos ht0 ht.1).le
    simpa only [finiteSourceEnergy,finiteBandEnergy,←mul_assoc,←Real.exp_add,←add_mul] using hh

#print axioms originalMajorant_canonicalSector_energy_limit
end Scheduled
end QuantitativeMaass
