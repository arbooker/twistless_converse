module

public import QuantitativeMaassMovingExactParityColumnV1
public import QuantitativeMaassCanonicalObservationSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns
open AsymptoticClassicalPetersson QuantitativeArithmeticRepeatedTwoBands
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

theorem columnLinearTrace_canonical_band_parity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (a b σ : ℝ) (hσ : σ^2=1) (χ : admissibleGeneratorIndex N hN→ℂ) (c : α→S.band a b) :
    columnLinearTrace μ (fun z => (c z).val.val)
      (completedNewSignParitySpace N hN χ σ).starProjection=
    columnLinearTrace μ (fun z => inclusion S a b σ
      ((S.parityBand a b σ).orthogonalProjectionOnto (c z)))
      (completedNewSignParitySpace N hN χ σ).starProjection := by
  simp only [parityBand_projection_coe S a b σ hσ]
  exact (columnLinearTrace_canonical_parity N hN χ σ μ (fun z => (c z).val.val)).symm

theorem movingBand_canonical_parity_eq (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) (σ : ℝ) (hσ : σ^2=1)
    (χ : admissibleGeneratorIndex N hN→ℂ)
    (δ C D B : ℝ) (hδ : 0<δ) (hB : 0<B)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,
      columnLinearTrace (quotientMeasure 0)
        (movingBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ K hc he ε
          (exactBandParameter B t) t) (completedNewSignParitySpace N hN χ σ).starProjection=
      columnLinearTrace (quotientMeasure 0)
        (fun z => inclusion S (t-Real.exp (B*Strong.strongScale t)) (t+Real.exp (B*Strong.strongScale t)) σ
          (movingParityColumn N hN S σ hδ K hc he ε B C D t z))
        (completedNewSignParitySpace N hN χ σ).starProjection := by
  filter_upwards [movingBandColumn_coe_exact N hN S δ C D B hδ hB K hc he ε] with t ht
  have hf := funext ht
  rw [hf]
  exact columnLinearTrace_canonical_band_parity (quotientMeasure 0) S _ _ σ hσ χ _

#print axioms columnLinearTrace_canonical_band_parity
#print axioms movingBand_canonical_parity_eq
end QuantitativeMaass.Scheduled
