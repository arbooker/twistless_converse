module

public import QuantitativeMaassBandParityTraceV1
public import QuantitativeMaassMajorantBandColumnV1
public import QuantitativeMaassMovingExactParityColumnV1
public import QuantitativeArithmeticMaassExactBandCompressionV1
public import QuantitativeMaassMajorantSectorTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
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

/-- The adjusted spectral compression is the actual exponential band
transfer used by the canonical finite-band filters. -/
theorem originalMajorantBandColumn_coe_exact (N : ℕ) (hN : 0<N)
    (S : CuspEnergySpectrum N hN) (δ C D B : ℝ) (hδ : 0<δ) (hB : 0<B)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,∀ z : UpperHalfPlane,
      originalMajorantBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ K hc he ε
        (exactBandParameter B t) t z=
      (WideInput.bandTransfer S t (Real.exp (B*Strong.strongScale t))
        (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t))
        (originalMajorantColumn K hc he ε t z)).val.val := by
  filter_upwards [exactBandParameter_width B hB] with t ht
  intro z
  dsimp only [originalMajorantBandColumn]
  simp only [ht]
  rfl

/-- Exact identification of the compressed filtered parity trace with
the finite parity columns used by the canonical projection comparison. -/
theorem originalMajorantBand_filtered_parity_eq (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) (σ : ℝ) (hσ : σ^2=1) (e : Sector N)
    (δ C D B : ℝ) (hδ : 0<δ) (hB : 0<B)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,
      columnLinearTrace (quotientMeasure 0)
        (fun z => ambientSectorNewFilter N hN e (growingLVDegree t)
          (originalMajorantBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ
            K hc he ε (exactBandParameter B t) t z)) (parityProjection N σ)=
      columnLinearTrace (quotientMeasure 0)
        (fun z => ambientSectorNewFilter N hN e (growingLVDegree t)
          (inclusion S (t-Real.exp (B*Strong.strongScale t)) (t+Real.exp (B*Strong.strongScale t)) σ
            (originalMajorantParityColumn N hN S σ hδ K hc he ε B C D t z))) 1 := by
  filter_upwards [exactBandParameter_width B hB] with t ht
  let c := fun z => WideInput.bandTransfer S t (Real.exp (B*Strong.strongScale t))
    (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t))
    (originalMajorantColumn K hc he ε t z)
  have hw (z : UpperHalfPlane) :
      originalMajorantBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ K hc he ε
        (exactBandParameter B t) t z=(c z).val.val := by
    dsimp only [originalMajorantBandColumn]
    simp only [ht]
    rfl
  simp only [hw]
  exact columnLinearTrace_band_parity (quotientMeasure 0) S _ _ σ hσ e (growingLVDegree t) c

#print axioms originalMajorantBandColumn_coe_exact
#print axioms originalMajorantBand_filtered_parity_eq
end QuantitativeMaass.Scheduled
