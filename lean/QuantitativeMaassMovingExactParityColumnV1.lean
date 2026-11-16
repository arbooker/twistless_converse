module

public import QuantitativeMaassBandParityTraceV1
public import QuantitativeArithmeticMaassMovingFiniteBandTraceV1
public import QuantitativeArithmeticMaassExactBandCompressionV1
public import QuantitativeArithmeticMaassMovingSectorTraceV1

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

/-- The logarithmic adjustment gives the exact exponential band width
for every fixed positive exponent. -/
theorem exactBandParameter_width (B : ℝ) (hB : 0<B) :
    ∀ᶠ t in atTop,Real.exp (exactBandParameter B t*Strong.strongScale t)+3=
      Real.exp (B*Strong.strongScale t) := by
  filter_upwards [Strong.strongScale_tendsto.eventually
    (eventually_ge_atTop (max 1 (Real.log 4/B)))] with t ht
  have hs : 0<Strong.strongScale t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht)
  have hlog : Real.log 4≤B*Strong.strongScale t := by
    have hh := (div_le_iff₀ hB).mp ((le_max_right _ _).trans ht)
    simpa only [mul_comm] using hh
  have h4 : (4:ℝ)≤Real.exp (B*Strong.strongScale t) := by
    calc
      _ = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hpos : 0<Real.exp (B*Strong.strongScale t)-3 := by linarith
  rw [exactBandParameter,div_mul_cancel₀ _ hs.ne',Real.exp_log hpos]
  ring

/-- The adjusted spectral compression is the actual exponential band
transfer used by the canonical finite-band filters. -/
theorem movingBandColumn_coe_exact (N : ℕ) (hN : 0<N)
    (S : CuspEnergySpectrum N hN) (δ C D B : ℝ) (hδ : 0<δ) (hB : 0<B)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,∀ z : UpperHalfPlane,
      movingBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ K hc he ε
        (exactBandParameter B t) t z=
      (WideInput.bandTransfer S t (Real.exp (B*Strong.strongScale t))
        (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t))
        (column K hc he ε t z)).val.val := by
  filter_upwards [exactBandParameter_width B hB] with t ht
  intro z
  dsimp only [movingBandColumn]
  simp only [ht]
  rfl

/-- Exact identification of the compressed filtered parity trace with
the finite parity columns used by the canonical projection comparison. -/
theorem movingBand_filtered_parity_eq (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) (σ : ℝ) (hσ : σ^2=1) (e : Sector N)
    (δ C D B : ℝ) (hδ : 0<δ) (hB : 0<B)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) :
    ∀ᶠ t in atTop,
      columnLinearTrace (quotientMeasure 0)
        (fun z => ambientSectorNewFilter N hN e (growingLVDegree t)
          (movingBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ
            K hc he ε (exactBandParameter B t) t z)) (parityProjection N σ)=
      columnLinearTrace (quotientMeasure 0)
        (fun z => ambientSectorNewFilter N hN e (growingLVDegree t)
          (inclusion S (t-Real.exp (B*Strong.strongScale t)) (t+Real.exp (B*Strong.strongScale t)) σ
            (movingParityColumn N hN S σ hδ K hc he ε B C D t z))) 1 := by
  filter_upwards [exactBandParameter_width B hB] with t ht
  let c := fun z => WideInput.bandTransfer S t (Real.exp (B*Strong.strongScale t))
    (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t))
    (column K hc he ε t z)
  have hw (z : UpperHalfPlane) :
      movingBandColumn N hN S.basis S.energy S.energy_nonneg S.graph δ C D hδ K hc he ε
        (exactBandParameter B t) t z=(c z).val.val := by
    dsimp only [movingBandColumn]
    simp only [ht]
    rfl
  simp only [hw]
  exact columnLinearTrace_band_parity (quotientMeasure 0) S _ _ σ hσ e (growingLVDegree t) c

#print axioms movingBandColumn_coe_exact
#print axioms exactBandParameter_width
#print axioms movingBand_filtered_parity_eq
end QuantitativeMaass.Scheduled
