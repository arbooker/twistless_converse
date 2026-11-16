module

public import QuantitativeMaassQuotientWeightDerivativeV1
public import AsymptoticClassicalPeterssonMeasureV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Lebesgue almost-everywhere coordinate statements on the positive
half-plane hold for the actual weighted quotient measure. -/
theorem ae_quotient_coordinates (N : ℕ) {P : ℝ×ℝ → Prop}
    (hP : ∀ᵐ Z : ℝ×ℝ ∂volume,0<Z.2 → P Z) :
    ∀ᵐ z : ℍ ∂quotientMeasure N,P (z.re,z.im) := by
  have hc := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hP
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  have hu := hp.quasiMeasurePreserving.ae (ae_restrict_of_ae hc)
  have hv : ∀ᵐ z : ℍ ∂volume,P (z.re,z.im) := by
    rw [UpperHalfPlane.volume_def]
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [hu] with z hz
    exact hz z.im_pos
  exact (withDensity_absolutelyContinuous _ _).ae_le hv

/-- The actual orbit-weight coordinate derivative exists almost everywhere
for the quotient measure used in the Gram and energy spaces. -/
theorem quotientWeight_ae_differentiable (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    ∀ᵐ z : ℍ ∂quotientMeasure N,
      DifferentiableAt ℝ (quotientWeightPlane N ε v) (z.re,z.im) :=
  ae_quotient_coordinates N (quotientWeightPlane_ae_differentiable N hε hv)

#print axioms ae_quotient_coordinates
#print axioms quotientWeight_ae_differentiable

end QuantitativeMaass
