module

public import QuantitativeMaassQuotientWeightDerivativeMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip

namespace QuantitativeMaass

/-- Coordinate null sets remain null for hyperbolic area. -/
theorem ae_upper_coordinates {P : ℝ×ℝ → Prop}
    (hP : ∀ᵐ Z : ℝ×ℝ ∂volume,0<Z.2 → P Z) :
    ∀ᵐ z : ℍ ∂volume,P (z.re,z.im) := by
  have hc := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hP
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  have hu := hp.quasiMeasurePreserving.ae (ae_restrict_of_ae hc)
  rw [UpperHalfPlane.volume_def]
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [hu] with z hz
  exact hz z.im_pos

 #print axioms ae_upper_coordinates

/-- One quotient-conull set can be chosen on which a coordinate a.e. property
holds at every point of each congruence orbit. -/
theorem ae_quotient_orbit_coordinates (N : ℕ) {P : ℝ×ℝ → Prop}
    (hP : ∀ᵐ Z : ℝ×ℝ ∂volume,0<Z.2 → P Z) :
    ∀ᵐ z : ℍ ∂quotientMeasure N,∀ g : gamma N,P ((g•z).re,(g•z).im) := by
  have hu := ae_upper_coordinates hP
  have hg (g : gamma N) : ∀ᵐ z : ℍ ∂volume,P ((g•z).re,(g•z).im) :=
    (AsymptoticRationalGroup.measurePreserving g.val).quasiMeasurePreserving.ae hu
  have hall : ∀ᵐ z : ℍ ∂volume,∀ g : gamma N,P ((g•z).re,(g•z).im) :=
    ae_all_iff.mpr hg
  exact (withDensity_absolutelyContinuous _ _).ae_le hall

#print axioms ae_upper_coordinates
#print axioms ae_quotient_orbit_coordinates

end QuantitativeMaass
