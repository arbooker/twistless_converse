module

public import QuantitativeMaassZeroWaveCosineV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory

namespace QuantitativeMaass.ZeroWave

/-- Actual finite propagation on the logarithmic height line, formulated
for L² classes with all representative qualifications retained. -/
theorem wave_vanishes_outside (a : Space) (R t : ℝ)
    (ha : ∀ᵐ u : ℝ ∂volume, R < |u| → a u=0) :
    ∀ᵐ u : ℝ ∂volume, R + |t| < |u| → wave t a u=0 := by
  have hp := (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae ha
  have hm := (measurePreserving_add_right (volume : Measure ℝ) (-t)).quasiMeasurePreserving.ae ha
  filter_upwards [wave_ae t a,hp,hm] with u hu hplus hminus
  intro hout
  have hbplus : |u| ≤ |u+t|+|t| := by simpa using abs_sub (u+t) t
  have hbminus : |u| ≤ |u-t|+|t| := by simpa using abs_add_le (u-t) t
  have hpzero : a (u+t)=0 := hplus (by linarith)
  have hmzero : a (u-t)=0 := by
    apply hminus
    simpa [sub_eq_add_neg] using (show R < |u-t| by linarith)
  rw [hu,hpzero,hmzero,add_zero]

#print axioms wave_vanishes_outside

end QuantitativeMaass.ZeroWave
