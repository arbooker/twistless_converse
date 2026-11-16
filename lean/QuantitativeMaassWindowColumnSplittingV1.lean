module

public import QuantitativeMaassCylinderColumnLinearV1
public import QuantitativeArithmeticMaassResidualIntegralV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Splitting the frequency interval splits the actual Schwartz time test. -/
theorem windowTimeSchwartz_add_intervals (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b c : ℝ) (hab : a≤b) (hbc : b≤c) :
    windowTimeSchwartz K hc R hR a c =
      windowTimeSchwartz K hc R hR a b+windowTimeSchwartz K hc R hR b c := by
  ext s
  change symmetricWindowTimeTest K R a c s=
    symmetricWindowTimeTest K R a b s+symmetricWindowTimeTest K R b c s
  unfold symmetricWindowTimeTest averagedTimeTest
  have hcont : Continuous (fun T => scaledModulatedTimeTest (kernelTimeProfile K) R T s) := by
    unfold scaledModulatedTimeTest
    fun_prop
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) a b) (hcont.intervalIntegrable (μ := volume) b c)
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hbc,
    intervalIntegral.integral_of_le (hab.trans hbc)] at hh
  simp only [integral_Icc_eq_integral_Ioc]
  rw [←hh]
  ring

/-- Changing the spectral center adds precisely the difference of the
squared centers times the source time profile. -/
theorem spectralResidualSchwartz_change_center (t s : ℝ) (f : SchwartzMap ℝ ℂ) :
    spectralResidualSchwartz t f = spectralResidualSchwartz s f+
      (((s:ℂ)^2-(t:ℂ)^2)) • f := by
  unfold spectralResidualSchwartz
  module

/-- The same change of center holds for the literal Hilbert-space columns. -/
theorem cylinderTimeColumn_change_center (t s : ℝ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f:ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even t f he)
      R hR (spectralTimeResidual_support t f R hs) z =
    cylinderTimeColumn (spectralResidualSchwartz s f)
      (spectralResidualSchwartz_compact s f hc) (spectralResidualSchwartz_even s f he)
      R hR (spectralTimeResidual_support s f R hs) z+
      ((s:ℂ)^2-(t:ℂ)^2) • cylinderTimeColumn f hc he R hR hs z := by
  apply cylinderAutomorphic.injective
  have hh := cylinderTimeColumn_linear (spectralResidualSchwartz s f) f
    (spectralResidualSchwartz t f) (spectralResidualSchwartz_compact s f hc) hc
    (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even s f he) he
    (spectralResidualSchwartz_even t f he) R hR (spectralTimeResidual_support s f R hs) hs
    (spectralTimeResidual_support t f R hs) 1 ((s:ℂ)^2-(t:ℂ)^2)
    (by rw [one_smul]; exact spectralResidualSchwartz_change_center t s f) z
  simpa only [one_smul,map_add,map_smul] using hh

#print axioms windowTimeSchwartz_add_intervals
#print axioms spectralResidualSchwartz_change_center
#print axioms cylinderTimeColumn_change_center
end QuantitativeMaass
