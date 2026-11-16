module

public import AsymptoticFlatHyperbolicV1
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- A scalar majorant for the hyperbolic square norm: bounded below a
positive height and inverse-square above it. -/
theorem height_square_majorant_integrable (ε C D : ℝ) (hε : 0<ε) :
    Integrable (fun y : ℝ => (Ioc 0 ε).indicator (fun _ => C^2) y+
      (Ioi ε).indicator (fun y => D^2/y^2) y) volume := by
  have hl : IntegrableOn (fun _ : ℝ => C^2) (Ioc 0 ε) volume :=
    integrableOn_const (by simp)
  have hh : IntegrableOn (fun y : ℝ => 1/y^2) (Ioi ε) volume := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hε).congr_fun _ measurableSet_Ioi
    intro y hy
    dsimp only
    rw [Real.rpow_neg (hε.trans hy).le,Real.rpow_two]
    simp
  have ht : IntegrableOn (fun y : ℝ => D^2/y^2) (Ioi ε) volume := by
    change Integrable (fun y : ℝ => D^2/y^2) (volume.restrict (Ioi ε))
    simpa only [mul_one_div] using hh.const_mul (D^2)
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr hl).add
    ((integrable_indicator_iff measurableSet_Ioi).mpr ht)

/-- A continuous physical function that vanishes at least linearly at zero
and is bounded at infinity has a genuine strip-supported hyperbolic L²
representative. The change from flat to hyperbolic area is explicit. -/
theorem strip_memLp_of_height_bounds (f : ℍ → ℂ) (hf : Continuous f)
    (ε C D : ℝ) (hε : 0<ε)
    (hlow : ∀ z : ℍ,z.im≤ε → ‖f z‖≤C*z.im)
    (hhigh : ∀ z : ℍ,ε≤z.im → ‖f z‖≤D) :
    MemLp (AsymptoticMassTransport.strip.indicator f) 2 volume := by
  let H : ℝ → ℝ := fun y => (Ioc 0 ε).indicator (fun _ => C^2) y+
    (Ioi ε).indicator (fun y => D^2/y^2) y
  have hH : Integrable H volume := height_square_majorant_integrable ε C D hε
  have hp := (hH.integrableOn (s:=Ioi (0:ℝ))).comp_snd (volume.restrict (Ico (0:ℝ) 1))
  have hc : Integrable (fun z : ℍ => H z.im) AsymptoticStripCoordinates.flatStrip :=
    AsymptoticStripCoordinates.coordinates_preserving.integrable_comp_of_integrable hp
  have hi : Integrable (AsymptoticMassTransport.strip.indicator (fun z : ℍ => H z.im))
      AsymptoticStripCoordinates.flat :=
    (integrable_indicator_iff AsymptoticMassTransport.strip_measurable).mpr hc
  have hm : AEStronglyMeasurable (AsymptoticMassTransport.strip.indicator f) volume :=
    hf.aestronglyMeasurable.indicator AsymptoticMassTransport.strip_measurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [AsymptoticFlatHyperbolic.hyperbolic_density,
    integrable_withDensity_iff_integrable_coe_smul AsymptoticFlatHyperbolic.density_measurable]
  apply hi.mono_nonneg
  · exact ((AsymptoticFlatHyperbolic.density_measurable.coe_nnreal_real.aestronglyMeasurable).mul
      ((hf.aestronglyMeasurable.indicator AsymptoticMassTransport.strip_measurable).norm.pow 2))
  · exact Eventually.of_forall (fun z => mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
  · apply Eventually.of_forall
    intro z
    classical
    by_cases hs : z∈AsymptoticMassTransport.strip
    · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs]
      change (1/z.im)^2*‖f z‖^2≤H z.im
      by_cases hz : z.im≤ε
      · have he : H z.im=C^2 := by simp [H,z.im_pos,hz,not_lt.mpr hz]
        rw [he]
        have hb := pow_le_pow_left₀ (norm_nonneg (f z)) (hlow z hz) 2
        calc
          _ ≤ (1/z.im)^2*(C*z.im)^2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = _ := by field_simp
      · have he : H z.im=D^2/z.im^2 := by simp [H,not_le.mp hz,hz]
        rw [he]
        have hb := pow_le_pow_left₀ (norm_nonneg (f z)) (hhigh z (le_of_not_ge hz)) 2
        calc
          _ ≤ (1/z.im)^2*D^2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = _ := by ring
    · simp [hs]

#print axioms height_square_majorant_integrable
#print axioms strip_memLp_of_height_bounds

end QuantitativeMaass
