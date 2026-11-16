module

public import QuantitativeMaassCuspRectangleIntegralV1
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- Continuous functions give genuine local L2 vectors on compact sets. -/
theorem continuous_memLp_compact (K : Set ℍ) (hK : IsCompact K)
    (F : ℍ → ℂ) (hF : Continuous F) : MemLp F 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C,hC⟩ := hK.bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hK.measurableSet] with Z hZ
  exact hC (mem_image_of_mem _ hZ)

/-- Continuous height tests are L2 for the exact compact-region marginal. -/
theorem heightTest_memLp (K : Set ℍ) (hK : IsCompact K)
    (g : ℝ → ℂ) (hg : Continuous g) : MemLp g 2 (heightMeasure K) := by
  apply (memLp_map_measure_iff hg.aestronglyMeasurable
    continuous_im.measurable.aemeasurable).mpr
  exact continuous_memLp_compact K hK (g ∘ UpperHalfPlane.im) (hg.comp continuous_im)

def heightTestVector (K : Set ℍ) (hK : IsCompact K)
    (g : ℝ → ℂ) (hg : Continuous g) : Lp ℂ 2 (heightMeasure K) :=
  (heightTest_memLp K hK g hg).toLp g

theorem heightTestVector_ae (K : Set ℍ) (hK : IsCompact K)
    (g : ℝ → ℂ) (hg : Continuous g) :
    (heightTestVector K hK g hg : ℝ → ℂ)=ᵐ[heightMeasure K] g :=
  MemLp.coeFn_toLp _

/-- The adjoint average paired with a continuous height test is the literal
hyperbolic integral of that test against the original local L2 function. -/
theorem localHeightAverage_test (K : Set ℍ) (hK : IsCompact K)
    (g : ℝ → ℂ) (hg : Continuous g) (f : Lp ℂ 2 (volume.restrict K)) :
    inner ℂ (heightTestVector K hK g hg) (localHeightAverage K f)=
      ∫ Z in K, star (g Z.im)*f Z := by
  have he : inner ℂ (heightTestVector K hK g hg) (localHeightAverage K f)=
      ∫ Z in K, star (heightTestVector K hK g hg Z.im)*f Z :=
    FiberAverage.average_pairing_integral _ _ _ _ _
  rw [he]
  apply integral_congr_ae
  filter_upwards [ae_of_ae_map continuous_im.measurable.aemeasurable
    (heightTestVector_ae K hK g hg)] with Z hZ
  rw [hZ]

/-- An explicit horocycle integral formula for the bounded average, with no
assumed Fubini or disintegration identity. -/
theorem localHeightAverage_rectangle_test (l r a b : ℝ) (ha : 0<a)
    (F : ℍ → ℂ) (hF : Continuous F)
    (f : Lp ℂ 2 (volume.restrict (upperRectangle l r a b)))
    (hf : (f : ℍ → ℂ)=ᵐ[volume.restrict (upperRectangle l r a b)] F)
    (g : ℝ → ℂ) (hg : Continuous g) :
    inner ℂ (heightTestVector _ (upperRectangle_compact l r a b ha) g hg)
      (localHeightAverage (upperRectangle l r a b) f)=
      ∫ y in Icc a b, star (g y)*
        (∫ x in Icc l r, F (cartesianLift (x,y)))/(y:ℂ)^2 := by
  rw [localHeightAverage_test]
  have he : (∫ Z in upperRectangle l r a b, star (g Z.im)*f Z)=
      ∫ Z in upperRectangle l r a b, star (g Z.im)*F Z := by
    apply integral_congr_ae
    filter_upwards [hf] with Z hZ
    rw [hZ]
  rw [he,integral_upperRectangle_iterated l r a b ha
    (fun Z => star (g Z.im)*F Z) (((hg.comp continuous_im).star).mul hF)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hp : 0<y := ha.trans_le hy.1
  have he' : (fun x : ℝ => star (g (cartesianLift (x,y)).im)*
      F (cartesianLift (x,y))/(y:ℂ)^2)=
      fun x => star (g y)*F (cartesianLift (x,y))/(y:ℂ)^2 := by
    funext x
    rw [cartesianLift_positive _ hp]
    rfl
  rw [he',integral_div,integral_const_mul]

#print axioms continuous_memLp_compact
#print axioms heightTest_memLp
#print axioms localHeightAverage_rectangle_test

end QuantitativeMaass
