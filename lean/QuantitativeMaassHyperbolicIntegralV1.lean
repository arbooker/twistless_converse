module

public import QuantitativeMaassGreenCompactV1
public import QuantitativeMaassPoincareChartExtensionV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass
open MaassDifferential

/-- The actual hyperbolic volume in Cartesian coordinates, for Bochner
integrals. This follows from Mathlib's volume definition and the exact
Lebesgue normalization on the complex plane. -/
theorem integral_upper_cartesian (F : Point → ℂ) :
    (∫ z : ℍ, upperFunction F z) =
      ∫ Z in {Z : Point | 0<Z.2}, F Z/(Z.2:ℂ)^2 := by
  have hm : Measurable (fun z : ℍ => (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2) := by
    fun_prop
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  rw [UpperHalfPlane.volume_def,integral_withDensity_eq_integral_smul hm]
  calc
    _ = ∫ z : ℍ, F (z.re,z.im)/(z.im:ℂ)^2 ∂volume.comap UpperHalfPlane.coe := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp [upperFunction,NNReal.smul_def,Complex.real_smul,div_eq_mul_inv,
          inv_pow,mul_comm]
    _ = ∫ z : ℂ in range UpperHalfPlane.coe, F (z.re,z.im)/(z.im:ℂ)^2 :=
      hp.integral_comp measurableEmbedding_coe (fun z : ℂ => F (z.re,z.im)/(z.im:ℂ)^2)
    _ = ∫ Z in {Z : Point | 0<Z.2}, F Z/(Z.2:ℂ)^2 := by
      have h := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun Z : Point => F Z/(Z.2:ℂ)^2) {Z : Point | 0<Z.2}
      rw [range_coe]
      exact h

/-- Compact positive-height support permits removal of the positive-height
restriction, without extending hyperbolic volume across its singular edge. -/
theorem integral_upper_cartesian_of_support (F : Point → ℂ)
    (hF : Function.support F⊆{Z : Point | 0<Z.2}) :
    (∫ z : ℍ, upperFunction F z)=∫ Z : Point, F Z/(Z.2:ℂ)^2 := by
  rw [integral_upper_cartesian]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro Z hZ
  have hz : F Z=0 := by
    by_contra hn
    exact hZ (hF hn)
  simp [hz]

#print axioms integral_upper_cartesian

end QuantitativeMaass
