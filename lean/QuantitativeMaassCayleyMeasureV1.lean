module

public import QuantitativeMaassCayleyCoordinateV1
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass

/-- The actual hyperbolic measure as a complex-plane weighted integral. -/
theorem integral_upper_complex (f : ℂ → ℂ) :
    (∫ z : ℍ, f z)=∫ z in {z : ℂ | 0<z.im}, f z/(z.im:ℂ)^2 := by
  have hm : Measurable (fun z : ℍ => (1/NNReal.mk z.im z.im_pos.le:ℝ≥0)^2) := by
    fun_prop
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  rw [UpperHalfPlane.volume_def,integral_withDensity_eq_integral_smul hm]
  calc
    _ = ∫ z : ℍ, f z/(z.im:ℂ)^2 ∂volume.comap UpperHalfPlane.coe := by
      apply integral_congr_ae
      filter_upwards with z
      simp [NNReal.smul_def,Complex.real_smul,div_eq_mul_inv,inv_pow,mul_comm]
    _ = ∫ z : ℂ in range UpperHalfPlane.coe, f z/(z.im:ℂ)^2 :=
      hp.integral_comp measurableEmbedding_coe (fun z : ℂ => f z/(z.im:ℂ)^2)
    _ = _ := by rw [range_coe]

def cayleyFDeriv (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (2*Complex.I/(1-z)^2)).restrictScalars ℝ

theorem cayleyMap_hasDerivAt {z : ℂ} (hz : z∈cayleyDisk) :
    HasDerivAt cayleyMap (2*Complex.I/(1-z)^2) z := by
  have hd := cayleyDenom_ne_zero hz
  have h := (((hasDerivAt_id z).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id z).const_sub 1) hd
  convert h using 1
  · rfl
  · simp only [id_eq,mul_one]
    ring

theorem cayleyMap_hasFDerivAt {z : ℂ} (hz : z∈cayleyDisk) :
    HasFDerivAt cayleyMap (cayleyFDeriv z) z :=
  (cayleyMap_hasDerivAt hz).hasFDerivAt.restrictScalars ℝ

theorem cayleyFDeriv_det (z : ℂ) :
    (cayleyFDeriv z).det=4/(Complex.normSq (1-z))^2 := by
  norm_num [cayleyFDeriv,ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,map_div₀,map_pow,map_mul]

/-- Exact disk density of the actual upper-half-plane measure. This is
proved by the injective Cayley map and its real Jacobian, for Bochner integrals. -/
theorem integral_upper_cayley (f : ℂ → ℂ) :
    (∫ z : ℍ, f z)=∫ z in cayleyDisk,
      (4/(1-Complex.normSq z)^2:ℝ) • f (cayleyMap z) := by
  rw [integral_upper_complex,← cayleyMap_image]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume cayleyDisk_measurable
    (fun z hz => (cayleyMap_hasFDerivAt hz).hasFDerivWithinAt) cayleyMap_injOn]
  apply setIntegral_congr_fun cayleyDisk_measurable
  intro z hz
  have hd : Complex.normSq (1-z)≠0 :=
    ne_of_gt (Complex.normSq_pos.mpr (cayleyDenom_ne_zero hz))
  have hn : 1-Complex.normSq z≠0 := ne_of_gt (sub_pos.mpr hz)
  dsimp only
  rw [cayleyFDeriv_det,abs_of_nonneg (by positivity : 0≤4/(Complex.normSq (1-z))^2),
    cayleyMap_im]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
  have hd' : (Complex.normSq (1-z):ℂ)≠0 := by exact_mod_cast hd
  have hn' : 1-(Complex.normSq z:ℂ)≠0 := by exact_mod_cast hn
  field_simp

#print axioms integral_upper_complex
#print axioms cayleyMap_hasFDerivAt
#print axioms cayleyFDeriv_det
#print axioms integral_upper_cayley

end QuantitativeMaass
