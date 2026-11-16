module

public import QuantitativeMaassCayleyMeasureV1
public import QuantitativeMaassComplexRadialIntegralV1
public import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

theorem integral_cayleyDisk_normSq (f : ℝ → ℂ) :
    (∫ z in cayleyDisk,f (Complex.normSq z))=
      (Real.pi:ℂ)*∫ u in Ioo (0:ℝ) 1,f u := by
  have he : (∫ z in cayleyDisk,f (Complex.normSq z))=
      ∫ z : ℂ, (Iio (1:ℝ)).indicator f (Complex.normSq z) := by
    rw [← integral_indicator cayleyDisk_measurable]
    rfl
  rw [he,integral_complex_normSq,setIntegral_indicator measurableSet_Iio]
  rfl

def diskRadialVariable (u : ℝ) : ℝ := (1+u)/(1-u)

theorem diskRadialVariable_hasDerivAt {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) :
    HasDerivAt diskRadialVariable (2/(1-u)^2) u := by
  have hd : 1-u≠0 := ne_of_gt (sub_pos.mpr hu.2)
  have h := ((hasDerivAt_id u).const_add 1).div ((hasDerivAt_id u).const_sub 1) hd
  convert h using 1
  · rfl
  · simp only [id_eq,one_mul]
    ring

theorem diskRadialVariable_injOn : InjOn diskRadialVariable (Ioo (0:ℝ) 1) := by
  intro u hu v hv he
  have hd : 1-u≠0 := ne_of_gt (sub_pos.mpr hu.2)
  have hd' : 1-v≠0 := ne_of_gt (sub_pos.mpr hv.2)
  have h := (div_eq_div_iff hd hd').mp he
  nlinarith

theorem diskRadialVariable_image : diskRadialVariable '' Ioo (0:ℝ) 1=Ioi (1:ℝ) := by
  ext q
  constructor
  · rintro ⟨u,hu,rfl⟩
    change 1<(1+u)/(1-u)
    apply (lt_div_iff₀ (sub_pos.mpr hu.2)).mpr
    linarith [hu.1]
  · intro hq
    change 1<q at hq
    have hd : 0<q+1 := by linarith
    refine ⟨(q-1)/(q+1),⟨div_pos (by linarith) hd,?_⟩,?_⟩
    · apply (div_lt_one hd).mpr
      linarith
    · unfold diskRadialVariable
      field_simp
      ring

/-- The remaining radial Jacobian is exact, without an assumed polar
integration law for the hyperbolic plane. -/
theorem integral_diskRadialVariable (f : ℝ → ℂ) :
    (∫ u in Ioo (0:ℝ) 1,(4/(1-u)^2:ℝ) • f (diskRadialVariable u))=
      (2:ℂ)*∫ q in Ioi (1:ℝ),f q := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (diskRadialVariable_hasDerivAt hu).hasDerivWithinAt)
    diskRadialVariable_injOn f
  rw [diskRadialVariable_image] at h
  rw [h,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [abs_of_nonneg (by positivity : 0≤2/(1-u)^2)]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- The actual hyperbolic radial integration formula at i. -/
theorem integral_hyperbolic_radial_I (g : ℝ → ℂ) :
    (∫ z : ℍ,g (Real.cosh (dist z UpperHalfPlane.I)))=
      (2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q := by
  have he : (fun z : ℍ => g (Real.cosh (dist z UpperHalfPlane.I)))=
      (fun z : ℍ => g (radialCoordinate 0 1 (z.re,z.im))) := by
    funext z
    rw [← radialCoordinate_eq_cosh_dist z UpperHalfPlane.I]
    rfl
  rw [he]
  change (∫ z : ℍ,g (radialCoordinate 0 1 ((z:ℂ).re,(z:ℂ).im)))=_
  rw [integral_upper_cayley (fun z => g (radialCoordinate 0 1 (z.re,z.im)))]
  have hc : (∫ z in cayleyDisk,(4/(1-Complex.normSq z)^2:ℝ) •
      g (radialCoordinate 0 1 ((cayleyMap z).re,(cayleyMap z).im)))=
      ∫ z in cayleyDisk,(fun u : ℝ => (4/(1-u)^2:ℝ) • g (diskRadialVariable u))
        (Complex.normSq z) := by
    apply setIntegral_congr_fun cayleyDisk_measurable
    intro z hz
    dsimp only
    rw [cayleyMap_radial hz]
    rfl
  rw [hc,integral_cayleyDisk_normSq
    (fun u : ℝ => (4/(1-u)^2:ℝ) • g (diskRadialVariable u)),integral_diskRadialVariable]
  ring

/-- The radial measure formula at every actual hyperbolic centre, by
measure preservation and isometry of the transitive real matrix action. -/
theorem integral_hyperbolic_radial (g : ℝ → ℂ) (w : ℍ) :
    (∫ z : ℍ,g (Real.cosh (dist z w)))=
      (2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q := by
  have h := integral_smul_eq_self (μ:=volume) (g:=(w.toSL2R : Matrix.GeneralLinearGroup (Fin 2) ℝ))
    (fun z : ℍ => g (Real.cosh (dist z w)))
  change (∫ z : ℍ,g (Real.cosh (dist (w.toSL2R • z) w)))=∫ z : ℍ,g (Real.cosh (dist z w)) at h
  have he (z : ℍ) : dist (w.toSL2R • z) w=dist z UpperHalfPlane.I := by
    calc
      _ = dist (w.toSL2R • z) (w.toSL2R • UpperHalfPlane.I) := by rw [toSL2R_smul_I]
      _ = _ := dist_smul _ _ _
  simp_rw [he] at h
  rw [← h,integral_hyperbolic_radial_I]

#print axioms diskRadialVariable_image
#print axioms integral_diskRadialVariable
#print axioms integral_hyperbolic_radial_I
#print axioms integral_hyperbolic_radial

end QuantitativeMaass
