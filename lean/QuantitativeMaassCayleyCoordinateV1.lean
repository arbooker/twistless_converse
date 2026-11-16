module

public import QuantitativeMaassRadialCoordinateV1
public import QuantitativeMaassHyperbolicIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def cayleyDisk : Set ℂ := {z | Complex.normSq z<1}
def cayleyMap (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)
def cayleyInverse (w : ℂ) : ℂ := (w-Complex.I)/(w+Complex.I)

theorem cayleyDisk_measurable : MeasurableSet cayleyDisk :=
  measurableSet_lt Complex.continuous_normSq.measurable measurable_const

theorem cayleyDenom_ne_zero {z : ℂ} (hz : z∈cayleyDisk) : 1-z≠0 := by
  intro h
  have he : z=1 := (sub_eq_zero.mp h).symm
  simp [cayleyDisk,he] at hz

theorem cayleyMap_im (z : ℂ) :
    (cayleyMap z).im=(1-Complex.normSq z)/Complex.normSq (1-z) := by
  simp only [cayleyMap,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.sub_im,Complex.one_re,Complex.one_im,zero_mul,one_mul,zero_add,
    zero_sub,Complex.normSq_apply]
  ring

theorem cayleyMap_normSq (z : ℂ) :
    Complex.normSq (cayleyMap z)=Complex.normSq (1+z)/Complex.normSq (1-z) := by
  simp only [cayleyMap,map_div₀,map_mul,Complex.normSq_I,one_mul]

theorem cayleyMap_im_pos {z : ℂ} (hz : z∈cayleyDisk) : 0<(cayleyMap z).im := by
  rw [cayleyMap_im]
  exact div_pos (sub_pos.mpr hz) (Complex.normSq_pos.mpr (cayleyDenom_ne_zero hz))

theorem cayleyInverse_denom {w : ℂ} (hw : 0<w.im) : w+Complex.I≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hi
  linarith

theorem cayleyInverse_disk {w : ℂ} (hw : 0<w.im) : cayleyInverse w∈cayleyDisk := by
  change Complex.normSq ((w-Complex.I)/(w+Complex.I))<1
  rw [map_div₀,div_lt_one (Complex.normSq_pos.mpr (cayleyInverse_denom hw))]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,sub_zero,add_zero]
  nlinarith

theorem cayleyMap_add_I {z : ℂ} (hz : 1-z≠0) :
    cayleyMap z+Complex.I=2*Complex.I/(1-z) := by
  unfold cayleyMap
  field_simp
  ring

theorem cayleyInverse_left {z : ℂ} (hz : z∈cayleyDisk) :
    cayleyInverse (cayleyMap z)=z := by
  have hd := cayleyDenom_ne_zero hz
  have hp : cayleyMap z+Complex.I≠0 := by
    rw [cayleyMap_add_I hd]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hd
  apply (div_eq_iff hp).mpr
  change cayleyMap z-Complex.I=z*(cayleyMap z+Complex.I)
  unfold cayleyMap
  field_simp
  ring

theorem cayleyInverse_right {w : ℂ} (hw : 0<w.im) :
    cayleyMap (cayleyInverse w)=w := by
  have hd := cayleyInverse_denom hw
  have hi := cayleyDenom_ne_zero (cayleyInverse_disk hw)
  apply (div_eq_iff hi).mpr
  change Complex.I*(1+(w-Complex.I)/(w+Complex.I))=
    w*(1-(w-Complex.I)/(w+Complex.I))
  field_simp
  ring

theorem cayleyMap_injOn : InjOn cayleyMap cayleyDisk := by
  intro z hz w hw he
  rw [← cayleyInverse_left hz,← cayleyInverse_left hw,he]

theorem cayleyMap_image : cayleyMap '' cayleyDisk={w : ℂ | 0<w.im} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact cayleyMap_im_pos hz
  · intro hw
    exact ⟨cayleyInverse w,cayleyInverse_disk hw,cayleyInverse_right hw⟩

/-- The Cayley disk radius gives the actual hyperbolic radial coordinate
about i, without a polar-coordinate assumption. -/
theorem cayleyMap_radial {z : ℂ} (hz : z∈cayleyDisk) :
    radialCoordinate 0 1 ((cayleyMap z).re,(cayleyMap z).im)=
      (1+Complex.normSq z)/(1-Complex.normSq z) := by
  have hd := ne_of_gt (Complex.normSq_pos.mpr (cayleyDenom_ne_zero hz))
  have hn : 1-Complex.normSq z≠0 := ne_of_gt (sub_pos.mpr hz)
  have hnorm : (cayleyMap z).re^2+(cayleyMap z).im^2=Complex.normSq (cayleyMap z) := by
    simp only [Complex.normSq_apply,pow_two]
  simp only [radialCoordinate,sub_zero,one_pow,mul_one]
  rw [hnorm,cayleyMap_im,cayleyMap_normSq]
  field_simp
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.sub_im,Complex.one_re,Complex.one_im,zero_add,zero_sub]
  ring

#print axioms cayleyMap_image
#print axioms cayleyMap_injOn
#print axioms cayleyMap_radial

end QuantitativeMaass
