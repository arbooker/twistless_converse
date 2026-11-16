module

public import QuantitativeMaassParabolicVariationScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem parabolicLineProfile_mass_scale (g : ℝ → ℂ) (y : ℝ) (hy : 0<y) :
    (∫ v,parabolicLineProfile g y v)=y • ∫ v,parabolicLineProfile g 1 v := by
  simp_rw [parabolicLineProfile_height_scale g y]
  rw [Measure.integral_comp_div (parabolicLineProfile g 1) y,abs_of_pos hy]

theorem parabolicLineProfile_lattice_scale (g : ℝ → ℂ) (y q a v : ℝ)
    (hy : y≠0) (hq : q≠0) :
    parabolicLineProfile g (y/q) (a/q+v)=parabolicLineProfile g y (a+q*v) := by
  unfold parabolicLineProfile
  congr 2
  field_simp

/-- Every real lattice spacing and shift has the same height-independent
variation bound for its horizontal-profile discrepancy. -/
theorem parabolicLineProfile_spacing_discrepancy (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (y q a : ℝ) (hy : 0<y) (hq : 0<q) :
    Summable (fun n : ℤ => parabolicLineProfile g y (a+q*n)) ∧
      ‖(∑' n : ℤ,parabolicLineProfile g y (a+q*n))-
        q⁻¹ • ∫ v,parabolicLineProfile g y v‖≤
      ∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  have hh := parabolicLineProfile_lattice_discrepancy g hg B hs (y/q) (div_pos hy hq) (a/q)
  simp_rw [parabolicLineProfile_lattice_scale g y q a _ hy.ne' hq.ne'] at hh
  have hm : (∫ v,parabolicLineProfile g (y/q) v)=q⁻¹ • ∫ v,parabolicLineProfile g y v := by
    rw [parabolicLineProfile_mass_scale g (y/q) (div_pos hy hq),
      parabolicLineProfile_mass_scale g y hy,smul_smul]
    congr 1
    ring
  rw [hm,parabolicLineProfile_variation_scale g hg (y/q) (div_pos hy hq)] at hh
  exact hh

#print axioms parabolicLineProfile_mass_scale
#print axioms parabolicLineProfile_lattice_scale
#print axioms parabolicLineProfile_spacing_discrepancy

end QuantitativeMaass
