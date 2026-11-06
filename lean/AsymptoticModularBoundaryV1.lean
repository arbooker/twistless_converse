module

public import AsymptoticHyperbolicAreaV1
public import Mathlib.NumberTheory.Modular
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticModularDomain

open MeasureTheory UpperHalfPlane Set
open scoped ENNReal Modular

/-- Complex Lebesgue-null sets are also hyperbolically null on the
upper half-plane, whose measure has a positive density there. -/
theorem null_of_complex_null (s : Set ℂ) (hs : (volume : Measure ℂ) s=0) :
    (volume : Measure ℍ) (UpperHalfPlane.coe ⁻¹' s)=0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  exact measure_mono_null (Set.image_preimage_subset _ _) hs

theorem vertical_line_null (a : ℝ) : (volume : Measure ℍ) {z | z.re=a}=0 := by
  apply null_of_complex_null {z : ℂ | z.re=a}
  have he : {z : ℂ | z.re=a}=Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (univ : Set ℝ)) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [he]
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage (by measurability)]
  rw [Measure.volume_eq_prod,Measure.prod_prod]
  simp

theorem unit_circle_null : (volume : Measure ℍ) {z | Complex.normSq (z:ℂ)=1}=0 := by
  have hs : {z : ℂ | Complex.normSq z=1}=Metric.sphere 0 1 := by
    ext z
    simp only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h
      nlinarith [norm_nonneg z]
    · intro h
      rw [h,one_pow]
  apply null_of_complex_null {z : ℂ | Complex.normSq z=1}
  rw [hs]
  exact Measure.addHaar_sphere volume (0:ℂ) 1

/-- Only two vertical segments and one circle arc separate the closed
and open modular domains; all three are null for hyperbolic measure. -/
theorem boundary_null : (volume : Measure ℍ) (𝒟 \ 𝒟ᵒ)=0 := by
  apply measure_mono_null (t:={z : ℍ | z.re=1/2}∪{z : ℍ | z.re= -1/2}∪
    {z : ℍ | Complex.normSq (z:ℂ)=1})
  · intro z hz
    have hd := hz.1
    have ho := hz.2
    change 1≤Complex.normSq (z:ℂ) ∧ |z.re|≤(1:ℝ)/2 at hd
    change ¬(1<Complex.normSq (z:ℂ) ∧ |z.re|<(1:ℝ)/2) at ho
    rcases lt_or_eq_of_le hd.1 with hc | hc
    · have he : |z.re|=(1:ℝ)/2 := le_antisymm hd.2 (not_lt.mp (fun h => ho ⟨hc,h⟩))
      have he' : z.re=1/2 ∨ z.re= -1/2 := by
        simpa only [neg_div] using (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp he
      exact Or.inl he'
    · exact Or.inr hc.symm
  · exact measure_union_null (measure_union_null (vertical_line_null (1/2))
      (vertical_line_null (-1/2))) unit_circle_null

#print axioms null_of_complex_null
#print axioms vertical_line_null
#print axioms unit_circle_null
#print axioms boundary_null

end AsymptoticModularDomain
