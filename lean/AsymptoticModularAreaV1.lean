module

public import AsymptoticModularAreaIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticModularDomain

open MeasureTheory UpperHalfPlane Set
open scoped ENNReal NNReal Modular

def openRegion : Set (ℝ×ℝ) :=
  {q | q.1∈Ioo (-(1:ℝ)/2) (1/2) ∧ Real.sqrt (1-q.1^2)<q.2}

theorem openRegion_measurable : MeasurableSet openRegion := by
  apply MeasurableSet.inter
  · exact measurableSet_Ioo.preimage measurable_fst
  · exact measurableSet_lt (by fun_prop) measurable_snd

theorem open_domain_image : UpperHalfPlane.coe '' 𝒟ᵒ=
    Complex.measurableEquivRealProd.symm '' openRegion := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨(w.re,w.im),?_,rfl⟩
    change w.re∈Ioo (-(1:ℝ)/2) (1/2) ∧ Real.sqrt (1-w.re^2)<w.im
    have hnorm : 1<w.re^2+w.im^2 := by
      simpa only [UpperHalfPlane.re,UpperHalfPlane.im,Complex.normSq_apply,pow_two] using hw.1
    refine ⟨?_,(Real.sqrt_lt' w.im_pos).mpr (by linarith)⟩
    have h := abs_lt.mp hw.2
    constructor <;> linarith [h.1,h.2]
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    have hy : 0<y := (Real.sqrt_nonneg _).trans_lt hxy.2
    refine ⟨⟨⟨x,y⟩,hy⟩,?_,rfl⟩
    change 1<Complex.normSq ⟨x,y⟩ ∧ |x|<(1:ℝ)/2
    have hs := (Real.sqrt_lt' hy).mp hxy.2
    constructor
    · simp only [Complex.normSq_apply]
      nlinarith
    · apply abs_lt.mpr
      constructor <;> linarith [hxy.1.1,hxy.1.2]

/-- Fubini applied to the actual hyperbolic density above the circular
boundary of the open modular domain. -/
theorem open_region_integral :
    (∫⁻ q : ℝ×ℝ in openRegion,(↑((1/‖q.2‖₊)^2 : ℝ≥0) : ℝ≥0∞))=
      ENNReal.ofReal (Real.pi/3) := by
  classical
  let f : ℝ×ℝ → ℝ≥0∞ := fun q => ↑((1/‖q.2‖₊)^2 : ℝ≥0)
  rw [← lintegral_indicator openRegion_measurable,Measure.volume_eq_prod,
    lintegral_prod _ (((by fun_prop : Measurable f).indicator openRegion_measurable).aemeasurable)]
  have he : (fun x : ℝ => ∫⁻ y : ℝ,openRegion.indicator f (x,y))=
      (Ioo (-(1:ℝ)/2) (1/2)).indicator (fun x => ENNReal.ofReal ((Real.sqrt (1-x^2))⁻¹)) := by
    funext x
    by_cases hx : x∈Ioo (-(1:ℝ)/2) (1/2)
    · rw [Set.indicator_of_mem hx]
      have hf : (fun y : ℝ => openRegion.indicator f (x,y))=
          (Ioi (Real.sqrt (1-x^2))).indicator (fun y => (↑((1/‖y‖₊)^2 : ℝ≥0) : ℝ≥0∞)) := by
        funext y
        by_cases hy : Real.sqrt (1-x^2)<y
        · rw [Set.indicator_of_mem (show (x,y)∈openRegion from ⟨hx,hy⟩),
            Set.indicator_of_mem (show y∈Ioi (Real.sqrt (1-x^2)) from hy)]
        · rw [Set.indicator_of_notMem (show (x,y)∉openRegion from fun h => hy h.2),
            Set.indicator_of_notMem (show y∉Ioi (Real.sqrt (1-x^2)) from hy)]
      rw [hf,lintegral_indicator measurableSet_Ioi]
      exact AsymptoticHyperbolicArea.vertical_area (sqrt_lower_pos ⟨hx.1.le,hx.2.le⟩)
    · rw [Set.indicator_of_notMem hx]
      have hf : (fun y : ℝ => openRegion.indicator f (x,y))=0 := by
        funext y
        rw [Set.indicator_of_notMem (show (x,y)∉openRegion from fun h => hx h.1)]
        rfl
      rw [hf]
      exact lintegral_zero_fun
  change (∫⁻ x : ℝ,∫⁻ y : ℝ,openRegion.indicator f (x,y))=_
  rw [he,lintegral_indicator measurableSet_Ioo]
  exact inverse_sqrt_lintegral

theorem open_domain_area : (volume : Measure ℍ) 𝒟ᵒ=ENNReal.ofReal (Real.pi/3) := by
  rw [UpperHalfPlane.volume_eq_lintegral,open_domain_image]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  exact open_region_integral

/-- The standard projective modular domain has hyperbolic area pi/3. -/
theorem closed_domain_area : (volume : Measure ℍ) 𝒟=ENNReal.ofReal (Real.pi/3) := by
  have he : (volume : Measure ℍ) 𝒟=(volume : Measure ℍ) 𝒟ᵒ := by
    exact (measure_eq_measure_of_null_sdiff ModularGroup.fdo_subset_fd boundary_null).symm
  rw [he,open_domain_area]

#print axioms openRegion_measurable
#print axioms open_domain_image
#print axioms open_region_integral
#print axioms open_domain_area
#print axioms closed_domain_area

end AsymptoticModularDomain
