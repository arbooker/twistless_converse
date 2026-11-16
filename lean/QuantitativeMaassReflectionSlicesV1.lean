module

public import QuantitativeMaassGeometricLimitV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- A quadratic slice is short above a fixed positive height, uniformly in
its constant term. This avoids any separation hypothesis on its roots. -/
theorem quadratic_height_slice_volume (a c Y δ : ℝ) (hc : 1≤|c|)
    (hY : 0<Y) (_hδ : 0≤δ) :
    volume {y : ℝ | Y≤y ∧ |a-c*y^2|<δ}≤ENNReal.ofReal (2*δ/Y) := by
  let S := {y : ℝ | Y≤y ∧ |a-c*y^2|<δ}
  by_cases hs : S.Nonempty
  · obtain ⟨y0,hy0⟩ := hs
    have hsub : S⊆Icc (y0-δ/Y) (y0+δ/Y) := by
      intro y hy
      have hh : |c| * |y^2-y0^2|<2*δ := by
        calc
          _ = |(a-c*y^2)-(a-c*y0^2)| := by
            rw [show (a-c*y^2)-(a-c*y0^2)= -c*(y^2-y0^2) by ring,abs_mul,abs_neg]
          _ ≤ |a-c*y^2|+|a-c*y0^2| := abs_sub _ _
          _ < _ := by linarith [hy.2,hy0.2]
      have hfac : |y^2-y0^2|=|y-y0| * (y+y0) := by
        rw [show y^2-y0^2=(y-y0)*(y+y0) by ring,abs_mul,abs_of_pos (show 0<y+y0 by linarith [hy.1,hy0.1])]
      have h1 : |y-y0| * (2*Y)≤|y^2-y0^2| := by
        rw [hfac]
        exact mul_le_mul_of_nonneg_left (by linarith [hy.1,hy0.1]) (abs_nonneg _)
      have h2 : |y^2-y0^2|≤|c| * |y^2-y0^2| := le_mul_of_one_le_left (abs_nonneg _) hc
      have hd : |y-y0|≤δ/Y := (le_div_iff₀ hY).mpr (by linarith)
      obtain ⟨hlo,hhi⟩ := abs_le.mp hd
      constructor <;> linarith
    apply (measure_mono hsub).trans_eq
    rw [Real.volume_Icc]
    congr 1
    ring
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    change volume S≤_
    rw [he,measure_empty]
    exact bot_le

/-- A linear slice is short uniformly in its translation. -/
theorem affine_slice_volume (a b δ : ℝ) (ha : 1≤|a|) (_hδ : 0≤δ) :
    volume {x : ℝ | |a*x+b|<δ}≤ENNReal.ofReal (4*δ) := by
  let S := {x : ℝ | |a*x+b|<δ}
  by_cases hs : S.Nonempty
  · obtain ⟨x0,hx0⟩ := hs
    have hsub : S⊆Icc (x0-2*δ) (x0+2*δ) := by
      intro x hx
      have hh : |a| * |x-x0|<2*δ := by
        calc
          _ = |(a*x+b)-(a*x0+b)| := by rw [show (a*x+b)-(a*x0+b)=a*(x-x0) by ring,abs_mul]
          _ ≤ |a*x+b|+|a*x0+b| := abs_sub _ _
          _ < _ := by
            change |a*x+b|<δ at hx
            change |a*x0+b|<δ at hx0
            linarith
      have hd : |x-x0|≤2*δ := (le_mul_of_one_le_left (abs_nonneg _) ha).trans hh.le
      obtain ⟨hlo,hhi⟩ := abs_le.mp hd
      constructor <;> linarith
    apply (measure_mono hsub).trans_eq
    rw [Real.volume_Icc]
    congr 1
    ring
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    change volume S≤_
    rw [he,measure_empty]
    exact bot_le

/-- Fubini converts uniform vertical slice bounds and a horizontal range
into an explicit planar-area estimate. -/
theorem planar_vertical_slice_bound (S : Set (ℝ×ℝ)) (hS : MeasurableSet S)
    (X C : ℝ) (_hX : 0≤X) (hC : 0≤C)
    (hx : ∀ p∈S,|p.1|≤X)
    (hs : ∀ x : ℝ,volume {y : ℝ | (x,y)∈S}≤ENNReal.ofReal C) :
    volume S≤ENNReal.ofReal (2*X*C) := by
  change (volume.prod volume) S≤_
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ x : ℝ,(Icc (-X) X).indicator (fun _ => ENNReal.ofReal C) x := by
      apply lintegral_mono
      intro x
      by_cases hxx : x∈Icc (-X) X
      · rw [indicator_of_mem hxx]
        exact hs x
      · rw [indicator_of_notMem hxx]
        have hz : Prod.mk x ⁻¹' S=∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hxx (abs_le.mp (hx (x,y) hy))
        change volume (Prod.mk x ⁻¹' S) ≤ 0
        rw [hz,measure_empty]
    _ = _ := by
      rw [lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,
        Real.volume_Icc,← ENNReal.ofReal_mul hC]
      congr 1
      ring

/-- Transfer the vertical-slice estimate from product coordinates to the
actual complex plane with its volume normalization. -/
theorem complex_vertical_slice_bound (S : Set ℂ) (hS : MeasurableSet S)
    (X C : ℝ) (hX : 0≤X) (hC : 0≤C)
    (hx : ∀ z∈S,|z.re|≤X)
    (hs : ∀ x : ℝ,volume {y : ℝ | (⟨x,y⟩ : ℂ)∈S}≤ENNReal.ofReal C) :
    volume S≤ENNReal.ofReal (2*X*C) := by
  let T := Complex.measurableEquivRealProd.symm ⁻¹' S
  have hT : MeasurableSet T := Complex.measurableEquivRealProd.symm.measurable hS
  have hv : volume T=volume S :=
    (MeasurePreserving.symm Complex.measurableEquivRealProd
      Complex.volume_preserving_equiv_real_prod).measure_preimage_equiv S
  rw [← hv]
  exact planar_vertical_slice_bound T hT X C hX hC (fun p hp => hx _ hp) hs

/-- The quadratic reflection numerator has uniformly small area above Y.
Only the integer-sized leading coefficient and a horizontal range are needed. -/
theorem reflected_quadratic_area (a b c d X Y δ : ℝ) (hc : 1≤|c|)
    (hX : 0≤X) (hY : 0<Y) (hδ : 0≤δ) :
    volume {z : ℂ | |z.re|≤X ∧ Y≤z.im ∧
      |-c*(z.re^2+z.im^2)+(a+d)*z.re-b|<δ}≤ENNReal.ofReal (4*X*δ/Y) := by
  have hm : MeasurableSet {z : ℂ | |z.re|≤X ∧ Y≤z.im ∧
      |-c*(z.re^2+z.im^2)+(a+d)*z.re-b|<δ} := by measurability
  have hh := complex_vertical_slice_bound _ hm X (2*δ/Y) hX (by positivity)
    (fun z hz => hz.1) (by
      intro x
      apply (measure_mono (show {y : ℝ | |x|≤X ∧ Y≤y ∧
          |-c*(x^2+y^2)+(a+d)*x-b|<δ}⊆
          {y : ℝ | Y≤y ∧ |(-c*x^2+(a+d)*x-b)-c*y^2|<δ} from ?_)).trans
        (quadratic_height_slice_volume _ c Y δ hc hY hδ)
      intro y hy
      refine ⟨hy.2.1,?_⟩
      have he : (-c*x^2+(a+d)*x-b)-c*y^2 = -c*(x^2+y^2)+(a+d)*x-b := by ring
      rw [he]
      exact hy.2.2)
  convert hh using 1
  congr 1
  ring

/-- Fubini converts uniform horizontal slice bounds and a vertical range
into an explicit planar-area estimate. -/
theorem planar_horizontal_slice_bound (S : Set (ℝ×ℝ)) (hS : MeasurableSet S)
    (Z C : ℝ) (_hZ : 0≤Z) (hC : 0≤C)
    (hx : ∀ p∈S,|p.2|≤Z)
    (hs : ∀ y : ℝ,volume {x : ℝ | (x,y)∈S}≤ENNReal.ofReal C) :
    volume S≤ENNReal.ofReal (2*Z*C) := by
  change (volume.prod volume) S≤_
  rw [Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ x : ℝ,(Icc (-Z) Z).indicator (fun _ => ENNReal.ofReal C) x := by
      apply lintegral_mono
      intro x
      by_cases hxx : x∈Icc (-Z) Z
      · rw [indicator_of_mem hxx]
        exact hs x
      · rw [indicator_of_notMem hxx]
        have hz : (fun y : ℝ => (y,x)) ⁻¹' S=∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hxx (abs_le.mp (hx (y,x) hy))
        change volume ((fun y : ℝ => (y,x)) ⁻¹' S) ≤ 0
        rw [hz,measure_empty]
    _ = _ := by
      rw [lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,
        Real.volume_Icc,← ENNReal.ofReal_mul hC]
      congr 1
      ring

/-- Transfer the horizontal-slice estimate from product coordinates to the
actual complex plane with its volume normalization. -/
theorem complex_horizontal_slice_bound (S : Set ℂ) (hS : MeasurableSet S)
    (Z C : ℝ) (hZ : 0≤Z) (hC : 0≤C)
    (hx : ∀ z∈S,|z.im|≤Z)
    (hs : ∀ y : ℝ,volume {x : ℝ | (⟨x,y⟩ : ℂ)∈S}≤ENNReal.ofReal C) :
    volume S≤ENNReal.ofReal (2*Z*C) := by
  let T := Complex.measurableEquivRealProd.symm ⁻¹' S
  have hT : MeasurableSet T := Complex.measurableEquivRealProd.symm.measurable hS
  have hv : volume T=volume S :=
    (MeasurePreserving.symm Complex.measurableEquivRealProd
      Complex.volume_preserving_equiv_real_prod).measure_preimage_equiv S
  rw [← hv]
  exact planar_horizontal_slice_bound T hT Z C hZ hC (fun p hp => hx _ hp) hs

/-- The affine reflection case is controlled by horizontal slices. -/
theorem reflected_affine_area (a b Z δ : ℝ) (ha : 1≤|a|)
    (hZ : 0≤Z) (hδ : 0≤δ) :
    volume {z : ℂ | |z.im|≤Z ∧ |a*z.re-b|<δ}≤ENNReal.ofReal (8*Z*δ) := by
  have hm : MeasurableSet {z : ℂ | |z.im|≤Z ∧ |a*z.re-b|<δ} := by measurability
  have hh := complex_horizontal_slice_bound _ hm Z (4*δ) hZ (by positivity)
    (fun z hz => hz.1) (by
      intro y
      apply (measure_mono (show {x : ℝ | |y|≤Z ∧ |a*x-b|<δ}⊆
          {x : ℝ | |a*x+(-b)|<δ} from ?_)).trans (affine_slice_volume a (-b) δ ha hδ)
      intro x hx
      change |a*x+(-b)|<δ
      simpa only [sub_eq_add_neg] using hx.2)
  convert hh using 1
  congr 1
  ring

/-- Both reflection cases, with an explicit bound independent of the
matrix entries and valid for every positive sublevel width. -/
theorem reflected_integral_numerator_area (a b c d : ℤ) (hdet : a*d-b*c=1)
    (X Y Z δ : ℝ) (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hδ : 0≤δ) :
    volume {z : ℂ | |z.re|≤X ∧ Y≤z.im ∧ |z.im|≤Z ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<δ}≤
      ENNReal.ofReal ((4*X/Y+8*Z)*δ) := by
  by_cases hc : c=0
  · have had : (a:ℝ)*(d:ℝ)=1 := by exact_mod_cast (by simpa [hc] using hdet : a*d=1)
    have hsum : 1≤|(a:ℝ)+(d:ℝ)| := by
      have hs := sq_nonneg ((a:ℝ)-(d:ℝ))
      have he := sq_abs ((a:ℝ)+(d:ℝ))
      nlinarith [abs_nonneg ((a:ℝ)+(d:ℝ))]
    apply (measure_mono (show _⊆{z : ℂ | |z.im|≤Z ∧ |((a:ℝ)+d)*z.re-b|<δ} from ?_)).trans
      ((reflected_affine_area (a+d) b Z δ hsum hZ hδ).trans ?_)
    · intro z hz
      exact ⟨hz.2.2.1,by simpa [hc] using hz.2.2.2⟩
    · apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg (div_nonneg (by positivity : 0≤4*X) hY.le) hδ]
  · have hc1 : 1≤|(c:ℝ)| := by
      have hi : (1:ℤ)≤|c| := by have hp := abs_pos.mpr hc; omega
      exact_mod_cast hi
    apply (measure_mono (show _⊆{z : ℂ | |z.re|≤X ∧ Y≤z.im ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<δ} from ?_)).trans
      ((reflected_quadratic_area a b c d X Y δ hc1 hX hY hδ).trans ?_)
    · intro z hz
      exact ⟨hz.1,hz.2.1,hz.2.2.2⟩
    · apply ENNReal.ofReal_le_ofReal
      have he : 4*X*δ/Y = (4*X/Y)*δ := by ring
      rw [he]
      nlinarith [mul_nonneg hZ hδ]

#print axioms planar_horizontal_slice_bound
#print axioms complex_horizontal_slice_bound
#print axioms reflected_affine_area
#print axioms reflected_integral_numerator_area

#print axioms quadratic_height_slice_volume
#print axioms affine_slice_volume
#print axioms planar_vertical_slice_bound
#print axioms complex_vertical_slice_bound
#print axioms reflected_quadratic_area

end QuantitativeMaass
