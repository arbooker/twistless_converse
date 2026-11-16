module

public import QuantitativeMaassAbelVariationTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Singular endpoint plus integration-by-parts tail, with the literal
integrated amplitude variation retained. -/
theorem abelSingularWeight_variation_split (g g' : ℝ → ℂ) (d b h t A V : ℝ)
    (hd : 0<d) (hh : 0<h) (hhb : d+h≤b) (ht : t≠0) (hA : 0≤A)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤A) (hv : (∫ u in d..b,‖g' u‖)≤V) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      2*A*Real.sqrt h/Real.sqrt (Real.sinh d)+
        (2*A+V)/ (|t| * Real.sqrt (Real.sinh d)*Real.sqrt h) := by
  have hda : d<d+h := by linarith
  have hdb : d≤b := hda.le.trans hhb
  have hsub : uIcc (d+h) b⊆uIcc d b := by
    rw [uIcc_of_le hhb,uIcc_of_le hdb]
    exact Icc_subset_Icc hda.le le_rfl
  have hsub0 : Icc (d+h) b⊆Icc d b := Icc_subset_Icc hda.le le_rfl
  have hi := abelSingularWeight_amplitude_integrable g d b t A hd hdb hgm
    (fun u hu => hg0 u (Ioc_subset_Icc_self hu))
  have hia := hi.mono_set (show uIcc d (d+h)⊆uIcc d b by
    rw [uIcc_of_le hda.le,uIcc_of_le hdb]; exact Icc_subset_Icc le_rfl hhb)
  have hib := hi.mono_set hsub
  have hnear := abelSingularWeight_initial_amplitude g d (d+h) t A hd hda.le hA
    (fun u hu => hg0 u ⟨hu.1.le,hu.2.trans hhb⟩)
  rw [add_sub_cancel_left] at hnear
  have htail := abelSingularWeight_variation_tail g g' d (d+h) b t A hd.le
    hda hhb ht (fun u hu => hg u (hsub hu)) (hgi.mono_set hsub)
    (fun u hu => hg0 u (hsub0 hu))
  have hvar : (∫ u in (d+h)..b,‖g' u‖)≤V :=
    (intervalIntegral.integral_mono_interval hda.le hhb le_rfl
      (Eventually.of_forall (fun _ => norm_nonneg _)) hgi.norm).trans hv
  have hweight := abelSingularWeight_le_inverse_sqrt d (d+h) hd hda
  rw [add_sub_cancel_left] at hweight
  have hcoeff : 0≤2*A+∫ u in (d+h)..b,‖g' u‖ :=
    add_nonneg (mul_nonneg (by norm_num) hA)
      (intervalIntegral.integral_nonneg_of_forall hhb (fun _ => norm_nonneg _))
  have hlength : (2*A+∫ u in (d+h)..b,‖g' u‖)≤2*A+V := by linarith
  have htail' : (2*A+∫ u in (d+h)..b,‖g' u‖)*abelSingularWeight d (d+h)/|t|≤
      (2*A+V)/(|t| * Real.sqrt (Real.sinh d)*Real.sqrt h) := by
    apply (div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hweight hcoeff).trans
        (mul_le_mul_of_nonneg_right hlength (by positivity))) (abs_nonneg t)).trans_eq
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hia hib]
  exact (norm_add_le _ _).trans (add_le_add hnear (htail.trans htail'))

/-- Frequency square-root decay with amplitude supremum and L1 derivative
cost. This remains useful for amplitudes with concentrated derivatives. -/
theorem abelSingularWeight_variation_decay (g g' : ℝ → ℂ) (d b t A V : ℝ)
    (hd : 0<d) (hdb : d≤b) (ht : t≠0) (hA : 0≤A) (hV : 0≤V)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤A) (hv : (∫ u in d..b,‖g' u‖)≤V) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      (4*A+V)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have ht0 : 0< |t| := abs_pos.mpr ht
  have hst : 0<Real.sqrt |t| := Real.sqrt_pos.mpr ht0
  have hss : 0<Real.sqrt (Real.sinh d) := Real.sqrt_pos.mpr (Real.sinh_pos_iff.mpr hd)
  by_cases hh : d+1/|t|≤b
  · have hs := abelSingularWeight_variation_split g g' d b (1/|t|) t A V hd
      (one_div_pos.mpr ht0) hh ht hA hgm hg hgi hg0 hv
    have hcancel : |t| /Real.sqrt |t|=Real.sqrt |t| :=
      (div_eq_iff hst.ne').mpr (Real.mul_self_sqrt ht0.le).symm
    have hden : |t| *Real.sqrt (Real.sinh d)*(Real.sqrt |t|)⁻¹=
        Real.sqrt |t| *Real.sqrt (Real.sinh d) := by
      calc
        _ = (|t| /Real.sqrt |t|)*Real.sqrt (Real.sinh d) := by ring
        _ = _ := by rw [hcancel]
    rw [one_div,Real.sqrt_inv,hden] at hs
    convert hs using 1
    ring
  · have hlen : b-d≤1/|t| := by linarith [lt_of_not_ge hh]
    have hs := abelSingularWeight_initial_amplitude g d b t A hd hdb hA
      (fun u hu => hg0 u (Ioc_subset_Icc_self hu))
    apply hs.trans
    calc
      _ ≤ 2*A*Real.sqrt (1/|t|)/Real.sqrt (Real.sinh d) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlen) (by positivity)) hss.le
      _ = (2*A)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
        rw [one_div,Real.sqrt_inv]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (by linarith) (by positivity)


#print axioms abelSingularWeight_variation_split
#print axioms abelSingularWeight_variation_decay

end QuantitativeMaass
