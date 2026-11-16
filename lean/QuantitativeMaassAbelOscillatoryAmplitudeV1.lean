module

public import QuantitativeMaassAbelEndpointEstimateV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Integration by parts for the actual Abel weight times a complex amplitude.
Both amplitude constants are retained explicitly and no upper support radius
or spectral parameter is hidden in the bound. -/
theorem abelSingularWeight_amplitude_tail (g g' : ℝ → ℂ) (d a b t A A1 : ℝ)
    (hd : 0≤d) (ha : d<a) (hab : a≤b) (ht : t≠0) (hA1 : 0≤A1)
    (hg : ∀ u∈uIcc a b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume a b)
    (hg0 : ∀ u∈Icc a b,‖g u‖≤A) (hg1 : ∀ u∈Icc a b,‖g' u‖≤A1) :
    ‖∫ u in a..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      (2*A+A1*(b-a))*abelSingularWeight d a/|t| := by
  let w := abelSingularWeight d
  let w' : ℝ → ℝ := fun u => -Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)
  have hsub : uIcc a b⊆Ioi d := by
    rw [uIcc_of_le hab]
    intro u hu
    exact lt_of_lt_of_le ha hu.1
  have hw : ContinuousOn (fun u => (w u:ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn ((abelSingularWeight_continuousOn d hd).mono hsub)
  have hw' : ContinuousOn w' (uIcc a b) :=
    (abelSingularWeight_derivative_continuousOn d hd).mono hsub
  have hwi : IntervalIntegrable w' volume a b := hw'.intervalIntegrable
  have hwic : IntervalIntegrable (fun u => (w' u:ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp_continuousOn hw').intervalIntegrable
  have hgc : ContinuousOn g (uIcc a b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  let G : ℝ → ℂ := fun u => g u*(w u:ℂ)
  let G' : ℝ → ℂ := fun u => g' u*(w u:ℂ)+g u*(w' u:ℂ)
  have hGi : IntervalIntegrable G' volume a b :=
    (hgi.mul_continuousOn hw).add (hwic.continuousOn_mul hgc)
  have hGD : ∀ u∈uIcc a b,HasDerivAt G (G' u) u := by
    intro u hu
    exact (hg u hu).mul ((abelSingularWeight_hasDerivAt d u hd (hsub hu)).ofReal_comp)
  have hwpos (u : ℝ) (hu : u∈Icc a b) : 0<w u :=
    abelSingularWeight_pos d u hd (lt_of_lt_of_le ha hu.1)
  have hwnorm (u : ℝ) (hu : u∈Icc a b) : ‖(w u:ℂ)‖=w u := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hwpos u hu)]
  have hG0 (u : ℝ) (hu : u∈Icc a b) : ‖G u‖≤A*w u := by
    change ‖g u*(w u:ℂ)‖≤A*w u
    rw [norm_mul,hwnorm u hu]
    exact mul_le_mul_of_nonneg_right (hg0 u hu) (hwpos u hu).le
  have hG1 (u : ℝ) (hu : u∈Icc a b) : ‖G' u‖≤A1*w a+A*‖w' u‖ := by
    have hwa : w u≤w a := abelSingularWeight_antitoneOn d hd ha
      (lt_of_lt_of_le ha hu.1) hu.1
    calc
      _ ≤ ‖g' u*(w u:ℂ)‖+‖g u*(w' u:ℂ)‖ := norm_add_le _ _
      _ = ‖g' u‖*w u+‖g u‖*‖w' u‖ := by
        rw [norm_mul,norm_mul,hwnorm u hu,Complex.norm_real]
      _ ≤ A1*w u+A*‖w' u‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hg1 u hu) (hwpos u hu).le)
        (mul_le_mul_of_nonneg_right (hg0 u hu) (norm_nonneg _))
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hwa hA1) le_rfl
  have hb : IntervalIntegrable (fun u => A1*w a+A*‖w' u‖) volume a b :=
    (intervalIntegrable_const).add (hwi.norm.const_mul A)
  have hI := intervalIntegral.integral_mono_on hab hGi.norm hb hG1
  rw [intervalIntegral.integral_add intervalIntegrable_const (hwi.norm.const_mul A),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    smul_eq_mul] at hI
  have hvar : (∫ u in a..b,‖w' u‖)=w a-w b := abelSingularWeight_variation d a b hd ha hab
  rw [hvar] at hI
  have hh := oscillatory_interval_variation_bound G G' a b t hab ht hGD hGi
  have hbound : (‖G a‖+‖G b‖+∫ u in a..b,‖G' u‖)≤(2*A+A1*(b-a))*w a := by
    have hga := hG0 a ⟨le_rfl,hab⟩
    have hgb := hG0 b ⟨hab,le_rfl⟩
    nlinarith
  have hfinal := hh.trans (div_le_div_of_nonneg_right hbound (abs_nonneg t))
  simpa only [G,w,mul_assoc] using hfinal

/-- A bounded measurable amplitude times the Abel weight is integrable on
an interval including its singular lower endpoint. -/
theorem abelSingularWeight_amplitude_integrable (g : ℝ → ℂ) (d b t A : ℝ)
    (hd : 0<d) (hdb : d≤b) (hg : Measurable g)
    (hbound : ∀ u∈Ioc d b,‖g u‖≤A) :
    IntervalIntegrable (fun u => Complex.exp ((t*u:ℝ)*Complex.I)*g u*
      (abelSingularWeight d u:ℂ)) volume d b := by
  have hi := (abelSingularWeight_intervalIntegrable d b hd hdb).const_mul A
  have hw : Measurable (abelSingularWeight d) := by
    change Measurable (fun u => (Real.sqrt (Real.cosh u-Real.cosh d))⁻¹)
    fun_prop
  have hm : Measurable (fun u => Complex.exp ((t*u:ℝ)*Complex.I)*g u*
      (abelSingularWeight d u:ℂ)) := by fun_prop
  apply hi.mono_fun' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [uIoc_of_le hdb] at hu
  rw [norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (abelSingularWeight_pos d u hd.le hu.1)]
  exact mul_le_mul_of_nonneg_right (hbound u hu) (abelSingularWeight_pos d u hd.le hu.1).le

/-- Quantitative split of the WHOLE singular oscillatory integral into its
initial square-root mass and a tail controlled by integration by parts. -/
theorem abelSingularWeight_amplitude_split (g g' : ℝ → ℂ) (d b h t A A1 : ℝ)
    (hd : 0<d) (hh : 0<h) (hhb : d+h≤b) (ht : t≠0) (hA : 0≤A) (hA1 : 0≤A1)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤A) (hg1 : ∀ u∈Icc d b,‖g' u‖≤A1) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      2*A*Real.sqrt h/Real.sqrt (Real.sinh d)+
        (2*A+A1*(b-d))/ (|t| * Real.sqrt (Real.sinh d)*Real.sqrt h) := by
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
  have htail := abelSingularWeight_amplitude_tail g g' d (d+h) b t A A1 hd.le
    hda hhb ht hA1 (fun u hu => hg u (hsub hu)) (hgi.mono_set hsub)
    (fun u hu => hg0 u (hsub0 hu)) (fun u hu => hg1 u (hsub0 hu))
  have hweight := abelSingularWeight_le_inverse_sqrt d (d+h) hd hda
  rw [add_sub_cancel_left] at hweight
  have hcoeff : 0≤2*A+A1*(b-(d+h)) := by
    exact add_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg hA1 (sub_nonneg.mpr hhb))
  have hlength : 2*A+A1*(b-(d+h))≤2*A+A1*(b-d) := by nlinarith
  have htail' : (2*A+A1*(b-(d+h)))*abelSingularWeight d (d+h)/|t|≤
      (2*A+A1*(b-d))/(|t| * Real.sqrt (Real.sinh d)*Real.sqrt h) := by
    apply (div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hweight hcoeff).trans
        (mul_le_mul_of_nonneg_right hlength (by positivity))) (abs_nonneg t)).trans_eq
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hia hib]
  exact (norm_add_le _ _).trans (add_le_add hnear (htail.trans htail'))

/-- Square-root frequency decay for the complete Abel oscillatory integral,
including its singular endpoint, with explicit amplitude and derivative costs. -/
theorem abelSingularWeight_amplitude_decay (g g' : ℝ → ℂ) (d b t A A1 : ℝ)
    (hd : 0<d) (hdb : d≤b) (ht : t≠0) (hA : 0≤A) (hA1 : 0≤A1)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤A) (hg1 : ∀ u∈Icc d b,‖g' u‖≤A1) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      (4*A+A1*(b-d))/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have ht0 : 0< |t| := abs_pos.mpr ht
  have hst : 0<Real.sqrt |t| := Real.sqrt_pos.mpr ht0
  have hss : 0<Real.sqrt (Real.sinh d) := Real.sqrt_pos.mpr (Real.sinh_pos_iff.mpr hd)
  by_cases hh : d+1/|t|≤b
  · have hs := abelSingularWeight_amplitude_split g g' d b (1/|t|) t A A1 hd
      (one_div_pos.mpr ht0) hh ht hA hA1 hgm hg hgi hg0 hg1
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
        (by nlinarith [mul_nonneg hA1 (sub_nonneg.mpr hdb)]) (by positivity)

#print axioms abelSingularWeight_amplitude_decay

#print axioms abelSingularWeight_amplitude_tail
#print axioms abelSingularWeight_amplitude_integrable
#print axioms abelSingularWeight_amplitude_split

end QuantitativeMaass
