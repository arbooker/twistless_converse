module

public import QuantitativeMaassAbelOscillatoryAmplitudeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Integration by parts charges the actual total amplitude variation,
not the interval length times its worst derivative. -/
theorem abelSingularWeight_variation_tail (g g' : ℝ → ℂ) (d a b t A : ℝ)
    (hd : 0≤d) (ha : d<a) (hab : a≤b) (ht : t≠0)
    (hg : ∀ u∈uIcc a b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume a b)
    (hg0 : ∀ u∈Icc a b,‖g u‖≤A) :
    ‖∫ u in a..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u*(abelSingularWeight d u:ℂ)‖≤
      (2*A+∫ u in a..b,‖g' u‖)*abelSingularWeight d a/|t| := by
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
  have hG1 (u : ℝ) (hu : u∈Icc a b) : ‖G' u‖≤‖g' u‖*w a+A*‖w' u‖ := by
    have hwa : w u≤w a := abelSingularWeight_antitoneOn d hd ha
      (lt_of_lt_of_le ha hu.1) hu.1
    calc
      _ ≤ ‖g' u*(w u:ℂ)‖+‖g u*(w' u:ℂ)‖ := norm_add_le _ _
      _ = ‖g' u‖*w u+‖g u‖*‖w' u‖ := by
        rw [norm_mul,norm_mul,hwnorm u hu,Complex.norm_real]
      _ ≤ ‖g' u‖*w a+A*‖w' u‖ := add_le_add
        (mul_le_mul_of_nonneg_left hwa (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hg0 u hu) (norm_nonneg _))
  have hb : IntervalIntegrable (fun u => ‖g' u‖*w a+A*‖w' u‖) volume a b :=
    (hgi.norm.mul_const (w a)).add (hwi.norm.const_mul A)
  have hI := intervalIntegral.integral_mono_on hab hGi.norm hb hG1
  rw [intervalIntegral.integral_add (hgi.norm.mul_const (w a)) (hwi.norm.const_mul A),
    intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul] at hI
  have hvar : (∫ u in a..b,‖w' u‖)=w a-w b := abelSingularWeight_variation d a b hd ha hab
  rw [hvar] at hI
  have hh := oscillatory_interval_variation_bound G G' a b t hab ht hGD hGi
  have hbound : (‖G a‖+‖G b‖+∫ u in a..b,‖G' u‖)≤(2*A+∫ u in a..b,‖g' u‖)*w a := by
    have hga := hG0 a ⟨le_rfl,hab⟩
    have hgb := hG0 b ⟨hab,le_rfl⟩
    nlinarith
  have hfinal := hh.trans (div_le_div_of_nonneg_right hbound (abs_nonneg t))
  simpa only [G,w,mul_assoc] using hfinal


#print axioms abelSingularWeight_variation_tail

end QuantitativeMaass
