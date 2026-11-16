module

public import QuantitativeMaassAbelOffDiagonalTimeV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The positive singular weight in the physical Abel time formula. -/
def abelSingularWeight (d u : ℝ) : ℝ := (abelRadiusTimeCoordinate d u)⁻¹

theorem cosh_sub_lower_linear (d u : ℝ) (hd : 0≤d) (hu : d≤u) :
    Real.sinh d*(u-d)≤Real.cosh u-Real.cosh d := by
  have h := Real.cosh_add d (u-d)
  rw [add_sub_cancel] at h
  have hc := Real.one_le_cosh (u-d)
  have hs := Real.self_le_sinh_iff.mpr (sub_nonneg.mpr hu)
  have hcd := Real.cosh_pos d
  have hsd := Real.sinh_nonneg_iff.mpr hd
  nlinarith [mul_nonneg hcd.le (sub_nonneg.mpr hc),
    mul_nonneg hsd (sub_nonneg.mpr hs)]

theorem abelSingularWeight_pos (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    0<abelSingularWeight d u := inv_pos.mpr (abelRadiusTimeCoordinate_pos d u hd hu)

theorem abelSingularWeight_le_linear (d u : ℝ) (hd : 0<d) (hu : d<u) :
    abelSingularWeight d u≤(Real.sqrt (Real.sinh d*(u-d)))⁻¹ := by
  apply inv_anti₀ (Real.sqrt_pos.mpr
    (mul_pos (Real.sinh_pos_iff.mpr hd) (sub_pos.mpr hu)))
  exact Real.sqrt_le_sqrt (cosh_sub_lower_linear d u hd.le hu.le)

theorem abelSingularWeight_hasDerivAt (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    HasDerivAt (abelSingularWeight d)
      (-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)) u := by
  have h := (abelRadiusTimeCoordinate_hasDerivAt d u hd hu).inv
    (abelRadiusTimeCoordinate_pos d u hd hu).ne'
  convert h using 1 <;> first | rfl | field_simp

theorem abelSingularWeight_continuousOn (d : ℝ) (hd : 0≤d) :
    ContinuousOn (abelSingularWeight d) (Ioi d) :=
  fun u hu => (abelSingularWeight_hasDerivAt d u hd hu).continuousAt.continuousWithinAt

theorem abelSingularWeight_derivative_continuousOn (d : ℝ) (hd : 0≤d) :
    ContinuousOn (fun u => -Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)) (Ioi d) := by
  apply ContinuousOn.div (Real.continuous_sinh.neg.continuousOn)
  · exact continuousOn_const.mul
      ((Real.continuous_sqrt.comp (Real.continuous_cosh.sub continuous_const)).continuousOn.pow 3)
  · intro u hu
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (abelRadiusTimeCoordinate_pos d u hd hu).ne')

theorem abelSingularWeight_antitoneOn (d : ℝ) (hd : 0≤d) :
    AntitoneOn (abelSingularWeight d) (Ioi d) := by
  intro u hu v hv huv
  apply inv_anti₀ (abelRadiusTimeCoordinate_pos d u hd hu)
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_right
  apply Real.cosh_le_cosh.mpr
  simpa only [abs_of_pos (lt_of_le_of_lt hd hu),
    abs_of_pos (lt_of_le_of_lt hd hv)] using huv

/-- Exact total variation on every interval separated from the singular
endpoint. This supplies the derivative term in integration by parts. -/
theorem abelSingularWeight_variation (d a b : ℝ) (hd : 0≤d)
    (ha : d<a) (hab : a≤b) :
    (∫ u in a..b,‖-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)‖)=
      abelSingularWeight d a-abelSingularWeight d b := by
  have hsub : uIcc a b⊆Ioi d := by
    rw [uIcc_of_le hab]
    intro u hu
    exact lt_of_lt_of_le ha hu.1
  have hi : IntervalIntegrable (fun u => -Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)) volume a b :=
    ((abelSingularWeight_derivative_continuousOn d hd).mono hsub).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => abelSingularWeight_hasDerivAt d u hd (hsub hu)) hi
  have heq : (∫ u in a..b,‖-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)‖)=
      -(∫ u in a..b,-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [Real.norm_eq_abs,abs_of_nonpos]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.sinh_nonneg_iff.mpr (hd.trans (hsub hu).le)))
      (mul_nonneg (by norm_num) (pow_nonneg (abelRadiusTimeCoordinate_pos d u hd (hsub hu)).le _))
  rw [heq,hftc]
  ring

/-- A quantitative integration-by-parts bound for a complex amplitude.
The derivative and its integral are supplied explicitly, so this is reusable
for the actual Abel weight and for smooth time-profile amplitudes. -/
theorem oscillatory_interval_variation_bound (g g' : ℝ → ℂ) (a b t : ℝ)
    (hab : a≤b) (ht : t≠0)
    (hg : ∀ u∈uIcc a b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume a b) :
    ‖∫ u in a..b,Complex.exp ((t*u:ℝ)*Complex.I)*g u‖≤
      (‖g a‖+‖g b‖+∫ u in a..b,‖g' u‖)/|t| := by
  let e : ℝ → ℂ := fun u => Complex.exp ((t*u:ℝ)*Complex.I)
  have he (u : ℝ) : HasDerivAt e (e u*((t:ℂ)*Complex.I)) u := by
    simpa only [e,id_eq,mul_one] using ((((hasDerivAt_id u).const_mul t).ofReal_comp).mul_const Complex.I).cexp
  have hen (u : ℝ) : ‖e u‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hec : Continuous e := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg
    (fun u _ => he u) hgi ((hec.mul continuous_const).intervalIntegrable a b)
  have hleft : (∫ u in a..b,g u*(e u*((t:ℂ)*Complex.I)))=
      ((t:ℂ)*Complex.I)*(∫ u in a..b,e u*g u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [hleft] at hparts
  have hbound : ‖((t:ℂ)*Complex.I)*(∫ u in a..b,e u*g u)‖≤
      ‖g a‖+‖g b‖+∫ u in a..b,‖g' u‖ := by
    rw [hparts]
    calc
      _ ≤ ‖g b*e b-g a*e a‖+‖∫ u in a..b,g' u*e u‖ := norm_sub_le _ _
      _ ≤ (‖g b*e b‖+‖g a*e a‖)+∫ u in a..b,‖g' u*e u‖ :=
        add_le_add (norm_sub_le _ _) (intervalIntegral.norm_integral_le_integral_norm hab)
      _ = _ := by simp only [norm_mul,hen,mul_one]; ring
  have hnorm : ‖((t:ℂ)*Complex.I)*(∫ u in a..b,e u*g u)‖=
      |t| *‖∫ u in a..b,e u*g u‖ := by
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm] at hbound
  apply (le_div_iff₀ (abs_pos.mpr ht)).mpr
  simpa only [e,mul_comm] using hbound

/-- The actual singular Abel weight has an explicit oscillatory tail bound.
The bound is uniform in the upper endpoint and keeps the separation a-d visible. -/
theorem abelSingularWeight_oscillatory_tail (d a b t : ℝ) (hd : 0≤d)
    (ha : d<a) (hab : a≤b) (ht : t≠0) :
    ‖∫ u in a..b,Complex.exp ((t*u:ℝ)*Complex.I)*(abelSingularWeight d u:ℂ)‖≤
      2*abelSingularWeight d a/|t| := by
  have hsub : uIcc a b⊆Ioi d := by
    rw [uIcc_of_le hab]
    intro u hu
    exact lt_of_lt_of_le ha hu.1
  have hi : IntervalIntegrable (fun u => ((-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3):ℝ):ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp_continuousOn
    ((abelSingularWeight_derivative_continuousOn d hd).mono hsub)).intervalIntegrable
  have h := oscillatory_interval_variation_bound
    (fun u => (abelSingularWeight d u:ℂ))
    (fun u => (-Real.sinh u/(2*(abelRadiusTimeCoordinate d u)^3):ℝ))
    a b t hab ht
    (fun u hu => (abelSingularWeight_hasDerivAt d u hd (hsub hu)).ofReal_comp) hi
  simp_rw [Complex.norm_real,← Real.norm_eq_abs] at h
  rw [Real.norm_of_nonneg (abelSingularWeight_pos d a hd ha).le,
    Real.norm_of_nonneg (abelSingularWeight_pos d b hd (lt_of_lt_of_le ha hab)).le,
    abelSingularWeight_variation d a b hd ha hab,Real.norm_eq_abs] at h
  convert h using 1
  ring

#print axioms abelSingularWeight_oscillatory_tail

#print axioms cosh_sub_lower_linear
#print axioms abelSingularWeight_pos
#print axioms abelSingularWeight_le_linear
#print axioms abelSingularWeight_hasDerivAt
#print axioms abelSingularWeight_continuousOn
#print axioms abelSingularWeight_derivative_continuousOn
#print axioms abelSingularWeight_antitoneOn
#print axioms abelSingularWeight_variation
#print axioms oscillatory_interval_variation_bound

end QuantitativeMaass
