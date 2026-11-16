module

public import QuantitativeMaassMonotoneAmplitudeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The first reciprocal hyperbolic weight arising in radial differentiation. -/
def reciprocalSinh (u : ℝ) : ℝ := (Real.sinh u)⁻¹

/-- Minus the derivative of the reciprocal sinh weight. -/
def reciprocalSinhSlope (u : ℝ) : ℝ := Real.cosh u/(Real.sinh u)^2

theorem reciprocalSinh_hasDerivAt (u : ℝ) (hu : 0<u) :
    HasDerivAt reciprocalSinh (-reciprocalSinhSlope u) u := by
  have hh := (Real.hasDerivAt_sinh u).inv (Real.sinh_pos_iff.mpr hu).ne'
  change HasDerivAt reciprocalSinh (-Real.cosh u/(Real.sinh u)^2) u at hh
  have he : -reciprocalSinhSlope u = -Real.cosh u/(Real.sinh u)^2 := by
    unfold reciprocalSinhSlope
    ring
  rw [he]
  exact hh

theorem reciprocalSinhSlope_hasDerivAt (u : ℝ) (hu : 0<u) :
    HasDerivAt reciprocalSinhSlope (-((Real.cosh u)^2+1)/(Real.sinh u)^3) u := by
  have hs : Real.sinh u≠0 := (Real.sinh_pos_iff.mpr hu).ne'
  have hh := (Real.hasDerivAt_cosh u).div ((Real.hasDerivAt_sinh u).pow 2) (pow_ne_zero _ hs)
  change HasDerivAt reciprocalSinhSlope
    ((Real.sinh u*(Real.sinh u)^2-Real.cosh u*(2*(Real.sinh u)^1*Real.cosh u))/((Real.sinh u)^2)^2) u at hh
  have he : (Real.sinh u*(Real.sinh u)^2-Real.cosh u*(2*(Real.sinh u)^1*Real.cosh u))/((Real.sinh u)^2)^2 =
      -((Real.cosh u)^2+1)/(Real.sinh u)^3 := by
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  rw [he] at hh
  exact hh

theorem reciprocalSinh_nonneg (u : ℝ) (hu : 0<u) : 0≤reciprocalSinh u := by
  exact inv_nonneg.mpr (Real.sinh_pos_iff.mpr hu).le

theorem reciprocalSinhSlope_nonneg (u : ℝ) : 0≤reciprocalSinhSlope u :=
  div_nonneg (Real.cosh_pos u).le (sq_nonneg _)

theorem reciprocalSinh_antitone : AntitoneOn reciprocalSinh (Ioi (0:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0:ℝ))
    (fun u hu => (reciprocalSinh_hasDerivAt u hu).continuousAt.continuousWithinAt)
  · intro u hu
    exact (reciprocalSinh_hasDerivAt u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(reciprocalSinh_hasDerivAt u (interior_subset hu)).deriv]
    exact neg_nonpos.mpr (reciprocalSinhSlope_nonneg u)

theorem reciprocalSinhSlope_antitone : AntitoneOn reciprocalSinhSlope (Ioi (0:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0:ℝ))
    (fun u hu => (reciprocalSinhSlope_hasDerivAt u hu).continuousAt.continuousWithinAt)
  · intro u hu
    exact (reciprocalSinhSlope_hasDerivAt u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hp := Real.sinh_pos_iff.mpr (interior_subset hu : 0<u)
    rw [(reciprocalSinhSlope_hasDerivAt u (interior_subset hu)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (Real.cosh u)]) (by positivity)

/-- A reciprocal sinh factor costs only 1/sinh(d) in the oscillatory estimate. -/
theorem abelSingularWeight_reciprocalSinh_decay
    (g g' : ℝ → ℂ) (d b t M M1 : ℝ)
    (hd : 0<d) (hdb : d≤b) (ht : t≠0) (hM : 0≤M) (hM1 : 0≤M1)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤M) (hg1 : ∀ u∈Icc d b,‖g' u‖≤M1) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(reciprocalSinh u:ℂ))*(abelSingularWeight d u:ℂ)‖≤
      ((5*M+M1*(b-d))*reciprocalSinh d)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have hpos (u : ℝ) (hu : u∈uIcc d b) : 0<u := by
    rw [uIcc_of_le hdb] at hu
    exact hd.trans_le hu.1
  apply abelSingularWeight_decreasing_amplitude_decay g g' reciprocalSinh
    (fun u => -reciprocalSinhSlope u) d b t M M1 hd hdb ht hM hM1 hgm
    (by unfold reciprocalSinh;fun_prop) hg
    (fun u hu => reciprocalSinh_hasDerivAt u (hpos u hu))
    hgi
  · apply ContinuousOn.intervalIntegrable
    exact fun u hu => (reciprocalSinhSlope_hasDerivAt u (hpos u hu)).continuousAt.neg.continuousWithinAt
  · exact hg0
  · exact hg1
  · intro u hu
    exact ⟨reciprocalSinh_nonneg u (hd.trans_le hu.1),
      reciprocalSinh_antitone hd (hd.trans_le hu.1) hu.1⟩
  · intro u _
    exact neg_nonpos.mpr (reciprocalSinhSlope_nonneg u)

/-- The second hyperbolic weight costs cosh(d)/sinh(d)^2, without an extra
inverse distance from its derivative. -/
theorem abelSingularWeight_reciprocalSinhSlope_decay
    (g g' : ℝ → ℂ) (d b t M M1 : ℝ)
    (hd : 0<d) (hdb : d≤b) (ht : t≠0) (hM : 0≤M) (hM1 : 0≤M1)
    (hgm : Measurable g) (hg : ∀ u∈uIcc d b,HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' volume d b)
    (hg0 : ∀ u∈Icc d b,‖g u‖≤M) (hg1 : ∀ u∈Icc d b,‖g' u‖≤M1) :
    ‖∫ u in d..b,Complex.exp ((t*u:ℝ)*Complex.I)*(g u*(reciprocalSinhSlope u:ℂ))*(abelSingularWeight d u:ℂ)‖≤
      ((5*M+M1*(b-d))*reciprocalSinhSlope d)/(Real.sqrt |t| *Real.sqrt (Real.sinh d)) := by
  have hpos (u : ℝ) (hu : u∈uIcc d b) : 0<u := by
    rw [uIcc_of_le hdb] at hu
    exact hd.trans_le hu.1
  apply abelSingularWeight_decreasing_amplitude_decay g g' reciprocalSinhSlope
    (fun u => -((Real.cosh u)^2+1)/(Real.sinh u)^3) d b t M M1 hd hdb ht hM hM1 hgm
    (by unfold reciprocalSinhSlope;fun_prop) hg
    (fun u hu => reciprocalSinhSlope_hasDerivAt u (hpos u hu)) hgi
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact pow_ne_zero _ (Real.sinh_pos_iff.mpr (hpos u hu)).ne'
  · exact hg0
  · exact hg1
  · intro u hu
    exact ⟨reciprocalSinhSlope_nonneg u,
      reciprocalSinhSlope_antitone hd (hd.trans_le hu.1) hu.1⟩
  · intro u hu
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (Real.cosh u)])
      (pow_nonneg (Real.sinh_pos_iff.mpr (hd.trans_le hu.1)).le _)

#print axioms reciprocalSinh_hasDerivAt
#print axioms reciprocalSinhSlope_hasDerivAt
#print axioms reciprocalSinh_nonneg
#print axioms reciprocalSinhSlope_nonneg
#print axioms reciprocalSinh_antitone
#print axioms reciprocalSinhSlope_antitone
#print axioms abelSingularWeight_reciprocalSinh_decay
#print axioms abelSingularWeight_reciprocalSinhSlope_decay

end QuantitativeMaass
