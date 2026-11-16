module

public import QuantitativeMaassBranchIdentityCoefficientV1
public import QuantitativeMaassCylinderFiniteBranchV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

private theorem cutoff_branch_integral (S B : Set ℍ) (hS : MeasurableSet S)
    (hSB : S⊆B) (a u : ℍ→ℂ) :
    (∫ x in B,(S.indicator a x*u x).re)=∫ x in S,(a x*u x).re := by
  have he : (fun x => (S.indicator a x*u x).re)=S.indicator (fun x => (a x*u x).re) := by
    funext x
    classical
    by_cases hx : x∈S <;> simp [hx]
  rw [he,integral_indicator hS,Measure.restrict_restrict hS,inter_eq_left.mpr hSB]

/-- The uniform geometric estimate now applies to an actual rational
finite-expression branch, and its main term is the actual regular diagonal.
The matrix representative, input-strip indicator and localization are retained. -/
theorem concrete_branch_window_regular_error (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (b : Branch) (M : IntegerMatrix2)
      (_hM : IntegerAction b.label M) (_hpos : 0<M.det)
      (S : Set ℍ) (_hS : MeasurableSet S) (L R ε t : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t → S⊆Metric.closedBall o L →
      (∀ᵐ z ∂volume.restrict S,z∈strip) →
      |(∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
        (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•x)).re)-
        (∫ x in S,(matrix (regular b x) 1 1*
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re)|≤
        (b.bound*(integralMatrixHeight M)^40)*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_branch_uniform_height K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro b M hM hpos S hS L R ε t hR hL hε hε1 ht hSB hstrip
  let a := S.indicator (cylinderInputBranchCoefficient b)
  have ha : Measurable a := (cylinderInputBranchCoefficient_measurable b).indicator hS
  have hba (z : ℍ) : ‖a z‖≤b.bound :=
    (norm_indicator_le_norm_self _ z).trans (cylinderInputBranchCoefficient_bound b z)
  have hh := hbound M hpos L R ε t hR hL hε hε1 ht a b.bound b.bound_nonneg
    ha.aestronglyMeasurable (Eventually.of_forall hba)
  have hact (x : ℍ) : positiveIntegralGL M hpos•x=b.label•x := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional,hM.2]
  change |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
      (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (positiveIntegralGL M hpos•x)).re)-
    (∫ x in Metric.closedBall o L,(a x*(if integralIdentityCoset 0 M then
      windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) else 0)).re)|≤_ at hh
  simp only [hact] at hh
  rw [cutoff_branch_integral S _ hS hSB,cutoff_branch_integral S _ hS hSB] at hh
  have hmain : (∫ x in S,(cylinderInputBranchCoefficient b x*(if integralIdentityCoset 0 M then
      windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) else 0)).re)=
    ∫ x in S,(matrix (regular b x) 1 1*
      windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re := by
    apply integral_congr_ae
    filter_upwards [hstrip] with x hx
    exact congrArg Complex.re (cylinder_branch_identity_coefficient b M hM hpos x hx _)
  rw [hmain] at hh
  exact hh

/-- A concrete radius for every compact input rectangle. Its coarse
power dependence is sufficient for the doubly exponential branch schedule. -/
theorem upperRectangle_subset_explicit_ball {a : ℝ} (ha : 0<a) (b : ℝ) :
    upperRectangle 0 1 a b⊆Metric.closedBall I ((b+2)/Real.sqrt a) := by
  intro z hz
  apply Metric.mem_closedBall.mpr
  have hn : ‖(z:ℂ)‖≤1+b := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,abs_of_nonneg hz.1.1,
      abs_of_pos z.im_pos] at hh
    linarith [hz.1.2,hz.2.2]
  have hd : dist (z:ℂ) (I:ℍ)≤b+2 := by
    rw [dist_eq_norm]
    have hh := norm_sub_le (z:ℂ) ((I:ℍ):ℂ)
    norm_num at hh
    change ‖(z:ℂ)-Complex.I‖≤b+2
    linarith
  have hsq : Real.sqrt a≤Real.sqrt z.im := Real.sqrt_le_sqrt hz.2.1
  have hbp : 0≤b+2 := by linarith [hz.2.2,z.im_pos]
  have hh := dist_le_dist_coe_div_sqrt z I
  simp only [I_im,mul_one] at hh
  exact hh.trans ((div_le_div_of_nonneg_right hd (Real.sqrt_nonneg _)).trans
    (div_le_div_of_nonneg_left hbp (Real.sqrt_pos.mpr ha) hsq))

#print axioms concrete_branch_window_regular_error
#print axioms upperRectangle_subset_explicit_ball
end QuantitativeMaass
