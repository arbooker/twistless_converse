module

public import QuantitativeMaassCylinderGrowingBranchV1
public import QuantitativeMaassCombinedFilterGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- The actual compact cylinder branch trace minus its identity-coset term. -/
def cylinderWindowBranchRemainder (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (o : ℍ) (L R : ℝ) (hR : 0<R) (ε t : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (a : ℍ→ℂ) : ℝ :=
  (∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
    (windowSquareProfile K hc R hR ε t) x (positiveIntegralGL M hM • x)).re)-
  (∫ x in Metric.closedBall o L,(a x*(if integralIdentityCoset 0 M then
    windowIdentityContribution K hc R hR (t-ε) (t+ε) else 0)).re)

/-- The uniform branch estimate has a polynomial entry-height cost.
The constants are chosen before the branch and its bounded coefficient. -/
theorem cylinder_window_branch_uniform_height (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      ∀ (a : ℍ→ℂ) (A : ℝ),0≤A →
      AEStronglyMeasurable a (volume.restrict (Metric.closedBall o L)) →
      (∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) →
      |cylinderWindowBranchRemainder K hc o L R (lt_of_lt_of_le zero_lt_one hR) ε t M hM a|≤
        (A*(integralMatrixHeight M)^40)*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_branch_uniform_exp K he hc o
  obtain ⟨J,hJ,hheight⟩ := correspondence_height_cost o
  refine ⟨U,C*J,hU,mul_pos hC hJ,?_⟩
  intro M hM L R ε t hR hL hε hε1 ht a A hA ha haB
  have hb := hbound M hM L R ε t hR hL hε hε1 ht a A hA ha haB
  have hh := hheight M hM _ (integralMatrixHeight_bounds M).1 (integralMatrixHeight_bounds M).2
  apply hb.trans
  calc
    _ = (A*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L))*
        Real.exp (10*(dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))) := by
      rw [show Real.exp (U*R+30*L+10*dist (positiveIntegralGL M hM • o) o+
        20*Real.log (2*integralMatrixHeight M))=Real.exp (U*R+30*L)*
          Real.exp (10*(dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))) by
        rw [←Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ (A*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L))*(J*(integralMatrixHeight M)^40) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- Finite branch sums keep the sum of coefficient bounds times matrix
height costs. The number of branches is unrestricted and no fixed-degree
limit is taken. Coefficients need only be measurable and bounded. -/
theorem cylinder_window_finite_branch_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ {ι : Type*} (s : Finset ι)
      (M : ι→Matrix (Fin 2) (Fin 2) ℤ) (hM : ∀ j,0<(M j).det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      ∀ (a : ι→ℍ→ℂ) (A : ι→ℝ),
      (∀ j∈s,0≤A j) →
      (∀ j∈s,AEStronglyMeasurable (a j) (volume.restrict (Metric.closedBall o L))) →
      (∀ j∈s,∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a j x‖≤A j) →
      |∑ j∈s,cylinderWindowBranchRemainder K hc o L R
        (lt_of_lt_of_le zero_lt_one hR) ε t (M j) (hM j) (a j)|≤
        (∑ j∈s,A j*(integralMatrixHeight (M j))^40)*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_branch_uniform_height K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro ι s M hM L R ε t hR hL hε hε1 ht a A hA ha haB
  calc
    _ ≤ ∑ j∈s,|cylinderWindowBranchRemainder K hc o L R
        (lt_of_lt_of_le zero_lt_one hR) ε t (M j) (hM j) (a j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈s,(A j*(integralMatrixHeight (M j))^40)*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) :=
      Finset.sum_le_sum (fun j hj => hbound (M j) (hM j) L R ε t hR hL hε hε1 ht
        (a j) (A j) (hA j hj) (ha j hj) (haB j hj))
    _ = _ := by simp only [Finset.sum_mul]

#print axioms cylinder_window_branch_uniform_height
#print axioms cylinder_window_finite_branch_bound
end QuantitativeMaass
