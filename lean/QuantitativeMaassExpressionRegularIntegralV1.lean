module

public import QuantitativeMaassConcreteExpressionWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic ContinuousLinearMap
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

private theorem sum_branch_sub (E : Expression) (f g : Branch→ℝ) :
    (E.map (fun b => f b-g b)).sum=(E.map f).sum-(E.map g).sum := by
  induction E with
  | nil => simp
  | cons b E ih => simp only [List.map_cons,List.sum_cons,ih];ring

/-- Compact regular branch diagonals are integrable for every bounded
measurable coefficient, so finite sums may be integrated term by term. -/
theorem regular_branch_diagonal_integrable (b : Branch) (S : Set ℍ) (hS : IsCompact S)
    (v : ℂ) : Integrable (fun z => (AsymptoticRegularTrace.matrix (regular b z) 1 1*v).re) (volume.restrict S) := by
  classical
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hm (z : ℍ) : AsymptoticRegularTrace.matrix (regular b z) 1 1=if b.label=1 then b.coefficient z else 0 := by
    simp only [regular,AsymptoticOrbitBranch.operator_matrix,mul_one,one_smul]
  simp_rw [hm]
  by_cases hb : b.label=1
  · simp only [ite_eq_left hb]
    apply Integrable.of_bound ((Complex.continuous_re.measurable.comp (b.measurable.mul_const v)).aestronglyMeasurable) (b.bound*‖v‖)
    exact Eventually.of_forall (fun z => (RCLike.norm_re_le_norm _).trans
      ((norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (b.norm_le z) (norm_nonneg _))))
  · simp only [ite_eq_right hb,zero_mul,Complex.zero_re]
    exact integrable_zero _ _ _

theorem regular_expression_diagonal_integrable (E : Expression) (S : Set ℍ) (hS : IsCompact S)
    (v : ℂ) : Integrable (fun z => (AsymptoticRegularTrace.matrix (regularSum E z) 1 1*v).re) (volume.restrict S) := by
  induction E with
  | nil => simpa only [regularSum,List.map_nil,List.sum_nil,AsymptoticRegularTrace.matrix,zero_apply,
      lp.coeFn_zero,Pi.zero_apply,zero_mul,Complex.zero_re] using! (integrable_zero ℍ ℝ (volume.restrict S))
  | cons b E ih =>
    simpa only [regularSum,List.map_cons,List.sum_cons,AsymptoticRegularTrace.matrix,add_apply,
      lp.coeFn_add,Pi.add_apply,add_mul,Complex.add_re] using!
      (regular_branch_diagonal_integrable b S hS v).add ih

theorem regular_expression_diagonal_integral (E : Expression) (S : Set ℍ) (hS : IsCompact S)
    (v : ℂ) :
    (E.map (fun b => ∫ x in S,(AsymptoticRegularTrace.matrix (regular b x) 1 1*v).re)).sum=
      ∫ x in S,(AsymptoticRegularTrace.matrix (regularSum E x) 1 1*v).re := by
  induction E with
  | nil => simp [regularSum,AsymptoticRegularTrace.matrix]
  | cons b E ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    rw [←integral_add (regular_branch_diagonal_integrable b S hS v)
      (regular_expression_diagonal_integrable E S hS v)]
    congr 1
    funext x
    simp only [regularSum,List.map_cons,List.sum_cons,AsymptoticRegularTrace.matrix,add_apply,
      lp.coeFn_add,Pi.add_apply,add_mul,Complex.add_re]

/-- The full physical finite-expression kernel trace is compared to its
actual regular diagonal integral, including all localization indicators. -/
theorem concrete_expression_kernel_regular_comparison (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (E : Expression) (B : ℝ),0≤B →
      ExpressionMatrixBound E B → ∀ (S : Set ℍ) (_hS : IsCompact S)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      S⊆Metric.closedBall o L → (∀ᵐ z ∂volume.restrict S,z∈strip) →
      |(E.map (fun b => ∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•x)).re)).sum-
        (∫ x in S,(AsymptoticRegularTrace.matrix (regularSum E x) 1 1*
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re)|≤
      expressionBound E*(1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := concrete_expression_window_regular_error K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro E B hB hE S hS L R ε t hR hL hε hε1 ht hSB hstrip
  have hh := hbound E B hB hE S hS.measurableSet L R ε t hR hL hε hε1 ht hSB hstrip
  rw [sum_branch_sub,regular_expression_diagonal_integral E S hS] at hh
  exact hh

#print axioms regular_branch_diagonal_integrable
#print axioms regular_expression_diagonal_integrable
#print axioms regular_expression_diagonal_integral
#print axioms concrete_expression_kernel_regular_comparison
end QuantitativeMaass
