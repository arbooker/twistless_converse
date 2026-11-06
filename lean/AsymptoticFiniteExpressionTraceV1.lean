module

public import AsymptoticFiniteBranchRetainedV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Filter ContinuousLinearMap InnerProductSpace
open AsymptoticRegularTrace AsymptoticUnweightedKernel
open scoped InnerProduct Topology

noncomputable def retainedExpression (Y H : ℝ) (e : Expression) : Expression := e.map (retained Y H)

theorem holomorphicSum_retainedExpression (Y H : ℝ) (e : Expression) (m : ℕ) :
    holomorphicSum (retainedExpression Y H e) m=
      (holomorphic (corner (retainedRegion Y H) (retainedRegion_measurable Y H)) m).comp
        ((holomorphicSum e m).comp
          (holomorphic (corner (retainedRegion Y H) (retainedRegion_measurable Y H)) m)) := by
  induction e with
  | nil => simp [holomorphicSum,retainedExpression]
  | cons b e ih =>
    change holomorphic (retained Y H b) m+holomorphicSum (retainedExpression Y H e) m=_
    rw [holomorphic_retained,ih]
    simp only [holomorphicSum,List.map_cons,List.sum_cons,add_comp,comp_add]

theorem regularSum_retainedExpression (Y H : ℝ) (e : Expression) (z : ℍ) :
    regularSum (retainedExpression Y H e) z=
      (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((regularSum e z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)) := by
  induction e with
  | nil => simp [regularSum,retainedExpression]
  | cons b e ih =>
    change regular (retained Y H b) z+regularSum (retainedExpression Y H e) z=_
    exact (congrArg₂ (·+·) (regular_retained Y H b z) ih).trans (by
      change _=(AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((regular b z+regularSum e z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))
      rw [add_comp,comp_add])

theorem retainedExpression_diagonal_summable (h : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y)
    (H : ℝ) (e : Expression) :
    Summable (fun n => (⟪holomorphicSum (retainedExpression Y H e) (h+1) (liftedMode h n hε),
      liftedMode h n hε⟫_ℂ).re) := by
  induction e with
  | nil => simp [holomorphicSum,retainedExpression]
  | cons b e ih =>
    simpa only [retainedExpression,holomorphicSum,List.map_cons,List.sum_cons,add_apply,
      inner_add_left,Complex.add_re] using (retained_diagonal_summable h hε hY H b).add ih

theorem retainedExpression_root_integrable {Y : ℝ} (hY : 0<Y) (H : ℝ) (e : Expression) :
    Integrable (fun z => (matrix (regularSum (retainedExpression Y H e) z) 1 1).re) volume := by
  induction e with
  | nil => simp [regularSum,retainedExpression,matrix]
  | cons b e ih =>
    have hi : Integrable (fun z => (matrix (regular (retained Y H b) z) 1 1).re+
        (matrix (regularSum (retainedExpression Y H e) z) 1 1).re) volume :=
      (retained_root_integrable hY H b).add ih
    simpa only [regularSum,retainedExpression,List.map_cons,List.sum_cons,matrix,add_apply,
      lp.coeFn_add,Pi.add_apply,Complex.add_re] using hi

theorem retainedExpression_signedTrace_cons {Y : ℝ} (hY : 0<Y) (H : ℝ) (b : Branch) (e : Expression) :
    signedTrace volume (regularSum (retainedExpression Y H (b::e)))=
      signedTrace volume (regular (retained Y H b))+
        signedTrace volume (regularSum (retainedExpression Y H e)) := by
  have hi := integral_add (retained_root_integrable hY H b) (retainedExpression_root_integrable hY H e)
  simpa only [signedTrace,regularSum,retainedExpression,List.map_cons,List.sum_cons,matrix,
    add_apply,lp.coeFn_add,Pi.add_apply,Complex.add_re] using hi

/-- The trace comparison for every finite expression, including arbitrary
products, adjoints and inverse polynomials, after retaining both endpoints.
Summability and integrability are proved, rather than assumed as trace rules. -/
theorem retainedExpression_trace_tendsto {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y)
    (H : ℝ) (e : Expression) :
    Tendsto (fun h => liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h+1))/(2*h+2:ℕ))
      atTop (𝓝 (signedTrace volume (regularSum (retainedExpression Y H e))/(4*Real.pi))) := by
  induction e with
  | nil =>
    simp [retainedExpression,holomorphicSum,regularSum,liftedTrace_eq_sum,signedTrace,matrix]
  | cons b e ih =>
    have he (h : ℕ) :
        liftedTrace h hε (holomorphicSum (retainedExpression Y H (b::e)) (h+1))=
          liftedTrace h hε (holomorphic (retained Y H b) (h+1))+
            liftedTrace h hε (holomorphicSum (retainedExpression Y H e) (h+1)) :=
      liftedTrace_add h hε _ _ (retained_diagonal_summable h hε hY H b)
        (retainedExpression_diagonal_summable h hε hY H e)
    simp only [he,add_div,retainedExpression_signedTrace_cons hY]
    exact (retained_trace_tendsto hε hY H b).add ih

#print axioms holomorphicSum_retainedExpression
#print axioms regularSum_retainedExpression
#print axioms retainedExpression_diagonal_summable
#print axioms retainedExpression_root_integrable
#print axioms retainedExpression_signedTrace_cons
#print axioms retainedExpression_trace_tendsto

end AsymptoticFiniteBranch
