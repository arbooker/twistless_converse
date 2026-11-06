module

public import AsymptoticFiniteBranchDataV1
public import Mathlib.Algebra.BigOperators.Ring.List

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane ContinuousLinearMap

abbrev Expression := List Branch

noncomputable def holomorphicSum (e : Expression) (m : ℕ) := (e.map (fun b => holomorphic b m)).sum
noncomputable def regularSum (e : Expression) (z : ℍ) := (e.map (fun b => regular b z)).sum

noncomputable def composeExpression (e f : Expression) : Expression :=
  e.flatMap (fun b => f.map (compose b))

noncomputable def adjointExpression (e : Expression) : Expression := e.map adjoint
noncomputable def scaleExpression (a : ℂ) (e : Expression) : Expression := e.map (scale a)

/-- Distributing a finite product produces the same branch list in both
representations, retaining order and every coefficient. -/
theorem sum_composeExpression {R : Type*} [Semiring R] (v : Branch → R)
    (hv : ∀ b c,v (compose b c)=v b*v c) (e f : Expression) :
    ((composeExpression e f).map v).sum=(e.map v).sum*(f.map v).sum := by
  induction e with
  | nil => simp [composeExpression]
  | cons b e ih =>
    simp only [composeExpression,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,hv,List.map_cons,List.sum_cons] at *
    rw [ih,List.sum_map_mul_left,add_mul]

theorem holomorphicSum_append (e f : Expression) (m : ℕ) :
    holomorphicSum (e++f) m=holomorphicSum e m+holomorphicSum f m := by
  simp only [holomorphicSum,List.map_append,List.sum_append]

theorem regularSum_append (e f : Expression) (z : ℍ) :
    regularSum (e++f) z=regularSum e z+regularSum f z := by
  simp only [regularSum,List.map_append,List.sum_append]

theorem holomorphicSum_compose (e f : Expression) (m : ℕ) :
    holomorphicSum (composeExpression e f) m=(holomorphicSum e m).comp (holomorphicSum f m) :=
  sum_composeExpression (fun b => holomorphic b m) (fun b c => holomorphic_compose b c m) e f

theorem regularSum_compose (e f : Expression) (z : ℍ) :
    regularSum (composeExpression e f) z=(regularSum e z).comp (regularSum f z) :=
  sum_composeExpression (fun b => regular b z) (fun b c => regular_compose b c z) e f

theorem holomorphicSum_adjoint (e : Expression) (m : ℕ) :
    holomorphicSum (adjointExpression e) m=(holomorphicSum e m).adjoint := by
  induction e with
  | nil => simp [holomorphicSum,adjointExpression]
  | cons b e ih =>
    simp only [holomorphicSum,adjointExpression,List.map_cons,List.sum_cons] at *
    rw [holomorphic_adjoint,ih,map_add]

theorem regularSum_adjoint (e : Expression) (z : ℍ) :
    regularSum (adjointExpression e) z=(regularSum e z).adjoint := by
  induction e with
  | nil => simp [regularSum,adjointExpression]
  | cons b e ih =>
    change regular (adjoint b) z+regularSum (adjointExpression e) z=
      (regular b z+regularSum e z).adjoint
    exact (congrArg₂ (·+·) (regular_adjoint b z) ih).trans
      (map_add (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := RegularSpace) (F := RegularSpace)) _ _).symm

theorem holomorphicSum_scale (a : ℂ) (e : Expression) (m : ℕ) :
    holomorphicSum (scaleExpression a e) m=a • holomorphicSum e m := by
  induction e with
  | nil =>
    change (0 : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)=a • 0
    exact (smul_zero (A := AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) a).symm
  | cons b e ih =>
    change holomorphic (scale a b) m+holomorphicSum (scaleExpression a e) m=
      a • (holomorphic b m+holomorphicSum e m)
    exact (congrArg₂ (·+·) (holomorphic_scale a b m) ih).trans (smul_add a _ _).symm

theorem regularSum_scale (a : ℂ) (e : Expression) (z : ℍ) :
    regularSum (scaleExpression a e) z=a • regularSum e z := by
  induction e with
  | nil =>
    change (0 : RegularSpace →L[ℂ] RegularSpace)=a • 0
    exact (smul_zero (A := RegularSpace →L[ℂ] RegularSpace) a).symm
  | cons b e ih =>
    change regular (scale a b) z+regularSum (scaleExpression a e) z=
      a • (regular b z+regularSum e z)
    exact (congrArg₂ (·+·) (regular_scale a b z) ih).trans (smul_add a _ _).symm

noncomputable def expressionBound (e : Expression) : ℝ := (e.map Branch.bound).sum

theorem expressionBound_nonneg (e : Expression) : 0≤expressionBound e := by
  induction e with
  | nil => simp [expressionBound]
  | cons b e ih => exact add_nonneg b.bound_nonneg ih

theorem holomorphicSum_norm_le (e : Expression) (m : ℕ) : ‖holomorphicSum e m‖≤expressionBound e := by
  induction e with
  | nil => simp [holomorphicSum,expressionBound]
  | cons b e ih =>
    exact (norm_add_le _ _).trans (add_le_add (holomorphic_norm_le b m) ih)

theorem regularSum_norm_le (e : Expression) (z : ℍ) : ‖regularSum e z‖≤expressionBound e := by
  induction e with
  | nil => simp [regularSum,expressionBound]
  | cons b e ih =>
    exact (norm_add_le _ _).trans (add_le_add (regular_norm_le b z) ih)

#print axioms sum_composeExpression
#print axioms holomorphicSum_compose
#print axioms regularSum_compose
#print axioms holomorphicSum_adjoint
#print axioms regularSum_adjoint
#print axioms holomorphicSum_scale
#print axioms regularSum_scale
#print axioms holomorphicSum_norm_le
#print axioms regularSum_norm_le

end AsymptoticFiniteBranch
