module

public import AsymptoticFiniteBranchPolynomialV1
public import AsymptoticFiniteBranchSumsV1
public import QuantitativeMaassHeckeL2V1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticFiniteBranch ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass

/-- Literal weight-zero action of a rational branch on functions. -/
def branchFunction (b : Branch) : Module.End ℂ (ℍ→ℂ) where
  toFun f z := b.coefficient z*f (b.label • z)
  map_add' f g := by ext z; exact mul_add _ _ _
  map_smul' c f := by ext z; exact mul_left_comm _ _ _

def expressionFunction (E : Expression) : Module.End ℂ (ℍ→ℂ) :=
  (E.map branchFunction).sum

theorem branchFunction_compose (b c : Branch) :
    branchFunction (AsymptoticFiniteBranch.compose b c)=branchFunction b*branchFunction c := by
  ext f z
  change (b.coefficient z*c.coefficient (b.label • z))*f ((c.label*b.label) • z)=
    b.coefficient z*(c.coefficient (b.label • z)*f (c.label • b.label • z))
  rw [mul_smul,mul_assoc]

theorem expressionFunction_compose (E F : Expression) :
    expressionFunction (composeExpression E F)=expressionFunction E*expressionFunction F :=
  sum_composeExpression branchFunction branchFunction_compose E F

theorem expressionFunction_append (E F : Expression) :
    expressionFunction (E++F)=expressionFunction E+expressionFunction F := by
  simp only [expressionFunction,List.map_append,List.sum_append]

theorem expressionFunction_identity : expressionFunction [AsymptoticFiniteBranch.identity]=1 := by
  ext f z
  simp [expressionFunction,branchFunction,AsymptoticFiniteBranch.identity]

theorem branchFunction_scale (c : ℂ) (b : Branch) :
    branchFunction (AsymptoticFiniteBranch.scale c b)=c • branchFunction b := by
  ext f z
  exact mul_assoc _ _ _

theorem expressionFunction_scale (c : ℂ) (E : Expression) :
    expressionFunction (scaleExpression c E)=c • expressionFunction E := by
  induction E with
  | nil => simp [expressionFunction,scaleExpression]
  | cons b E ih =>
    change branchFunction (AsymptoticFiniteBranch.scale c b)+expressionFunction (scaleExpression c E)=
      c • (branchFunction b+expressionFunction E)
    rw [branchFunction_scale,ih,smul_add]

theorem expressionFunction_ofFinset {ι : Type*} (s : Finset ι) (f : ι→Branch) :
    expressionFunction (ofFinset s f)=∑ i∈s,branchFunction (f i) := by
  simp only [expressionFunction,ofFinset,List.map_map,Function.comp_def,Finset.sum_map_toList]

/-- The bounded quotient operator has exactly the displayed common branch
expression on every genuine representative. No individual branch is asserted
to preserve automorphy. -/
def QuotientRealizes (N : ℕ) (E : Expression)
    (A : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) : Prop :=
  ∀ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
    ∃ g : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      AutomorphicL2.denseEmbedding _ _ g=A (AutomorphicL2.denseEmbedding _ _ f) ∧
      g.val=expressionFunction E f.val

theorem QuotientRealizes.zero (N : ℕ) : QuotientRealizes N [] 0 := by
  intro f
  refine ⟨0,?_,?_⟩
  · simp only [map_zero,zero_apply]
  · rfl

theorem QuotientRealizes.one (N : ℕ) :
    QuotientRealizes N [AsymptoticFiniteBranch.identity] 1 := by
  intro f
  refine ⟨f,rfl,?_⟩
  rw [expressionFunction_identity]
  rfl

theorem QuotientRealizes.add {N : ℕ} {E F : Expression}
    {A B : AutomorphicSpace N→L[ℂ]AutomorphicSpace N}
    (hE : QuotientRealizes N E A) (hF : QuotientRealizes N F B) :
    QuotientRealizes N (E++F) (A+B) := by
  intro f
  obtain ⟨g,hg,eg⟩ := hE f
  obtain ⟨h,hh,eh⟩ := hF f
  refine ⟨g+h,?_,?_⟩
  · rw [map_add,hg,hh]
    rfl
  · change g.val+h.val=_
    rw [eg,eh,expressionFunction_append]
    rfl

theorem QuotientRealizes.smul {N : ℕ} {E : Expression}
    {A : AutomorphicSpace N→L[ℂ]AutomorphicSpace N}
    (hE : QuotientRealizes N E A) (c : ℂ) :
    QuotientRealizes N (scaleExpression c E) (c • A) := by
  intro f
  obtain ⟨g,hg,eg⟩ := hE f
  refine ⟨c • g,?_,?_⟩
  · rw [map_smul,hg]
    rfl
  · change c • g.val=_
    rw [eg,expressionFunction_scale]
    rfl

theorem QuotientRealizes.mul {N : ℕ} {E F : Expression}
    {A B : AutomorphicSpace N→L[ℂ]AutomorphicSpace N}
    (hE : QuotientRealizes N E A) (hF : QuotientRealizes N F B) :
    QuotientRealizes N (composeExpression E F) (A*B) := by
  intro f
  obtain ⟨g,hg,eg⟩ := hF f
  obtain ⟨h,hh,eh⟩ := hE g
  refine ⟨h,?_,?_⟩
  · rw [hh,hg]
    rfl
  · rw [eh,eg,expressionFunction_compose]
    rfl

theorem QuotientRealizes.pow {N : ℕ} {E : Expression}
    {A : AutomorphicSpace N→L[ℂ]AutomorphicSpace N}
    (hE : QuotientRealizes N E A) (m : ℕ) :
    QuotientRealizes N (powerExpression E m) (A^m) := by
  induction m with
  | zero => exact QuotientRealizes.one N
  | succ m ih =>
    rw [powerExpression,pow_succ']
    exact hE.mul ih

#print axioms expressionFunction_compose
#print axioms QuotientRealizes.add
#print axioms QuotientRealizes.smul
#print axioms QuotientRealizes.mul
#print axioms QuotientRealizes.pow
end QuantitativeMaass
