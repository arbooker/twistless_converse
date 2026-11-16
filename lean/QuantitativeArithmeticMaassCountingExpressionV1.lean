module
public import QuantitativeMaassQuotientGeneratorExpressionV1
public import AsymptoticCosetTraceSumsV1
public import QuantitativeNewGapNormalizerV1
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticFiniteBranch AsymptoticNestedQuotients
open ContinuousLinearMap AsymptoticQuotientOperators QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.Counting
attribute [local instance] Classical.propDecidable

abbrev G := AsymptoticRationalGroup.Group
abbrev LiftSpace := ℍ → G → ℂ

def branchAction (b : Branch) : Module.End ℂ LiftSpace where
  toFun f x g := b.coefficient x*f (b.label • x) (b.label*g)
  map_add' f h := by ext x g; exact mul_add _ _ _
  map_smul' c f := by ext x g; exact mul_left_comm _ _ _

def expressionAction (E : Expression) : Module.End ℂ LiftSpace :=
  (E.map branchAction).sum

def lift (H : Subgroup G) (f : ℓ²(Classes H,ℂ)) : LiftSpace :=
  fun _ g => f (classOf H g)

/-- The whole expression acts on the quotient. Its individual rational
branches need not preserve the quotient, and no such assumption is made. -/
def Realizes (H : Subgroup G) (E : Expression)
    (A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) : Prop :=
  ∀ f, lift H (A f)=expressionAction E (lift H f)

theorem branchAction_compose (b c : Branch) :
    branchAction (AsymptoticFiniteBranch.compose b c)=branchAction b*branchAction c := by
  ext f x g
  change (b.coefficient x*c.coefficient (b.label • x))*
      f ((c.label*b.label) • x) ((c.label*b.label)*g)=
    b.coefficient x*(c.coefficient (b.label • x)*
      f (c.label • b.label • x) (c.label*(b.label*g)))
  rw [mul_smul,mul_assoc,mul_assoc]

theorem expressionAction_compose (E F : Expression) :
    expressionAction (composeExpression E F)=expressionAction E*expressionAction F :=
  sum_composeExpression branchAction branchAction_compose E F

theorem expressionAction_append (E F : Expression) :
    expressionAction (E++F)=expressionAction E+expressionAction F := by
  simp only [expressionAction,List.map_append,List.sum_append]

theorem expressionAction_identity : expressionAction [AsymptoticFiniteBranch.identity]=1 := by
  ext f x g
  simp [expressionAction,branchAction,AsymptoticFiniteBranch.identity]

theorem expressionAction_scale (c : ℂ) (E : Expression) :
    expressionAction (scaleExpression c E)=c • expressionAction E := by
  have hs (b : Branch) : branchAction (AsymptoticFiniteBranch.scale c b)=c • branchAction b := by
    ext f x g
    exact mul_assoc _ _ _
  induction E with
  | nil => simp [expressionAction,scaleExpression]
  | cons b E ih =>
    change branchAction (AsymptoticFiniteBranch.scale c b)+expressionAction (scaleExpression c E)=
      c • (branchAction b+expressionAction E)
    rw [hs,ih,smul_add]

theorem expressionAction_apply (E : Expression) (f : LiftSpace) (x : ℍ) (g : G) :
    expressionAction E f x g=
      (E.map (fun b => b.coefficient x*f (b.label • x) (b.label*g))).sum := by
  induction E with
  | nil => rfl
  | cons b E ih =>
    change b.coefficient x*f (b.label • x) (b.label*g)+expressionAction E f x g=_
    rw [ih]
    rfl

theorem expressionAction_ofFinset {ι : Type*} (s : Finset ι) (b : ι→Branch) :
    expressionAction (ofFinset s b)=∑ i∈s,branchAction (b i) := by
  simp only [expressionAction,ofFinset,List.map_map,Function.comp_def,Finset.sum_map_toList]

theorem Realizes.one (H : Subgroup G) : Realizes H [AsymptoticFiniteBranch.identity] 1 := by
  intro f
  rw [expressionAction_identity]
  rfl

theorem Realizes.add {H : Subgroup G} {E F : Expression}
    {A B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)}
    (hE : Realizes H E A) (hF : Realizes H F B) : Realizes H (E++F) (A+B) := by
  intro f
  change lift H (A f)+lift H (B f)=_
  rw [hE,hF,expressionAction_append]
  rfl

theorem Realizes.smul {H : Subgroup G} {E : Expression}
    {A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)}
    (hE : Realizes H E A) (c : ℂ) : Realizes H (scaleExpression c E) (c • A) := by
  intro f
  change c • lift H (A f)=_
  rw [hE,expressionAction_scale]
  rfl

theorem Realizes.mul {H : Subgroup G} {E F : Expression}
    {A B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)}
    (hE : Realizes H E A) (hF : Realizes H F B) : Realizes H (composeExpression E F) (A*B) := by
  intro f
  change lift H (A (B f))=_
  rw [hE,hF,expressionAction_compose]
  rfl

theorem Realizes.pow {H : Subgroup G} {E : Expression}
    {A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)}
    (hE : Realizes H E A) (n : ℕ) : Realizes H (powerExpression E n) (A^n) := by
  induction n with
  | zero => exact Realizes.one H
  | succ n ih => simpa only [powerExpression,pow_succ'] using hE.mul ih

/-- The concrete quotient permutation realizes the actual rational pullback. -/
theorem normalizer_realizes (H : Subgroup G) (a : G)
    (ha : ∀ g∈H,a*g*a⁻¹∈H) (hai : ∀ g∈H,a⁻¹*g*a∈H) :
    Realizes H (quotientPullbackExpression a) (permutationOperator (leftMulEquiv H a ha hai)) := by
  intro f
  funext x g
  change f (classOf H (a*g))=_
  simp [expressionAction,quotientPullbackExpression,branchAction,quotientPullbackBranch,lift]

/-- The unnormalized trace has exactly the relative-index factor. -/
theorem coverTrace_realizes {M N : ℕ} [NeZero N] (hMN : M∣N) :
    Realizes (AsymptoticCongruenceStrip.gamma N) (quotientCoverTraceExpression hMN)
      (((((AsymptoticCongruenceStrip.gamma N).subgroupOf
          (AsymptoticCongruenceStrip.gamma M)).index:ℕ):ℂ) •
        (space (AsymptoticCongruenceStrip.gamma_le_of_dvd hMN)).starProjection) := by
  classical
  let H := AsymptoticCongruenceStrip.gamma N
  let J := AsymptoticCongruenceStrip.gamma M
  let h : H≤J := AsymptoticCongruenceStrip.gamma_le_of_dvd hMN
  let := Fintype.ofFinite (J ⧸ H.subgroupOf J)
  have hn : ((H.subgroupOf J).index:ℂ)≠0 := by
    exact_mod_cast (index_pos (H:=H) (J:=J)).ne'
  intro f
  funext x g
  change ((H.subgroupOf J).index:ℂ)*((space h).starProjection f (classOf H g))=_
  rw [projection_apply,forget_classOf]
  rw [fibre_sum_eq_coset_sum h (fun q : J ⧸ H.subgroupOf J => q.out)
    (Equiv.refl _) (by intro q; exact (QuotientGroup.out_eq' q).symm)]
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  rw [quotientCoverTraceExpression,expressionAction_ofFinset]
  simp only [LinearMap.sum_apply,Finset.sum_apply,branchAction,LinearMap.coe_mk,
    AddHom.coe_mk,quotientPullbackBranch,one_mul,lift]
  apply Finset.sum_congr
  · ext q; simp
  · intro q _; rfl

/-- Exact root coefficient; membership in H, rather than equality to the
identity rational matrix, is the correct quotient return condition. -/
theorem Realizes.root_coefficient {H : Subgroup G} {E : Expression}
    {A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)} (hE : Realizes H E A) (x : ℍ) :
    (A (AsymptoticRegularTrace.delta (classOf H 1))) (classOf H 1)=
      (E.map (fun b => if b.label∈H then b.coefficient x else 0)).sum := by
  classical
  have h := congrFun (congrFun (hE (AsymptoticRegularTrace.delta (classOf H 1))) x) 1
  rw [expressionAction_apply] at h
  simpa only [lift,mul_one,AsymptoticRegularTrace.delta,lp.single_apply,Pi.single_apply,
    classOf_eq_iff,inv_one,mul_ite,mul_one,one_mul,mul_zero,Subgroup.inv_mem_iff] using h

#print axioms coverTrace_realizes
#print axioms normalizer_realizes
#print axioms Realizes.root_coefficient
#print axioms Realizes.mul
#print axioms Realizes.pow
end QuantitativeMaass.Counting
