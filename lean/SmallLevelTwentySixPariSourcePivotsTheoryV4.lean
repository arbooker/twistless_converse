module

public import SmallLevelTwentySixGermThirteenTheoryV4
public import SmallLevelTwentySixPariFirstChartTheoryV4

/-! Consolidated chapter: SmallLevelTwentySixPariSourcePivots. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPariSourcePivotsV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourcePivots
open QuantitativeArithmeticSevenLaurentRows

def source4 (x y z w a b u : ℂ) : ℂ :=
  ((1/2)*x^4+(1/2)*x^3*y+(-1/2)*x^3*a+(1/1)*x^3+(-1/1)*x^2*y+(1/1)*x*y^2+(1/2)*x^2*z+(1/1)*x^2*a+(5/2)*x^2+(-1/1)*y^2+(1/1)*y)+u*((1/1)*x^4+(1/1)*x^3+(1/2)*x^2*y+(-1/2)*x^2*a+(3/2)*x^2+(1/1)*x*y+(-1/1)*y*a+(1/1)*y)

theorem source4_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=source4 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData0,source4]
  ring

def source6 (x y z w a b u : ℂ) : ℂ :=
  ((1/2)*x^4+(1/2)*x^3*y+(-1/2)*x^3*a+(1/1)*x^3+(-1/2)*x^2*y+(1/1)*x*y^2+(1/2)*x^2*z+(1/2)*x^2*w+(1/2)*x^2*a+(1/2)*x^2*b+(7/2)*x^2+(-1/1)*x*y+(-1/1)*y^2+(1/1)*x+(1/1)*y)+u*((1/1)*x^4+(-1/2)*x^3*y+(-1/2)*x^3*a+(3/2)*x^3+(1/1)*x^2*y+(-1/1)*x^2*a+(2/1)*x^2+(1/1)*x*y+(-1/1)*x*a+(-1/1)*y*a+(1/1)*x+(1/1)*y)

theorem source6_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=source6 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData0,source6]
  ring

def zValue (x y w a b u : ℂ) : ℂ := -source4 x y 0 w a b u/(x^2/2)
def bValue (x y w a u : ℂ) : ℂ :=
  -source6 x y (zValue x y w a 0 u) w a 0 u/(x^2/2)

theorem source4_decomposition (x y z w a b u : ℂ) :
    source4 x y z w a b u=(x^2/2)*z+source4 x y 0 w a b u := by
  unfold source4
  ring

theorem source6_decomposition (x y z w a b u : ℂ) :
    source6 x y z w a b u=(x^2/2)*b+source6 x y z w a 0 u := by
  unfold source6
  ring

theorem zValue_independent_b (x y w a b u : ℂ) :
    zValue x y w a b u=zValue x y w a 0 u := by rfl

/-- The two substitutions use only the original equations and x ≠ 0. -/
theorem original_pivots (x y z w a b u : ℂ) (hx : x≠0)
    (h4 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=0)
    (h6 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=0) :
    z=zValue x y w a 0 u ∧ b=bValue x y w a u := by
  have hp : x^2/2≠(0:ℂ) := div_ne_zero (pow_ne_zero 2 hx) (by norm_num)
  rw [source4_binding,source4_decomposition] at h4
  have hz : z=zValue x y w a b u := by
    apply (eq_div_iff hp).2
    linear_combination h4
  rw [zValue_independent_b] at hz
  refine ⟨hz, ?_⟩
  rw [source6_binding,source6_decomposition,hz] at h6
  apply (eq_div_iff hp).2
  linear_combination h6

#print axioms original_pivots
end SmallLevelTwentySixPariSourcePivots
end
end

/-! ## SmallLevelTwentySixPariThirteenReductionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourcePivots
open QuantitativeArithmeticSevenLaurentRows

/-- Original thirteen-row equations after the two justified linear substitutions.
No exceptional coefficient is inverted in this reduction. -/
def reducedThirteenRow (x y w a u : ℂ) (i : Fin 13) : ℂ :=
  eval x y (zValue x y w a 0 u) w a (bValue x y w a u) 1
    (fun j => if j=0 then 1 else u) (SmallLevelTwentySixGermThirteen.rows i)

theorem thirteen_rows_reduced (x y z w a b u : ℂ) (hx : x≠0)
    (h : ∀ i : Fin 13, eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      (SmallLevelTwentySixGermThirteen.rows i)=0) :
    z=zValue x y w a 0 u ∧ b=bValue x y w a u ∧
      ∀ i : Fin 13,reducedThirteenRow x y w a u i=0 := by
  have h4 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=0 := h 4
  have h6 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=0 := h 6
  obtain ⟨hz,hb⟩:=original_pivots x y z w a b u hx h4 h6
  refine ⟨hz,hb,?_⟩
  intro i
  have hi:=h i
  rw [hz,hb] at hi
  exact hi

theorem thirteen_low_equations (x y z w a b u : ℂ) (hx : x≠0)
    (h : ∀ i : Fin 13, eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      (SmallLevelTwentySixGermThirteen.rows i)=0) :
    SmallLevelTwentySixPariFirstChart.quadratic x y z w a b u=0 ∧
    SmallLevelTwentySixPariFirstChart.linear x y z w a b u=0 ∧
    SmallLevelTwentySixPariFirstChart.constantTerm x y *
      SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u=0 := by
  have h0 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0 := h 0
  have h2 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0 := h 2
  have h3 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=0 := h 3
  have hcurve:=SmallLevelTwentySixPariFirstChart.source_low_curve_product x y z w a b u hx h0 h2 h3
  have hr:=SmallLevelTwentySixPariFirstChart.first_resultant_zero x y z w a b u h0 h2
  rw [SmallLevelTwentySixPariFirstChart.source0_binding] at h0
  rw [SmallLevelTwentySixPariFirstChart.source3_binding] at h3
  have hc:=SmallLevelTwentySixPariFirstChart.source03_combination x y z w a b u
  rw [h0,h3,zero_mul,mul_zero,zero_add] at hc
  have hq : SmallLevelTwentySixPariFirstChart.quadratic x y z w a b u=0 :=
    (mul_eq_zero.mp hc.symm).resolve_left hx
  rw [SmallLevelTwentySixPariFirstChart.first_resultant_factor] at hr
  have he:=(mul_eq_zero.mp hr).resolve_left hx
  have hl:=SmallLevelTwentySixPariIdentity005.identity x y z w a b u
  change SmallLevelTwentySixPariIdentity005.p0 x y z w a b u=0 at hq
  rw [hq,he] at hl
  refine ⟨hq,?_,hcurve⟩
  simpa only [SmallLevelTwentySixPariFirstChart.linear,
    SmallLevelTwentySixPariIdentity005.p2,SmallLevelTwentySixPariIdentity005.p6,
    zero_mul,mul_zero,zero_add,add_zero,one_mul] using hl

#print axioms thirteen_rows_reduced
#print axioms thirteen_low_equations
end SmallLevelTwentySixPariSourcePivots
end
end
