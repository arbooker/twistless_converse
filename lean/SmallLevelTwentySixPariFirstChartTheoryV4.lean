module

public import SmallLevelTwentySixGermPrimitiveSparseMMMFamilyV4
public import SmallLevelTwentySixPariIdentityFamilyV4

/-! Consolidated chapter: SmallLevelTwentySixPariFirstChart. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPariFirstChartSourcesV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariFirstChart
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixPariIdentity004

/-- Bind the first resultant input to the actual normalized primitive row. -/
theorem source0_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=p0 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData0,p0]
  ring

theorem source2_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=p2 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData0,p2]
  ring

/-- This elimination consequence now follows from the actual source rows,
rather than an assumption about the exported CAS polynomials. -/
theorem first_resultant_zero (x y z w a b u : ℂ)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h2 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0) :
    p4 x y z w a b u=0 := by
  rw [source0_binding] at h0
  rw [source2_binding] at h2
  have h:=identity x y z w a b u
  simpa only [h0,h2,p6,mul_zero,zero_mul,zero_add,add_zero] using h.symm

theorem first_chart_x_ne_two (x y z w a b u : ℂ)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0) : x≠2 := by
  intro hx
  rw [source0_binding,hx] at h0
  have he : p0 2 y z w a b u=(-52/15:ℂ) := by unfold p0; ring
  rw [he] at h0
  norm_num at h0

def constantTerm (x y : ℂ) : ℂ :=
  -x^3/3+(-y/2+5/3)*x^2+(3*y/2-127/30)*x-y+1

def linearTerm (x a : ℂ) : ℂ :=
  -9*x^2/10+(a/2+13/10)*x-a+1

theorem source0_decomposition (x y z w a b u : ℂ) :
    p0 x y z w a b u=constantTerm x y+linearTerm x a*u := by
  unfold p0 constantTerm linearTerm
  ring

/-- The exceptional branch is retained explicitly; no coefficient is divided out. -/
theorem exceptional_split (x y z w a b u : ℂ)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (hc : constantTerm x y=0) : linearTerm x a=0 ∨ u=0 := by
  rw [source0_binding,source0_decomposition,hc,zero_add] at h0
  exact mul_eq_zero.mp h0

#print axioms first_resultant_zero
#print axioms first_chart_x_ne_two
#print axioms exceptional_split
end SmallLevelTwentySixPariFirstChart
end
end

/-! ## SmallLevelTwentySixPariLowCurveSourcesV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariFirstChart
open QuantitativeArithmeticSevenLaurentRows

abbrev quadratic := SmallLevelTwentySixPariIdentity005.p0
abbrev linear := SmallLevelTwentySixPariIdentity005.p3
abbrev lowCurve := SmallLevelTwentySixPariIdentity007.p1

def source3 (x y z w a b u : ℂ) : ℂ :=
  ((((1/3)*x+((20/27)*y+((2/9)*a+((4/3)*u+(-1/3)))))*x+(((1/3)*a+(7/27))*y+(((-1/3)*u+(-2/3))*a+((1)*u+(2/3)))))*x+(((-1/3)*a+(-1))*y+((((-1/3)*u)*a+((-2/3)*u+(1/3)))*a+((1)*u+(1)))))

def factor03 (x y z w a b u : ℂ) : ℂ :=
  (((-4/3)*x+((1/3)*a+(-1)))*x+(((1/3)*a+(2/3))*a+(-1)))

theorem source3_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=source3 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData0,source3]
  ring

theorem source03_combination (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity004.p0 x y z w a b u*factor03 x y z w a b u+
      SmallLevelTwentySixPariIdentity004.p3 x y z w a b u*source3 x y z w a b u=
      x*quadratic x y z w a b u := by
  unfold SmallLevelTwentySixPariIdentity004.p0 SmallLevelTwentySixPariIdentity004.p3
    factor03 source3 quadratic SmallLevelTwentySixPariIdentity005.p0
  ring

theorem first_resultant_factor (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity004.p4 x y z w a b u=
      x*SmallLevelTwentySixPariIdentity005.p4 x y z w a b u := by
  unfold SmallLevelTwentySixPariIdentity004.p4 SmallLevelTwentySixPariIdentity005.p4
  ring

theorem quadratic_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity006.p0 x y z w a b u=SmallLevelTwentySixPariIdentity005.p0 x y z w a b u := by
  unfold SmallLevelTwentySixPariIdentity006.p0 SmallLevelTwentySixPariIdentity005.p0
  ring

theorem linear_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity006.p2 x y z w a b u=SmallLevelTwentySixPariIdentity005.p3 x y z w a b u := by
  unfold SmallLevelTwentySixPariIdentity006.p2 SmallLevelTwentySixPariIdentity005.p3
  ring

theorem low_resultant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity007.p4 x y z w a b u=SmallLevelTwentySixPariIdentity006.p4 x y z w a b u := by
  unfold SmallLevelTwentySixPariIdentity007.p4 SmallLevelTwentySixPariIdentity006.p4
  ring

theorem constant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity007.p0 x y z w a b u=constantTerm x y := by
  unfold SmallLevelTwentySixPariIdentity007.p0 constantTerm
  ring

/-- The low-degree elimination curve follows from actual primitive rows 0,2,3.
The exceptional coefficient remains a factor, so this assertion makes no
unjustified nonvanishing assumption about it. -/
theorem source_low_curve_product (x y z w a b u : ℂ) (hx : x≠0)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h2 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0)
    (h3 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=0) :
    constantTerm x y*lowCurve x y z w a b u=0 := by
  have hr:=first_resultant_zero x y z w a b u h0 h2
  rw [source0_binding] at h0
  rw [source3_binding] at h3
  have hc:=source03_combination x y z w a b u
  rw [h0,h3,zero_mul,mul_zero,zero_add] at hc
  have hq : quadratic x y z w a b u=0 := (mul_eq_zero.mp hc.symm).resolve_left hx
  rw [first_resultant_factor] at hr
  have he:=(mul_eq_zero.mp hr).resolve_left hx
  have hl:=SmallLevelTwentySixPariIdentity005.identity x y z w a b u
  change SmallLevelTwentySixPariIdentity005.p0 x y z w a b u=0 at hq
  rw [hq,he] at hl
  have hl0 : linear x y z w a b u=0 := by
    simpa only [SmallLevelTwentySixPariIdentity005.p2,SmallLevelTwentySixPariIdentity005.p6,
      zero_mul,mul_zero,zero_add,add_zero,one_mul] using hl
  change SmallLevelTwentySixPariIdentity005.p3 x y z w a b u=0 at hl0
  have hh:=SmallLevelTwentySixPariIdentity006.identity x y z w a b u
  rw [quadratic_binding,linear_binding,hq,hl0] at hh
  have hh0 : SmallLevelTwentySixPariIdentity006.p4 x y z w a b u=0 := by
    simpa only [SmallLevelTwentySixPariIdentity006.p6,zero_mul,mul_zero,zero_add,add_zero] using hh.symm
  have hv:=SmallLevelTwentySixPariIdentity007.identity x y z w a b u
  rw [low_resultant_binding,hh0,constant_binding] at hv
  simpa only [SmallLevelTwentySixPariIdentity007.p3,SmallLevelTwentySixPariIdentity007.p6,
    mul_zero,add_zero] using hv

theorem source_low_curve (x y z w a b u : ℂ) (hx : x≠0)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h2 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0)
    (h3 : eval x y z w a b 1 (fun i => if i=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=0)
    (hc : constantTerm x y≠0) : lowCurve x y z w a b u=0 :=
  (mul_eq_zero.mp (source_low_curve_product x y z w a b u hx h0 h2 h3)).resolve_left hc

theorem constant_zero_avoids_one_two (x y : ℂ) (hc : constantTerm x y=0) :
    x≠1 ∧ x≠2 := by
  constructor
  · intro hx
    rw [hx] at hc
    have he : constantTerm 1 y=(-19/10:ℂ) := by unfold constantTerm; ring
    rw [he] at hc
    norm_num at hc
  · intro hx
    rw [hx] at hc
    have he : constantTerm 2 y=(-52/15:ℂ) := by unfold constantTerm; ring
    rw [he] at hc
    norm_num at hc

#print axioms source_low_curve_product
#print axioms source_low_curve
end SmallLevelTwentySixPariFirstChart
end
end
