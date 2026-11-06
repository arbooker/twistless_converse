module
public import SmallLevelTwentySixPariCompactIndexBindingSeriesV4
public import SmallLevelTwentySixPariIdentityFamilyV4
public import SmallLevelTwentySixPariFirstChartTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixPariRemainder87
open SmallLevelPolynomialCoefficientCertificate
theorem quadratic_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity001.p0 x y z w a b u=SmallLevelTwentySixPariIdentity005.p0 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity001.p0,SmallLevelTwentySixPariIdentity001.coefficients0,SmallLevelTwentySixPariIdentity001.c0_0,SmallLevelTwentySixPariIdentity001.c0_1,SmallLevelTwentySixPariIdentity001.c0_2,evaluate,SmallLevelTwentySixPariIdentity005.p0] <;> ring
theorem linear_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity008.p0 x y z w a b u=SmallLevelTwentySixPariIdentity005.p3 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity008.p0,SmallLevelTwentySixPariIdentity008.coefficients0,SmallLevelTwentySixPariIdentity008.c0_0,SmallLevelTwentySixPariIdentity008.c0_1,SmallLevelTwentySixPariIdentity008.c0_2,evaluate,SmallLevelTwentySixPariIdentity005.p3] <;> ring
theorem resultant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity008.p4 x y z w a b u=SmallLevelTwentySixPariIdentity011.p4 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity008.p4,SmallLevelTwentySixPariIdentity008.coefficients4,SmallLevelTwentySixPariIdentity008.c4_0,SmallLevelTwentySixPariIdentity008.c4_1,SmallLevelTwentySixPariIdentity008.c4_2,SmallLevelTwentySixPariIdentity008.c4_3,SmallLevelTwentySixPariIdentity008.c4_4,SmallLevelTwentySixPariIdentity008.c4_5,SmallLevelTwentySixPariIdentity008.c4_6,SmallLevelTwentySixPariIdentity008.c4_7,SmallLevelTwentySixPariIdentity008.c4_8,SmallLevelTwentySixPariIdentity008.c4_9,SmallLevelTwentySixPariIdentity008.c4_10,SmallLevelTwentySixPariIdentity008.c4_11,evaluate,SmallLevelTwentySixPariIdentity011.p4] <;> ring
theorem constant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity011.p0 x y z w a b u=SmallLevelTwentySixPariIdentity007.p0 x y z w a b u := by
  rfl

/-- A generic-branch consequence of the source resultant. Its source premise
is discharged separately; this does not assert the original pole exclusion. -/
theorem generic_remainder_zero (x y z w a b u : ℂ)
    (hq : SmallLevelTwentySixPariFirstChart.quadratic x y z w a b u=0)
    (hl : SmallLevelTwentySixPariFirstChart.linear x y z w a b u=0)
    (hc : SmallLevelTwentySixPariFirstChart.constantTerm x y≠0)
    (hR : SmallLevelTwentySixPariIdentity001.p4 x y z w a b u=0) :
    SmallLevelTwentySixPariIdentity011.p1 x y z w a b u=0 := by
  have hq0 : SmallLevelTwentySixPariIdentity001.p0 x y z w a b u=0 := (quadratic_binding x y z w a b u).trans hq
  have hd:=SmallLevelTwentySixPariIdentity001.identity x y z w a b u
  rw [hq0,hR] at hd
  have hr : SmallLevelTwentySixPariIdentity001.p3 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity001.p2,SmallLevelTwentySixPariIdentity001.coefficients2,SmallLevelTwentySixPariIdentity001.c2_0,evaluate,SmallLevelTwentySixPariIdentity001.p6,SmallLevelTwentySixPariIdentity001.coefficients6] using hd
  have hr2 : SmallLevelTwentySixPariIdentity008.p2 x y z w a b u=0 := (SmallLevelTwentySixPariCompact87Binding.binding x y z w a b u).symm.trans hr
  have hl0 : SmallLevelTwentySixPariIdentity008.p0 x y z w a b u=0 := (linear_binding x y z w a b u).trans hl
  have hi:=SmallLevelTwentySixPariIdentity008.identity x y z w a b u
  rw [hl0,hr2] at hi
  have hb : SmallLevelTwentySixPariIdentity008.p4 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity008.p6,SmallLevelTwentySixPariIdentity008.coefficients6,evaluate] using hi.symm
  have he:=SmallLevelTwentySixPariIdentity011.identity x y z w a b u
  rw [constant_binding,←resultant_binding,hb,SmallLevelTwentySixPariFirstChart.constant_binding] at he
  have hp : SmallLevelTwentySixPariFirstChart.constantTerm x y*SmallLevelTwentySixPariIdentity011.p1 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity011.p3,SmallLevelTwentySixPariIdentity011.p6] using he
  exact (mul_eq_zero.mp hp).resolve_left hc

#print axioms generic_remainder_zero
end SmallLevelTwentySixPariRemainder87
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixPariRemainder89
open SmallLevelPolynomialCoefficientCertificate
theorem quadratic_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity003.p0 x y z w a b u=SmallLevelTwentySixPariIdentity005.p0 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity003.p0,SmallLevelTwentySixPariIdentity003.coefficients0,SmallLevelTwentySixPariIdentity003.c0_0,SmallLevelTwentySixPariIdentity003.c0_1,SmallLevelTwentySixPariIdentity003.c0_2,evaluate,SmallLevelTwentySixPariIdentity005.p0] <;> ring
theorem linear_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity010.p0 x y z w a b u=SmallLevelTwentySixPariIdentity005.p3 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity010.p0,SmallLevelTwentySixPariIdentity010.coefficients0,SmallLevelTwentySixPariIdentity010.c0_0,SmallLevelTwentySixPariIdentity010.c0_1,SmallLevelTwentySixPariIdentity010.c0_2,evaluate,SmallLevelTwentySixPariIdentity005.p3] <;> ring
theorem resultant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity010.p4 x y z w a b u=SmallLevelTwentySixPariIdentity015.p4 x y z w a b u := by
  norm_num [SmallLevelTwentySixPariIdentity010.p4,SmallLevelTwentySixPariIdentity010.coefficients4,SmallLevelTwentySixPariIdentity010.c4_0,SmallLevelTwentySixPariIdentity010.c4_1,SmallLevelTwentySixPariIdentity010.c4_2,SmallLevelTwentySixPariIdentity010.c4_3,SmallLevelTwentySixPariIdentity010.c4_4,SmallLevelTwentySixPariIdentity010.c4_5,SmallLevelTwentySixPariIdentity010.c4_6,SmallLevelTwentySixPariIdentity010.c4_7,SmallLevelTwentySixPariIdentity010.c4_8,SmallLevelTwentySixPariIdentity010.c4_9,SmallLevelTwentySixPariIdentity010.c4_10,SmallLevelTwentySixPariIdentity010.c4_11,evaluate,SmallLevelTwentySixPariIdentity015.p4] <;> ring
theorem constant_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity015.p0 x y z w a b u=SmallLevelTwentySixPariIdentity007.p0 x y z w a b u := by
  rfl

/-- A generic-branch consequence of the source resultant. Its source premise
is discharged separately; this does not assert the original pole exclusion. -/
theorem generic_remainder_zero (x y z w a b u : ℂ)
    (hq : SmallLevelTwentySixPariFirstChart.quadratic x y z w a b u=0)
    (hl : SmallLevelTwentySixPariFirstChart.linear x y z w a b u=0)
    (hc : SmallLevelTwentySixPariFirstChart.constantTerm x y≠0)
    (hR : SmallLevelTwentySixPariIdentity003.p4 x y z w a b u=0) :
    SmallLevelTwentySixPariIdentity015.p1 x y z w a b u=0 := by
  have hq0 : SmallLevelTwentySixPariIdentity003.p0 x y z w a b u=0 := (quadratic_binding x y z w a b u).trans hq
  have hd:=SmallLevelTwentySixPariIdentity003.identity x y z w a b u
  rw [hq0,hR] at hd
  have hr : SmallLevelTwentySixPariIdentity003.p3 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity003.p2,SmallLevelTwentySixPariIdentity003.coefficients2,SmallLevelTwentySixPariIdentity003.c2_0,evaluate,SmallLevelTwentySixPariIdentity003.p6,SmallLevelTwentySixPariIdentity003.coefficients6] using hd
  have hr2 : SmallLevelTwentySixPariIdentity010.p2 x y z w a b u=0 := (SmallLevelTwentySixPariCompact89Binding.binding x y z w a b u).symm.trans hr
  have hl0 : SmallLevelTwentySixPariIdentity010.p0 x y z w a b u=0 := (linear_binding x y z w a b u).trans hl
  have hi:=SmallLevelTwentySixPariIdentity010.identity x y z w a b u
  rw [hl0,hr2] at hi
  have hb : SmallLevelTwentySixPariIdentity010.p4 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity010.p6,SmallLevelTwentySixPariIdentity010.coefficients6,evaluate] using hi.symm
  have he:=SmallLevelTwentySixPariIdentity015.identity x y z w a b u
  rw [constant_binding,←resultant_binding,hb,SmallLevelTwentySixPariFirstChart.constant_binding] at he
  have hp : SmallLevelTwentySixPariFirstChart.constantTerm x y*SmallLevelTwentySixPariIdentity015.p1 x y z w a b u=0 := by
    simpa [SmallLevelTwentySixPariIdentity015.p3,SmallLevelTwentySixPariIdentity015.p6] using he
  exact (mul_eq_zero.mp hp).resolve_left hc

#print axioms generic_remainder_zero
end SmallLevelTwentySixPariRemainder89
end
