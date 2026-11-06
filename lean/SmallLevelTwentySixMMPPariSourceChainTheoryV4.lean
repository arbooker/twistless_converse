module

public import SmallLevelTwentySixMMPPariLinkIndexPFamilySeriesV4
public import SmallLevelTwentySixMMPPariLinkIndexPIndexSeriesV4
public import SmallLevelTwentySixMMPPariSourceBindingFamilyV4
public import SmallLevelTwentySixMMPPariTheoryV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4

/-! Consolidated chapter: SmallLevelTwentySixMMPPariSourceChain. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixMMPPariSmallSourceBindingsV1 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSourceChain
open SmallLevelPolynomialCoefficientCertificate SmallLevelTwentySixMMPPari
theorem small_source_0 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=c00 x y z w a b+c01 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace001.p1,evaluate,c00,c01] <;> ring
#print axioms small_source_0
theorem small_source_1 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace001.p3 x y z w a b u=c10 x y z w a b+c11 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace001.p3,evaluate,c10,c11] <;> ring
#print axioms small_source_1
theorem small_source_2 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=c20 x y z w a b+c21 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace007.p1,evaluate,c20,c21] <;> ring
#print axioms small_source_2
theorem small_source_3 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace003.p3 x y z w a b u=c30 x y z w a b+c31 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace003.p3,evaluate,c30,c31] <;> ring
#print axioms small_source_3
theorem small_source_4 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=c40 x y z w a b+c41 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace009.p1,SmallLevelTwentySixMMPPariTrace009.coefficients1,SmallLevelTwentySixMMPPariTrace009.c1_0,SmallLevelTwentySixMMPPariTrace009.c1_1,SmallLevelTwentySixMMPPariTrace009.c1_2,SmallLevelTwentySixMMPPariTrace009.c1_3,SmallLevelTwentySixMMPPariTrace009.c1_4,evaluate,c40,c41] <;> ring
#print axioms small_source_4
theorem small_source_5 (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace007.p3 x y z w a b u=c50 x y z w a b+c51 x y z w a b*u := by
  simp only [SmallLevelTwentySixMMPPariTrace007.p3,evaluate,c50,c51] <;> ring
#print axioms small_source_5
end SmallLevelTwentySixMMPPariSourceChain
end
end

/-! ## SmallLevelTwentySixMMPPariSourceChainInitialV1 -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSourceChain
theorem initial (x y z w a b u : ℂ) (hx : x≠0) (hx2 : x≠2)
    (hc : SmallLevelTwentySixMMPPari.c00 x y z w a b≠0)
    (hs0 : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=0)
    (hs1 : SmallLevelTwentySixMMPPariTrace001.p3 x y z w a b u=0)
    (hs2 : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=0)
    (hs3 : SmallLevelTwentySixMMPPariTrace003.p3 x y z w a b u=0)
    (hs4 : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=0)
    (hs5 : SmallLevelTwentySixMMPPariTrace007.p3 x y z w a b u=0)
    (hs6 : SmallLevelTwentySixMMPPariTrace009.p3 x y z w a b u=0)
    (hs7 : SmallLevelTwentySixMMPPariTrace021.p3 x y z w a b u=0)
    : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=0 ∧ SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=0 ∧ SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=0 := by
  have he1:=SmallLevelTwentySixMMPPariTrace001.identity x y z w a b u
  rw [hs0] at he1
  rw [hs1] at he1
  have hp1 : SmallLevelTwentySixMMPPariTrace001.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace001.p6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp1] at he1
  have h1_4 : SmallLevelTwentySixMMPPariTrace001.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he1.symm
  have he2:=SmallLevelTwentySixMMPPariTrace002.identity x y z w a b u
  have empty2_3 : SmallLevelTwentySixMMPPariTrace002.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace002.p3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty2_3] at he2
  rw [SmallLevelTwentySixMMPPariLink002P1.binding] at he2
  rw [h1_4] at he2
  have hp2 : SmallLevelTwentySixMMPPariTrace002.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace002.p4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp2] at he2
  have hz2 : (SmallLevelTwentySixMMPPariTrace002.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he2.symm
  have hm2 : SmallLevelTwentySixMMPPariTrace002.p5 x y z w a b u=x-2 := by
    simp only [SmallLevelTwentySixMMPPariTrace002.p5,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm2] at hz2
  have h2_6 : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=0 := (mul_eq_zero.mp hz2).resolve_left (sub_ne_zero.mpr hx2)
  have he3:=SmallLevelTwentySixMMPPariTrace003.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink003P1.binding] at he3
  rw [hs0] at he3
  rw [hs3] at he3
  have hp3 : SmallLevelTwentySixMMPPariTrace003.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace003.p6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp3] at he3
  have h3_4 : SmallLevelTwentySixMMPPariTrace003.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he3.symm
  have he4:=SmallLevelTwentySixMMPPariTrace004.identity x y z w a b u
  have empty4_3 : SmallLevelTwentySixMMPPariTrace004.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace004.p3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty4_3] at he4
  rw [SmallLevelTwentySixMMPPariLink004P1.binding] at he4
  rw [h3_4] at he4
  have hp4 : SmallLevelTwentySixMMPPariTrace004.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace004.p4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp4] at he4
  have hz4 : (SmallLevelTwentySixMMPPariTrace004.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace004.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he4.symm
  have hm4 : SmallLevelTwentySixMMPPariTrace004.p5 x y z w a b u=x^1 := by
    simp only [SmallLevelTwentySixMMPPariTrace004.p5,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm4] at hz4
  have h4_6 : SmallLevelTwentySixMMPPariTrace004.p6 x y z w a b u=0 := (mul_eq_zero.mp hz4).resolve_left (pow_ne_zero 1 hx)
  have he5:=SmallLevelTwentySixMMPPariTrace005.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink005P1.binding] at he5
  rw [h4_6] at he5
  rw [SmallLevelTwentySixMMPPariLink005P3.binding] at he5
  rw [h2_6] at he5
  have hp5 : SmallLevelTwentySixMMPPariTrace005.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace005.p6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp5] at he5
  have h5_4 : SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he5.symm
  have he7:=SmallLevelTwentySixMMPPariTrace007.identity x y z w a b u
  rw [hs2] at he7
  rw [hs5] at he7
  have hp7 : SmallLevelTwentySixMMPPariTrace007.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace007.p6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp7] at he7
  have h7_4 : SmallLevelTwentySixMMPPariTrace007.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he7.symm
  have he8:=SmallLevelTwentySixMMPPariTrace008.identity x y z w a b u
  have empty8_3 : SmallLevelTwentySixMMPPariTrace008.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace008.p3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty8_3] at he8
  rw [SmallLevelTwentySixMMPPariLink008P1.binding] at he8
  rw [h7_4] at he8
  have hp8 : SmallLevelTwentySixMMPPariTrace008.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace008.p4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp8] at he8
  have hz8 : (SmallLevelTwentySixMMPPariTrace008.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he8.symm
  have hm8 : SmallLevelTwentySixMMPPariTrace008.p5 x y z w a b u=x^1 := by
    simp only [SmallLevelTwentySixMMPPariTrace008.p5,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm8] at hz8
  have h8_6 : SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=0 := (mul_eq_zero.mp hz8).resolve_left (pow_ne_zero 1 hx)
  exact ⟨h2_6,h5_4,h8_6⟩
#print axioms initial
end SmallLevelTwentySixMMPPariSourceChain
end
end

/-! ## SmallLevelTwentySixMMPPariSourceChainFirstV1 -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSourceChain
theorem first (x y z w a b u : ℂ) (hx : x≠0) (hx2 : x≠2)
    (hc : SmallLevelTwentySixMMPPari.c00 x y z w a b≠0)
    (hs0 : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=0)
    (hs1 : SmallLevelTwentySixMMPPariTrace001.p3 x y z w a b u=0)
    (hs2 : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=0)
    (hs3 : SmallLevelTwentySixMMPPariTrace003.p3 x y z w a b u=0)
    (hs4 : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=0)
    (hs5 : SmallLevelTwentySixMMPPariTrace007.p3 x y z w a b u=0)
    (hs6 : SmallLevelTwentySixMMPPariTrace009.p3 x y z w a b u=0)
    (hs7 : SmallLevelTwentySixMMPPariTrace021.p3 x y z w a b u=0)
    (h2_6 : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=0)
    (h5_4 : SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=0)
    (h8_6 : SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=0)
    : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u=0 := by
  have he9:=SmallLevelTwentySixMMPPariTrace009.identity x y z w a b u
  rw [hs4] at he9
  rw [hs6] at he9
  have hp9 : SmallLevelTwentySixMMPPariTrace009.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace009.p6,SmallLevelTwentySixMMPPariTrace009.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp9] at he9
  have h9_4 : SmallLevelTwentySixMMPPariTrace009.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he9.symm
  have he10:=SmallLevelTwentySixMMPPariTrace010.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink010P1.binding] at he10
  rw [hs2] at he10
  rw [SmallLevelTwentySixMMPPariLink010P3.binding] at he10
  rw [h9_4] at he10
  have hp10 : SmallLevelTwentySixMMPPariTrace010.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace010.p6,SmallLevelTwentySixMMPPariTrace010.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp10] at he10
  have h10_4 : SmallLevelTwentySixMMPPariTrace010.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he10.symm
  have he11:=SmallLevelTwentySixMMPPariTrace011.identity_shift x y z w a b u
  have empty11_3 : SmallLevelTwentySixMMPPariTrace011.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace011.p3,SmallLevelTwentySixMMPPariTrace011.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty11_3] at he11
  rw [SmallLevelTwentySixMMPPariLink011P1.binding] at he11
  rw [h10_4] at he11
  have hp11 : SmallLevelTwentySixMMPPariTrace011.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace011.p4,SmallLevelTwentySixMMPPariTrace011.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp11] at he11
  have hz11 : (SmallLevelTwentySixMMPPariTrace011.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace011.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he11.symm
  have hm11 : SmallLevelTwentySixMMPPariTrace011.p5 x y z w a b u=x^2 := by
    simp only [SmallLevelTwentySixMMPPariTrace011.p5,SmallLevelTwentySixMMPPariTrace011.coefficients5,SmallLevelTwentySixMMPPariTrace011.c5_0,SmallLevelTwentySixMMPPariTrace011.c5_1,SmallLevelTwentySixMMPPariTrace011.c5_2,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm11] at hz11
  have h11_6 : SmallLevelTwentySixMMPPariTrace011.p6 x y z w a b u=0 := (mul_eq_zero.mp hz11).resolve_left (pow_ne_zero 2 hx)
  have he12:=SmallLevelTwentySixMMPPariTrace012.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink012P1.binding] at he12
  rw [h8_6] at he12
  rw [SmallLevelTwentySixMMPPariLink012P3.binding] at he12
  rw [h11_6] at he12
  have hp12 : SmallLevelTwentySixMMPPariTrace012.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace012.p6,SmallLevelTwentySixMMPPariTrace012.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp12] at he12
  have h12_4 : SmallLevelTwentySixMMPPariTrace012.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he12.symm
  have he13:=SmallLevelTwentySixMMPPariTrace013.identity_shift x y z w a b u
  have empty13_3 : SmallLevelTwentySixMMPPariTrace013.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace013.p3,SmallLevelTwentySixMMPPariTrace013.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty13_3] at he13
  rw [SmallLevelTwentySixMMPPariLink013P1.binding] at he13
  rw [h12_4] at he13
  have hp13 : SmallLevelTwentySixMMPPariTrace013.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace013.p4,SmallLevelTwentySixMMPPariTrace013.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp13] at he13
  have hz13 : (SmallLevelTwentySixMMPPariTrace013.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace013.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he13.symm
  have hm13 : SmallLevelTwentySixMMPPariTrace013.p5 x y z w a b u=x^1 := by
    simp only [SmallLevelTwentySixMMPPariTrace013.p5,SmallLevelTwentySixMMPPariTrace013.coefficients5,SmallLevelTwentySixMMPPariTrace013.c5_0,SmallLevelTwentySixMMPPariTrace013.c5_1,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm13] at hz13
  have h13_6 : SmallLevelTwentySixMMPPariTrace013.p6 x y z w a b u=0 := (mul_eq_zero.mp hz13).resolve_left (pow_ne_zero 1 hx)
  have he14:=SmallLevelTwentySixMMPPariTrace014.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink014P1.binding] at he14
  rw [hs0] at he14
  rw [SmallLevelTwentySixMMPPariLink014P3.binding] at he14
  rw [h13_6] at he14
  have hp14 : SmallLevelTwentySixMMPPariTrace014.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace014.p6,SmallLevelTwentySixMMPPariTrace014.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp14] at he14
  have h14_4 : SmallLevelTwentySixMMPPariTrace014.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he14.symm
  have he15:=SmallLevelTwentySixMMPPariTrace015.identity_shift x y z w a b u
  have empty15_3 : SmallLevelTwentySixMMPPariTrace015.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace015.p3,SmallLevelTwentySixMMPPariTrace015.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty15_3] at he15
  rw [SmallLevelTwentySixMMPPariLink015P1.binding] at he15
  rw [h14_4] at he15
  have hp15 : SmallLevelTwentySixMMPPariTrace015.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace015.p4,SmallLevelTwentySixMMPPariTrace015.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp15] at he15
  have hz15 : (SmallLevelTwentySixMMPPariTrace015.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace015.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he15.symm
  have hm15 : SmallLevelTwentySixMMPPariTrace015.p5 x y z w a b u=x^3 := by
    simp only [SmallLevelTwentySixMMPPariTrace015.p5,SmallLevelTwentySixMMPPariTrace015.coefficients5,SmallLevelTwentySixMMPPariTrace015.c5_0,SmallLevelTwentySixMMPPariTrace015.c5_1,SmallLevelTwentySixMMPPariTrace015.c5_2,SmallLevelTwentySixMMPPariTrace015.c5_3,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm15] at hz15
  have h15_6 : SmallLevelTwentySixMMPPariTrace015.p6 x y z w a b u=0 := (mul_eq_zero.mp hz15).resolve_left (pow_ne_zero 3 hx)
  have he16:=SmallLevelTwentySixMMPPariTrace016.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink016P1.binding] at he16
  rw [h15_6] at he16
  rw [SmallLevelTwentySixMMPPariLink016P3.binding] at he16
  rw [h2_6] at he16
  have hp16 : SmallLevelTwentySixMMPPariTrace016.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace016.p6,SmallLevelTwentySixMMPPariTrace016.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp16] at he16
  have h16_4 : SmallLevelTwentySixMMPPariTrace016.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he16.symm
  have he17:=SmallLevelTwentySixMMPPariTrace017.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink017P1.binding] at he17
  rw [h5_4] at he17
  rw [SmallLevelTwentySixMMPPariLink017P3.binding] at he17
  rw [h16_4] at he17
  have hp17 : SmallLevelTwentySixMMPPariTrace017.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace017.p6,SmallLevelTwentySixMMPPariTrace017.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp17] at he17
  have h17_4 : SmallLevelTwentySixMMPPariTrace017.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he17.symm
  have he18:=SmallLevelTwentySixMMPPariTrace018.identity x y z w a b u
  have empty18_3 : SmallLevelTwentySixMMPPariTrace018.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace018.p3,SmallLevelTwentySixMMPPariTrace018.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty18_3] at he18
  rw [SmallLevelTwentySixMMPPariLink018P1.binding] at he18
  rw [h17_4] at he18
  have hp18 : SmallLevelTwentySixMMPPariTrace018.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace018.p4,SmallLevelTwentySixMMPPariTrace018.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp18] at he18
  have hz18 : (SmallLevelTwentySixMMPPariTrace018.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace018.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he18.symm
  have hm18 : SmallLevelTwentySixMMPPariTrace018.p5 x y z w a b u=SmallLevelTwentySixMMPPari.c00 x y z w a b := by
    simp only [SmallLevelTwentySixMMPPariTrace018.p5,SmallLevelTwentySixMMPPariTrace018.coefficients5,SmallLevelTwentySixMMPPariTrace018.c5_0,SmallLevelTwentySixMMPPariTrace018.c5_1,SmallLevelTwentySixMMPPariTrace018.c5_2,SmallLevelTwentySixMMPPariTrace018.c5_3,SmallLevelPolynomialCoefficientCertificate.evaluate,SmallLevelTwentySixMMPPari.c00] <;> ring
  rw [hm18] at hz18
  have h18_6 : SmallLevelTwentySixMMPPariTrace018.p6 x y z w a b u=0 := (mul_eq_zero.mp hz18).resolve_left hc
  have h19_6 : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u=0 := by
    change SmallLevelTwentySixMMPPariTrace019.p1 x y z w a b u=0
    exact (SmallLevelTwentySixMMPPariLink019P1.binding x y z w a b u).trans h18_6
  exact h19_6
#print axioms first
end SmallLevelTwentySixMMPPariSourceChain
end
end

/-! ## SmallLevelTwentySixMMPPariSourceChainSecondV1 -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSourceChain
theorem second (x y z w a b u : ℂ) (hx : x≠0) (hx2 : x≠2)
    (hc : SmallLevelTwentySixMMPPari.c00 x y z w a b≠0)
    (hs0 : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=0)
    (hs1 : SmallLevelTwentySixMMPPariTrace001.p3 x y z w a b u=0)
    (hs2 : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=0)
    (hs3 : SmallLevelTwentySixMMPPariTrace003.p3 x y z w a b u=0)
    (hs4 : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=0)
    (hs5 : SmallLevelTwentySixMMPPariTrace007.p3 x y z w a b u=0)
    (hs6 : SmallLevelTwentySixMMPPariTrace009.p3 x y z w a b u=0)
    (hs7 : SmallLevelTwentySixMMPPariTrace021.p3 x y z w a b u=0)
    (h2_6 : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=0)
    (h5_4 : SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=0)
    (h8_6 : SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=0)
    : SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u=0 := by
  have h21_4 : SmallLevelTwentySixMMPPariTrace021.p4 x y z w a b u=0 := hs7
  have he22:=SmallLevelTwentySixMMPPariTrace022.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink022P1.binding] at he22
  rw [hs2] at he22
  rw [SmallLevelTwentySixMMPPariLink022P3.binding] at he22
  rw [h21_4] at he22
  have hp22 : SmallLevelTwentySixMMPPariTrace022.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace022.p6,SmallLevelTwentySixMMPPariTrace022.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp22] at he22
  have h22_4 : SmallLevelTwentySixMMPPariTrace022.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he22.symm
  have he23:=SmallLevelTwentySixMMPPariTrace023.identity_shift x y z w a b u
  have empty23_3 : SmallLevelTwentySixMMPPariTrace023.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace023.p3,SmallLevelTwentySixMMPPariTrace023.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty23_3] at he23
  rw [SmallLevelTwentySixMMPPariLink023P1.binding] at he23
  rw [h22_4] at he23
  have hp23 : SmallLevelTwentySixMMPPariTrace023.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace023.p4,SmallLevelTwentySixMMPPariTrace023.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp23] at he23
  have hz23 : (SmallLevelTwentySixMMPPariTrace023.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace023.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he23.symm
  have hm23 : SmallLevelTwentySixMMPPariTrace023.p5 x y z w a b u=x^1 := by
    simp only [SmallLevelTwentySixMMPPariTrace023.p5,SmallLevelTwentySixMMPPariTrace023.coefficients5,SmallLevelTwentySixMMPPariTrace023.c5_0,SmallLevelTwentySixMMPPariTrace023.c5_1,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm23] at hz23
  have h23_6 : SmallLevelTwentySixMMPPariTrace023.p6 x y z w a b u=0 := (mul_eq_zero.mp hz23).resolve_left (pow_ne_zero 1 hx)
  have he24:=SmallLevelTwentySixMMPPariTrace024.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink024P1.binding] at he24
  rw [h8_6] at he24
  rw [SmallLevelTwentySixMMPPariLink024P3.binding] at he24
  rw [h23_6] at he24
  have hp24 : SmallLevelTwentySixMMPPariTrace024.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace024.p6,SmallLevelTwentySixMMPPariTrace024.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp24] at he24
  have h24_4 : SmallLevelTwentySixMMPPariTrace024.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he24.symm
  have he25:=SmallLevelTwentySixMMPPariTrace025.identity_shift x y z w a b u
  have empty25_3 : SmallLevelTwentySixMMPPariTrace025.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace025.p3,SmallLevelTwentySixMMPPariTrace025.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty25_3] at he25
  rw [SmallLevelTwentySixMMPPariLink025P1.binding] at he25
  rw [h24_4] at he25
  have hp25 : SmallLevelTwentySixMMPPariTrace025.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace025.p4,SmallLevelTwentySixMMPPariTrace025.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp25] at he25
  have hz25 : (SmallLevelTwentySixMMPPariTrace025.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace025.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he25.symm
  have hm25 : SmallLevelTwentySixMMPPariTrace025.p5 x y z w a b u=x^2 := by
    simp only [SmallLevelTwentySixMMPPariTrace025.p5,SmallLevelTwentySixMMPPariTrace025.coefficients5,SmallLevelTwentySixMMPPariTrace025.c5_0,SmallLevelTwentySixMMPPariTrace025.c5_1,SmallLevelTwentySixMMPPariTrace025.c5_2,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm25] at hz25
  have h25_6 : SmallLevelTwentySixMMPPariTrace025.p6 x y z w a b u=0 := (mul_eq_zero.mp hz25).resolve_left (pow_ne_zero 2 hx)
  have he26:=SmallLevelTwentySixMMPPariTrace026.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink026P1.binding] at he26
  rw [hs0] at he26
  rw [SmallLevelTwentySixMMPPariLink026P3.binding] at he26
  rw [h25_6] at he26
  have hp26 : SmallLevelTwentySixMMPPariTrace026.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace026.p6,SmallLevelTwentySixMMPPariTrace026.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp26] at he26
  have h26_4 : SmallLevelTwentySixMMPPariTrace026.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he26.symm
  have he27:=SmallLevelTwentySixMMPPariTrace027.identity_shift x y z w a b u
  have empty27_3 : SmallLevelTwentySixMMPPariTrace027.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace027.p3,SmallLevelTwentySixMMPPariTrace027.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty27_3] at he27
  rw [SmallLevelTwentySixMMPPariLink027P1.binding] at he27
  rw [h26_4] at he27
  have hp27 : SmallLevelTwentySixMMPPariTrace027.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace027.p4,SmallLevelTwentySixMMPPariTrace027.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp27] at he27
  have hz27 : (SmallLevelTwentySixMMPPariTrace027.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace027.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he27.symm
  have hm27 : SmallLevelTwentySixMMPPariTrace027.p5 x y z w a b u=x^4 := by
    simp only [SmallLevelTwentySixMMPPariTrace027.p5,SmallLevelTwentySixMMPPariTrace027.coefficients5,SmallLevelTwentySixMMPPariTrace027.c5_0,SmallLevelTwentySixMMPPariTrace027.c5_1,SmallLevelTwentySixMMPPariTrace027.c5_2,SmallLevelTwentySixMMPPariTrace027.c5_3,SmallLevelTwentySixMMPPariTrace027.c5_4,SmallLevelPolynomialCoefficientCertificate.evaluate] <;> ring
  rw [hm27] at hz27
  have h27_6 : SmallLevelTwentySixMMPPariTrace027.p6 x y z w a b u=0 := (mul_eq_zero.mp hz27).resolve_left (pow_ne_zero 4 hx)
  have he28:=SmallLevelTwentySixMMPPariTrace028.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink028P1.binding] at he28
  rw [h27_6] at he28
  rw [SmallLevelTwentySixMMPPariLink028P3.binding] at he28
  rw [h2_6] at he28
  have hp28 : SmallLevelTwentySixMMPPariTrace028.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace028.p6,SmallLevelTwentySixMMPPariTrace028.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp28] at he28
  have h28_4 : SmallLevelTwentySixMMPPariTrace028.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he28.symm
  have he29:=SmallLevelTwentySixMMPPariTrace029.identity x y z w a b u
  rw [SmallLevelTwentySixMMPPariLink029P1.binding] at he29
  rw [h5_4] at he29
  rw [SmallLevelTwentySixMMPPariLink029P3.binding] at he29
  rw [h28_4] at he29
  have hp29 : SmallLevelTwentySixMMPPariTrace029.p6 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace029.p6,SmallLevelTwentySixMMPPariTrace029.coefficients6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp29] at he29
  have h29_4 : SmallLevelTwentySixMMPPariTrace029.p4 x y z w a b u=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he29.symm
  have he30:=SmallLevelTwentySixMMPPariTrace030.identity x y z w a b u
  have empty30_3 : SmallLevelTwentySixMMPPariTrace030.p3 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace030.p3,SmallLevelTwentySixMMPPariTrace030.coefficients3,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [empty30_3] at he30
  rw [SmallLevelTwentySixMMPPariLink030P1.binding] at he30
  rw [h29_4] at he30
  have hp30 : SmallLevelTwentySixMMPPariTrace030.p4 x y z w a b u=0 := by norm_num [SmallLevelTwentySixMMPPariTrace030.p4,SmallLevelTwentySixMMPPariTrace030.coefficients4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  rw [hp30] at he30
  have hz30 : (SmallLevelTwentySixMMPPariTrace030.p5 x y z w a b u)*(SmallLevelTwentySixMMPPariTrace030.p6 x y z w a b u)=0 := by
    simpa only [mul_zero,zero_mul,add_zero,zero_add] using he30.symm
  have hm30 : SmallLevelTwentySixMMPPariTrace030.p5 x y z w a b u=SmallLevelTwentySixMMPPari.c00 x y z w a b := by
    simp only [SmallLevelTwentySixMMPPariTrace030.p5,SmallLevelTwentySixMMPPariTrace030.coefficients5,SmallLevelTwentySixMMPPariTrace030.c5_0,SmallLevelTwentySixMMPPariTrace030.c5_1,SmallLevelTwentySixMMPPariTrace030.c5_2,SmallLevelTwentySixMMPPariTrace030.c5_3,SmallLevelPolynomialCoefficientCertificate.evaluate,SmallLevelTwentySixMMPPari.c00] <;> ring
  rw [hm30] at hz30
  have h30_6 : SmallLevelTwentySixMMPPariTrace030.p6 x y z w a b u=0 := (mul_eq_zero.mp hz30).resolve_left hc
  have h31_6 : SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u=0 := by
    change SmallLevelTwentySixMMPPariTrace031.p1 x y z w a b u=0
    exact (SmallLevelTwentySixMMPPariLink031P1.binding x y z w a b u).trans h30_6
  exact h31_6
#print axioms second
end SmallLevelTwentySixMMPPariSourceChain
end
end

/-! ## SmallLevelTwentySixMMPPariReducedEquationsV1 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSourceChain
open SmallLevelPolynomialCoefficientCertificate SmallLevelTwentySixMMPPari
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive
/-- Exact elimination consequence of the actual eight normalized scalar rows. -/
theorem reduced_equations (x y z w a b u : ℂ) (hx : x≠0) (hx2 : x≠2)
    (hc : c00 x y z w a b≠0)
    (hsmall : ∀ i : Fin 6,eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      (primitiveRows ⟨i.val,by omega⟩)=0)
    (h6 : constraint6 x y z w a b (fun j => if j=0 then 1 else u)=0)
    (h7 : constraint7 x y z w a b (fun j => if j=0 then 1 else u)=0) :
    SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u=0 ∧
    SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u=0 := by
  have hs0 : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=0 := by
    have h:=hsmall 0
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 0)=0 at h
    rw [small_row_0] at h
    rw [small_source_0]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs1 : SmallLevelTwentySixMMPPariTrace001.p3 x y z w a b u=0 := by
    have h:=hsmall 1
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 1)=0 at h
    rw [small_row_1] at h
    rw [small_source_1]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs2 : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=0 := by
    have h:=hsmall 2
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 2)=0 at h
    rw [small_row_2] at h
    rw [small_source_2]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs3 : SmallLevelTwentySixMMPPariTrace003.p3 x y z w a b u=0 := by
    have h:=hsmall 3
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 3)=0 at h
    rw [small_row_3] at h
    rw [small_source_3]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs4 : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=0 := by
    have h:=hsmall 4
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 4)=0 at h
    rw [small_row_4] at h
    rw [small_source_4]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs5 : SmallLevelTwentySixMMPPariTrace007.p3 x y z w a b u=0 := by
    have h:=hsmall 5
    change eval x y z w a b 1 (fun j => if j=0 then 1 else u) (primitiveRows 5)=0 at h
    rw [small_row_5] at h
    rw [small_source_5]
    simpa only [ite_true,ite_false,Nat.one_ne_zero,mul_one] using h
  have hs6 := (SmallLevelTwentySixMMPPariSourceBinding6.binding x y z w a b u).trans h6
  have hs7 := (SmallLevelTwentySixMMPPariSourceBinding7.binding x y z w a b u).trans h7
  obtain ⟨hq,hl,hw⟩ := initial x y z w a b u hx hx2 hc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  exact ⟨first x y z w a b u hx hx2 hc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hq hl hw,
    second x y z w a b u hx hx2 hc hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hq hl hw⟩
#print axioms reduced_equations
end SmallLevelTwentySixMMPPariSourceChain
end
end
