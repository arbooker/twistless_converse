module
public import SmallLevelTwentySixPariIdentity021XCoefficientCertificatesV1
public meta import SmallLevelCertificateBatchCommandV1
public import SmallLevelTwentySixPariIdentityIndexXDataSeriesV4
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

set_option Elab.async false
namespace SmallLevelTwentySixPariIdentity021X
open SmallLevelPolynomialCoefficientCertificate
certificate_batch {
theorem coefficient_0 (y z w a b u : ℂ) :
    (certificate y z w a b u)[0]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_0 y z w a b u))+0)+((c2_0 y z w a b u*(c3_0 y z w a b u))+0))+(((-1)*(c4_0 y z w a b u))+((-1)*(0))))) = some 0
  congr 1 <;> simp only [c0_0,c1_0,c2_0,c3_0,c4_0] <;> ring

#print axioms coefficient_0


theorem coefficient_1 (y z w a b u : ℂ) :
    (certificate y z w a b u)[1]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_1 y z w a b u))+((c0_1 y z w a b u*(c1_0 y z w a b u))+0))+((c2_0 y z w a b u*(c3_1 y z w a b u))+((c2_1 y z w a b u*(c3_0 y z w a b u))+0)))+((-1)*(c4_1 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1] <;> ring

#print axioms coefficient_1


theorem coefficient_2 (y z w a b u : ℂ) :
    (certificate y z w a b u)[2]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_2 y z w a b u))+((c0_1 y z w a b u*(c1_1 y z w a b u))+((c0_2 y z w a b u*(c1_0 y z w a b u))+0)))+((c2_0 y z w a b u*(c3_2 y z w a b u))+((c2_1 y z w a b u*(c3_1 y z w a b u))+((c2_2 y z w a b u*(c3_0 y z w a b u))+0))))+((-1)*(c4_2 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_2] <;> ring

#print axioms coefficient_2


theorem coefficient_3 (y z w a b u : ℂ) :
    (certificate y z w a b u)[3]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_3 y z w a b u))+((c0_1 y z w a b u*(c1_2 y z w a b u))+((c0_2 y z w a b u*(c1_1 y z w a b u))+((c0_3 y z w a b u*(c1_0 y z w a b u))+0))))+((c2_0 y z w a b u*(c3_3 y z w a b u))+((c2_1 y z w a b u*(c3_2 y z w a b u))+((c2_2 y z w a b u*(c3_1 y z w a b u))+((c2_3 y z w a b u*(c3_0 y z w a b u))+0)))))+((-1)*(c4_3 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_3] <;> ring

#print axioms coefficient_3


theorem coefficient_4 (y z w a b u : ℂ) :
    (certificate y z w a b u)[4]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_4 y z w a b u))+((c0_1 y z w a b u*(c1_3 y z w a b u))+((c0_2 y z w a b u*(c1_2 y z w a b u))+((c0_3 y z w a b u*(c1_1 y z w a b u))+((c0_4 y z w a b u*(c1_0 y z w a b u))+0)))))+((c2_0 y z w a b u*(c3_4 y z w a b u))+((c2_1 y z w a b u*(c3_3 y z w a b u))+((c2_2 y z w a b u*(c3_2 y z w a b u))+((c2_3 y z w a b u*(c3_1 y z w a b u))+((c2_4 y z w a b u*(c3_0 y z w a b u))+0))))))+((-1)*(c4_4 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_0,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c3_4,c4_4] <;> ring

#print axioms coefficient_4


theorem coefficient_5 (y z w a b u : ℂ) :
    (certificate y z w a b u)[5]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_5 y z w a b u))+((c0_1 y z w a b u*(c1_4 y z w a b u))+((c0_2 y z w a b u*(c1_3 y z w a b u))+((c0_3 y z w a b u*(c1_2 y z w a b u))+((c0_4 y z w a b u*(c1_1 y z w a b u))+((c0_5 y z w a b u*(c1_0 y z w a b u))+0))))))+((c2_0 y z w a b u*(c3_5 y z w a b u))+((c2_1 y z w a b u*(c3_4 y z w a b u))+((c2_2 y z w a b u*(c3_3 y z w a b u))+((c2_3 y z w a b u*(c3_2 y z w a b u))+((c2_4 y z w a b u*(c3_1 y z w a b u))+((c2_5 y z w a b u*(c3_0 y z w a b u))+0)))))))+((-1)*(c4_5 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c4_5] <;> ring

#print axioms coefficient_5


theorem coefficient_6 (y z w a b u : ℂ) :
    (certificate y z w a b u)[6]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_6 y z w a b u))+((c0_1 y z w a b u*(c1_5 y z w a b u))+((c0_2 y z w a b u*(c1_4 y z w a b u))+((c0_3 y z w a b u*(c1_3 y z w a b u))+((c0_4 y z w a b u*(c1_2 y z w a b u))+((c0_5 y z w a b u*(c1_1 y z w a b u))+((c0_6 y z w a b u*(c1_0 y z w a b u))+0)))))))+((c2_0 y z w a b u*(c3_6 y z w a b u))+((c2_1 y z w a b u*(c3_5 y z w a b u))+((c2_2 y z w a b u*(c3_4 y z w a b u))+((c2_3 y z w a b u*(c3_3 y z w a b u))+((c2_4 y z w a b u*(c3_2 y z w a b u))+((c2_5 y z w a b u*(c3_1 y z w a b u))+((c2_6 y z w a b u*(c3_0 y z w a b u))+0))))))))+((-1)*(c4_6 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c4_6] <;> ring

#print axioms coefficient_6


theorem coefficient_7 (y z w a b u : ℂ) :
    (certificate y z w a b u)[7]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_7 y z w a b u))+((c0_1 y z w a b u*(c1_6 y z w a b u))+((c0_2 y z w a b u*(c1_5 y z w a b u))+((c0_3 y z w a b u*(c1_4 y z w a b u))+((c0_4 y z w a b u*(c1_3 y z w a b u))+((c0_5 y z w a b u*(c1_2 y z w a b u))+((c0_6 y z w a b u*(c1_1 y z w a b u))+((c0_7 y z w a b u*(c1_0 y z w a b u))+0))))))))+((c2_0 y z w a b u*(c3_7 y z w a b u))+((c2_1 y z w a b u*(c3_6 y z w a b u))+((c2_2 y z w a b u*(c3_5 y z w a b u))+((c2_3 y z w a b u*(c3_4 y z w a b u))+((c2_4 y z w a b u*(c3_3 y z w a b u))+((c2_5 y z w a b u*(c3_2 y z w a b u))+((c2_6 y z w a b u*(c3_1 y z w a b u))+((c2_7 y z w a b u*(c3_0 y z w a b u))+0)))))))))+((-1)*(c4_7 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c4_7] <;> ring

#print axioms coefficient_7


theorem coefficient_8 (y z w a b u : ℂ) :
    (certificate y z w a b u)[8]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_8 y z w a b u))+((c0_1 y z w a b u*(c1_7 y z w a b u))+((c0_2 y z w a b u*(c1_6 y z w a b u))+((c0_3 y z w a b u*(c1_5 y z w a b u))+((c0_4 y z w a b u*(c1_4 y z w a b u))+((c0_5 y z w a b u*(c1_3 y z w a b u))+((c0_6 y z w a b u*(c1_2 y z w a b u))+((c0_7 y z w a b u*(c1_1 y z w a b u))+((c0_8 y z w a b u*(c1_0 y z w a b u))+0)))))))))+((c2_0 y z w a b u*(c3_8 y z w a b u))+((c2_1 y z w a b u*(c3_7 y z w a b u))+((c2_2 y z w a b u*(c3_6 y z w a b u))+((c2_3 y z w a b u*(c3_5 y z w a b u))+((c2_4 y z w a b u*(c3_4 y z w a b u))+((c2_5 y z w a b u*(c3_3 y z w a b u))+((c2_6 y z w a b u*(c3_2 y z w a b u))+((c2_7 y z w a b u*(c3_1 y z w a b u))+((c2_8 y z w a b u*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_8 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c4_8] <;> ring

#print axioms coefficient_8


theorem coefficient_9 (y z w a b u : ℂ) :
    (certificate y z w a b u)[9]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_9 y z w a b u))+((c0_1 y z w a b u*(c1_8 y z w a b u))+((c0_2 y z w a b u*(c1_7 y z w a b u))+((c0_3 y z w a b u*(c1_6 y z w a b u))+((c0_4 y z w a b u*(c1_5 y z w a b u))+((c0_5 y z w a b u*(c1_4 y z w a b u))+((c0_6 y z w a b u*(c1_3 y z w a b u))+((c0_7 y z w a b u*(c1_2 y z w a b u))+((c0_8 y z w a b u*(c1_1 y z w a b u))+((c0_9 y z w a b u*(c1_0 y z w a b u))+0))))))))))+((c2_0 y z w a b u*(c3_9 y z w a b u))+((c2_1 y z w a b u*(c3_8 y z w a b u))+((c2_2 y z w a b u*(c3_7 y z w a b u))+((c2_3 y z w a b u*(c3_6 y z w a b u))+((c2_4 y z w a b u*(c3_5 y z w a b u))+((c2_5 y z w a b u*(c3_4 y z w a b u))+((c2_6 y z w a b u*(c3_3 y z w a b u))+((c2_7 y z w a b u*(c3_2 y z w a b u))+((c2_8 y z w a b u*(c3_1 y z w a b u))+((c2_9 y z w a b u*(c3_0 y z w a b u))+0)))))))))))+((-1)*(c4_9 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_9] <;> ring

#print axioms coefficient_9


theorem coefficient_10 (y z w a b u : ℂ) :
    (certificate y z w a b u)[10]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_10 y z w a b u))+((c0_1 y z w a b u*(c1_9 y z w a b u))+((c0_2 y z w a b u*(c1_8 y z w a b u))+((c0_3 y z w a b u*(c1_7 y z w a b u))+((c0_4 y z w a b u*(c1_6 y z w a b u))+((c0_5 y z w a b u*(c1_5 y z w a b u))+((c0_6 y z w a b u*(c1_4 y z w a b u))+((c0_7 y z w a b u*(c1_3 y z w a b u))+((c0_8 y z w a b u*(c1_2 y z w a b u))+(c0_9 y z w a b u*(c1_1 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_10 y z w a b u))+((c2_1 y z w a b u*(c3_9 y z w a b u))+((c2_2 y z w a b u*(c3_8 y z w a b u))+((c2_3 y z w a b u*(c3_7 y z w a b u))+((c2_4 y z w a b u*(c3_6 y z w a b u))+((c2_5 y z w a b u*(c3_5 y z w a b u))+((c2_6 y z w a b u*(c3_4 y z w a b u))+((c2_7 y z w a b u*(c3_3 y z w a b u))+((c2_8 y z w a b u*(c3_2 y z w a b u))+((c2_9 y z w a b u*(c3_1 y z w a b u))+((c2_10 y z w a b u*(c3_0 y z w a b u))+0))))))))))))+((-1)*(c4_10 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_1,c1_10,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_10] <;> ring

#print axioms coefficient_10


theorem coefficient_11 (y z w a b u : ℂ) :
    (certificate y z w a b u)[11]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_11 y z w a b u))+((c0_1 y z w a b u*(c1_10 y z w a b u))+((c0_2 y z w a b u*(c1_9 y z w a b u))+((c0_3 y z w a b u*(c1_8 y z w a b u))+((c0_4 y z w a b u*(c1_7 y z w a b u))+((c0_5 y z w a b u*(c1_6 y z w a b u))+((c0_6 y z w a b u*(c1_5 y z w a b u))+((c0_7 y z w a b u*(c1_4 y z w a b u))+((c0_8 y z w a b u*(c1_3 y z w a b u))+(c0_9 y z w a b u*(c1_2 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_11 y z w a b u))+((c2_1 y z w a b u*(c3_10 y z w a b u))+((c2_2 y z w a b u*(c3_9 y z w a b u))+((c2_3 y z w a b u*(c3_8 y z w a b u))+((c2_4 y z w a b u*(c3_7 y z w a b u))+((c2_5 y z w a b u*(c3_6 y z w a b u))+((c2_6 y z w a b u*(c3_5 y z w a b u))+((c2_7 y z w a b u*(c3_4 y z w a b u))+((c2_8 y z w a b u*(c3_3 y z w a b u))+((c2_9 y z w a b u*(c3_2 y z w a b u))+((c2_10 y z w a b u*(c3_1 y z w a b u))+((c2_11 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))+((-1)*(c4_11 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_11] <;> ring

#print axioms coefficient_11


theorem coefficient_12 (y z w a b u : ℂ) :
    (certificate y z w a b u)[12]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_12 y z w a b u))+((c0_1 y z w a b u*(c1_11 y z w a b u))+((c0_2 y z w a b u*(c1_10 y z w a b u))+((c0_3 y z w a b u*(c1_9 y z w a b u))+((c0_4 y z w a b u*(c1_8 y z w a b u))+((c0_5 y z w a b u*(c1_7 y z w a b u))+((c0_6 y z w a b u*(c1_6 y z w a b u))+((c0_7 y z w a b u*(c1_5 y z w a b u))+((c0_8 y z w a b u*(c1_4 y z w a b u))+(c0_9 y z w a b u*(c1_3 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_12 y z w a b u))+((c2_1 y z w a b u*(c3_11 y z w a b u))+((c2_2 y z w a b u*(c3_10 y z w a b u))+((c2_3 y z w a b u*(c3_9 y z w a b u))+((c2_4 y z w a b u*(c3_8 y z w a b u))+((c2_5 y z w a b u*(c3_7 y z w a b u))+((c2_6 y z w a b u*(c3_6 y z w a b u))+((c2_7 y z w a b u*(c3_5 y z w a b u))+((c2_8 y z w a b u*(c3_4 y z w a b u))+((c2_9 y z w a b u*(c3_3 y z w a b u))+((c2_10 y z w a b u*(c3_2 y z w a b u))+((c2_11 y z w a b u*(c3_1 y z w a b u))+((c2_12 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))+((-1)*(c4_12 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_3,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_12] <;> ring

#print axioms coefficient_12


theorem coefficient_13 (y z w a b u : ℂ) :
    (certificate y z w a b u)[13]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_13 y z w a b u))+((c0_1 y z w a b u*(c1_12 y z w a b u))+((c0_2 y z w a b u*(c1_11 y z w a b u))+((c0_3 y z w a b u*(c1_10 y z w a b u))+((c0_4 y z w a b u*(c1_9 y z w a b u))+((c0_5 y z w a b u*(c1_8 y z w a b u))+((c0_6 y z w a b u*(c1_7 y z w a b u))+((c0_7 y z w a b u*(c1_6 y z w a b u))+((c0_8 y z w a b u*(c1_5 y z w a b u))+(c0_9 y z w a b u*(c1_4 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_13 y z w a b u))+((c2_1 y z w a b u*(c3_12 y z w a b u))+((c2_2 y z w a b u*(c3_11 y z w a b u))+((c2_3 y z w a b u*(c3_10 y z w a b u))+((c2_4 y z w a b u*(c3_9 y z w a b u))+((c2_5 y z w a b u*(c3_8 y z w a b u))+((c2_6 y z w a b u*(c3_7 y z w a b u))+((c2_7 y z w a b u*(c3_6 y z w a b u))+((c2_8 y z w a b u*(c3_5 y z w a b u))+((c2_9 y z w a b u*(c3_4 y z w a b u))+((c2_10 y z w a b u*(c3_3 y z w a b u))+((c2_11 y z w a b u*(c3_2 y z w a b u))+((c2_12 y z w a b u*(c3_1 y z w a b u))+((c2_13 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))+((-1)*(c4_13 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_13] <;> ring

#print axioms coefficient_13


theorem coefficient_14 (y z w a b u : ℂ) :
    (certificate y z w a b u)[14]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_14 y z w a b u))+((c0_1 y z w a b u*(c1_13 y z w a b u))+((c0_2 y z w a b u*(c1_12 y z w a b u))+((c0_3 y z w a b u*(c1_11 y z w a b u))+((c0_4 y z w a b u*(c1_10 y z w a b u))+((c0_5 y z w a b u*(c1_9 y z w a b u))+((c0_6 y z w a b u*(c1_8 y z w a b u))+((c0_7 y z w a b u*(c1_7 y z w a b u))+((c0_8 y z w a b u*(c1_6 y z w a b u))+(c0_9 y z w a b u*(c1_5 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_14 y z w a b u))+((c2_1 y z w a b u*(c3_13 y z w a b u))+((c2_2 y z w a b u*(c3_12 y z w a b u))+((c2_3 y z w a b u*(c3_11 y z w a b u))+((c2_4 y z w a b u*(c3_10 y z w a b u))+((c2_5 y z w a b u*(c3_9 y z w a b u))+((c2_6 y z w a b u*(c3_8 y z w a b u))+((c2_7 y z w a b u*(c3_7 y z w a b u))+((c2_8 y z w a b u*(c3_6 y z w a b u))+((c2_9 y z w a b u*(c3_5 y z w a b u))+((c2_10 y z w a b u*(c3_4 y z w a b u))+((c2_11 y z w a b u*(c3_3 y z w a b u))+((c2_12 y z w a b u*(c3_2 y z w a b u))+((c2_13 y z w a b u*(c3_1 y z w a b u))+((c2_14 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))+((-1)*(c4_14 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_14] <;> ring

#print axioms coefficient_14


theorem coefficient_15 (y z w a b u : ℂ) :
    (certificate y z w a b u)[15]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_15 y z w a b u))+((c0_1 y z w a b u*(c1_14 y z w a b u))+((c0_2 y z w a b u*(c1_13 y z w a b u))+((c0_3 y z w a b u*(c1_12 y z w a b u))+((c0_4 y z w a b u*(c1_11 y z w a b u))+((c0_5 y z w a b u*(c1_10 y z w a b u))+((c0_6 y z w a b u*(c1_9 y z w a b u))+((c0_7 y z w a b u*(c1_8 y z w a b u))+((c0_8 y z w a b u*(c1_7 y z w a b u))+(c0_9 y z w a b u*(c1_6 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_15 y z w a b u))+((c2_1 y z w a b u*(c3_14 y z w a b u))+((c2_2 y z w a b u*(c3_13 y z w a b u))+((c2_3 y z w a b u*(c3_12 y z w a b u))+((c2_4 y z w a b u*(c3_11 y z w a b u))+((c2_5 y z w a b u*(c3_10 y z w a b u))+((c2_6 y z w a b u*(c3_9 y z w a b u))+((c2_7 y z w a b u*(c3_8 y z w a b u))+((c2_8 y z w a b u*(c3_7 y z w a b u))+((c2_9 y z w a b u*(c3_6 y z w a b u))+((c2_10 y z w a b u*(c3_5 y z w a b u))+((c2_11 y z w a b u*(c3_4 y z w a b u))+((c2_12 y z w a b u*(c3_3 y z w a b u))+((c2_13 y z w a b u*(c3_2 y z w a b u))+((c2_14 y z w a b u*(c3_1 y z w a b u))+((c2_15 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))+((-1)*(c4_15 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_15] <;> ring

#print axioms coefficient_15


theorem coefficient_16 (y z w a b u : ℂ) :
    (certificate y z w a b u)[16]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_16 y z w a b u))+((c0_1 y z w a b u*(c1_15 y z w a b u))+((c0_2 y z w a b u*(c1_14 y z w a b u))+((c0_3 y z w a b u*(c1_13 y z w a b u))+((c0_4 y z w a b u*(c1_12 y z w a b u))+((c0_5 y z w a b u*(c1_11 y z w a b u))+((c0_6 y z w a b u*(c1_10 y z w a b u))+((c0_7 y z w a b u*(c1_9 y z w a b u))+((c0_8 y z w a b u*(c1_8 y z w a b u))+(c0_9 y z w a b u*(c1_7 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_16 y z w a b u))+((c2_1 y z w a b u*(c3_15 y z w a b u))+((c2_2 y z w a b u*(c3_14 y z w a b u))+((c2_3 y z w a b u*(c3_13 y z w a b u))+((c2_4 y z w a b u*(c3_12 y z w a b u))+((c2_5 y z w a b u*(c3_11 y z w a b u))+((c2_6 y z w a b u*(c3_10 y z w a b u))+((c2_7 y z w a b u*(c3_9 y z w a b u))+((c2_8 y z w a b u*(c3_8 y z w a b u))+((c2_9 y z w a b u*(c3_7 y z w a b u))+((c2_10 y z w a b u*(c3_6 y z w a b u))+((c2_11 y z w a b u*(c3_5 y z w a b u))+((c2_12 y z w a b u*(c3_4 y z w a b u))+((c2_13 y z w a b u*(c3_3 y z w a b u))+((c2_14 y z w a b u*(c3_2 y z w a b u))+((c2_15 y z w a b u*(c3_1 y z w a b u))+((c2_16 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))+((-1)*(c4_16 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_7,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_16] <;> ring

#print axioms coefficient_16


theorem coefficient_17 (y z w a b u : ℂ) :
    (certificate y z w a b u)[17]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_17 y z w a b u))+((c0_1 y z w a b u*(c1_16 y z w a b u))+((c0_2 y z w a b u*(c1_15 y z w a b u))+((c0_3 y z w a b u*(c1_14 y z w a b u))+((c0_4 y z w a b u*(c1_13 y z w a b u))+((c0_5 y z w a b u*(c1_12 y z w a b u))+((c0_6 y z w a b u*(c1_11 y z w a b u))+((c0_7 y z w a b u*(c1_10 y z w a b u))+((c0_8 y z w a b u*(c1_9 y z w a b u))+(c0_9 y z w a b u*(c1_8 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_17 y z w a b u))+((c2_1 y z w a b u*(c3_16 y z w a b u))+((c2_2 y z w a b u*(c3_15 y z w a b u))+((c2_3 y z w a b u*(c3_14 y z w a b u))+((c2_4 y z w a b u*(c3_13 y z w a b u))+((c2_5 y z w a b u*(c3_12 y z w a b u))+((c2_6 y z w a b u*(c3_11 y z w a b u))+((c2_7 y z w a b u*(c3_10 y z w a b u))+((c2_8 y z w a b u*(c3_9 y z w a b u))+((c2_9 y z w a b u*(c3_8 y z w a b u))+((c2_10 y z w a b u*(c3_7 y z w a b u))+((c2_11 y z w a b u*(c3_6 y z w a b u))+((c2_12 y z w a b u*(c3_5 y z w a b u))+((c2_13 y z w a b u*(c3_4 y z w a b u))+((c2_14 y z w a b u*(c3_3 y z w a b u))+((c2_15 y z w a b u*(c3_2 y z w a b u))+((c2_16 y z w a b u*(c3_1 y z w a b u))+((c2_17 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))+((-1)*(c4_17 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17,c1_8,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_17] <;> ring

#print axioms coefficient_17


theorem coefficient_18 (y z w a b u : ℂ) :
    (certificate y z w a b u)[18]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_18 y z w a b u))+((c0_1 y z w a b u*(c1_17 y z w a b u))+((c0_2 y z w a b u*(c1_16 y z w a b u))+((c0_3 y z w a b u*(c1_15 y z w a b u))+((c0_4 y z w a b u*(c1_14 y z w a b u))+((c0_5 y z w a b u*(c1_13 y z w a b u))+((c0_6 y z w a b u*(c1_12 y z w a b u))+((c0_7 y z w a b u*(c1_11 y z w a b u))+((c0_8 y z w a b u*(c1_10 y z w a b u))+(c0_9 y z w a b u*(c1_9 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_18 y z w a b u))+((c2_1 y z w a b u*(c3_17 y z w a b u))+((c2_2 y z w a b u*(c3_16 y z w a b u))+((c2_3 y z w a b u*(c3_15 y z w a b u))+((c2_4 y z w a b u*(c3_14 y z w a b u))+((c2_5 y z w a b u*(c3_13 y z w a b u))+((c2_6 y z w a b u*(c3_12 y z w a b u))+((c2_7 y z w a b u*(c3_11 y z w a b u))+((c2_8 y z w a b u*(c3_10 y z w a b u))+((c2_9 y z w a b u*(c3_9 y z w a b u))+((c2_10 y z w a b u*(c3_8 y z w a b u))+((c2_11 y z w a b u*(c3_7 y z w a b u))+((c2_12 y z w a b u*(c3_6 y z w a b u))+((c2_13 y z w a b u*(c3_5 y z w a b u))+((c2_14 y z w a b u*(c3_4 y z w a b u))+((c2_15 y z w a b u*(c3_3 y z w a b u))+((c2_16 y z w a b u*(c3_2 y z w a b u))+((c2_17 y z w a b u*(c3_1 y z w a b u))+((c2_18 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))))+((-1)*(c4_18 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17,c1_18,c1_9,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_18] <;> ring

#print axioms coefficient_18


theorem coefficient_19 (y z w a b u : ℂ) :
    (certificate y z w a b u)[19]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_19 y z w a b u))+((c0_1 y z w a b u*(c1_18 y z w a b u))+((c0_2 y z w a b u*(c1_17 y z w a b u))+((c0_3 y z w a b u*(c1_16 y z w a b u))+((c0_4 y z w a b u*(c1_15 y z w a b u))+((c0_5 y z w a b u*(c1_14 y z w a b u))+((c0_6 y z w a b u*(c1_13 y z w a b u))+((c0_7 y z w a b u*(c1_12 y z w a b u))+((c0_8 y z w a b u*(c1_11 y z w a b u))+(c0_9 y z w a b u*(c1_10 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_19 y z w a b u))+((c2_1 y z w a b u*(c3_18 y z w a b u))+((c2_2 y z w a b u*(c3_17 y z w a b u))+((c2_3 y z w a b u*(c3_16 y z w a b u))+((c2_4 y z w a b u*(c3_15 y z w a b u))+((c2_5 y z w a b u*(c3_14 y z w a b u))+((c2_6 y z w a b u*(c3_13 y z w a b u))+((c2_7 y z w a b u*(c3_12 y z w a b u))+((c2_8 y z w a b u*(c3_11 y z w a b u))+((c2_9 y z w a b u*(c3_10 y z w a b u))+((c2_10 y z w a b u*(c3_9 y z w a b u))+((c2_11 y z w a b u*(c3_8 y z w a b u))+((c2_12 y z w a b u*(c3_7 y z w a b u))+((c2_13 y z w a b u*(c3_6 y z w a b u))+((c2_14 y z w a b u*(c3_5 y z w a b u))+((c2_15 y z w a b u*(c3_4 y z w a b u))+((c2_16 y z w a b u*(c3_3 y z w a b u))+((c2_17 y z w a b u*(c3_2 y z w a b u))+((c2_18 y z w a b u*(c3_1 y z w a b u))+((c2_19 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))))+((-1)*(c4_19 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_10,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17,c1_18,c1_19,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_19] <;> ring

#print axioms coefficient_19


theorem coefficient_20 (y z w a b u : ℂ) :
    (certificate y z w a b u)[20]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_20 y z w a b u))+((c0_1 y z w a b u*(c1_19 y z w a b u))+((c0_2 y z w a b u*(c1_18 y z w a b u))+((c0_3 y z w a b u*(c1_17 y z w a b u))+((c0_4 y z w a b u*(c1_16 y z w a b u))+((c0_5 y z w a b u*(c1_15 y z w a b u))+((c0_6 y z w a b u*(c1_14 y z w a b u))+((c0_7 y z w a b u*(c1_13 y z w a b u))+((c0_8 y z w a b u*(c1_12 y z w a b u))+(c0_9 y z w a b u*(c1_11 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_20 y z w a b u))+((c2_1 y z w a b u*(c3_19 y z w a b u))+((c2_2 y z w a b u*(c3_18 y z w a b u))+((c2_3 y z w a b u*(c3_17 y z w a b u))+((c2_4 y z w a b u*(c3_16 y z w a b u))+((c2_5 y z w a b u*(c3_15 y z w a b u))+((c2_6 y z w a b u*(c3_14 y z w a b u))+((c2_7 y z w a b u*(c3_13 y z w a b u))+((c2_8 y z w a b u*(c3_12 y z w a b u))+((c2_9 y z w a b u*(c3_11 y z w a b u))+((c2_10 y z w a b u*(c3_10 y z w a b u))+((c2_11 y z w a b u*(c3_9 y z w a b u))+((c2_12 y z w a b u*(c3_8 y z w a b u))+((c2_13 y z w a b u*(c3_7 y z w a b u))+((c2_14 y z w a b u*(c3_6 y z w a b u))+((c2_15 y z w a b u*(c3_5 y z w a b u))+((c2_16 y z w a b u*(c3_4 y z w a b u))+((c2_17 y z w a b u*(c3_3 y z w a b u))+((c2_18 y z w a b u*(c3_2 y z w a b u))+((c2_19 y z w a b u*(c3_1 y z w a b u))+((c2_20 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))))))+((-1)*(c4_20 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_11,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17,c1_18,c1_19,c1_20,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_20] <;> ring

#print axioms coefficient_20


theorem coefficient_21 (y z w a b u : ℂ) :
    (certificate y z w a b u)[21]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_21 y z w a b u))+((c0_1 y z w a b u*(c1_20 y z w a b u))+((c0_2 y z w a b u*(c1_19 y z w a b u))+((c0_3 y z w a b u*(c1_18 y z w a b u))+((c0_4 y z w a b u*(c1_17 y z w a b u))+((c0_5 y z w a b u*(c1_16 y z w a b u))+((c0_6 y z w a b u*(c1_15 y z w a b u))+((c0_7 y z w a b u*(c1_14 y z w a b u))+((c0_8 y z w a b u*(c1_13 y z w a b u))+(c0_9 y z w a b u*(c1_12 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_21 y z w a b u))+((c2_1 y z w a b u*(c3_20 y z w a b u))+((c2_2 y z w a b u*(c3_19 y z w a b u))+((c2_3 y z w a b u*(c3_18 y z w a b u))+((c2_4 y z w a b u*(c3_17 y z w a b u))+((c2_5 y z w a b u*(c3_16 y z w a b u))+((c2_6 y z w a b u*(c3_15 y z w a b u))+((c2_7 y z w a b u*(c3_14 y z w a b u))+((c2_8 y z w a b u*(c3_13 y z w a b u))+((c2_9 y z w a b u*(c3_12 y z w a b u))+((c2_10 y z w a b u*(c3_11 y z w a b u))+((c2_11 y z w a b u*(c3_10 y z w a b u))+((c2_12 y z w a b u*(c3_9 y z w a b u))+((c2_13 y z w a b u*(c3_8 y z w a b u))+((c2_14 y z w a b u*(c3_7 y z w a b u))+((c2_15 y z w a b u*(c3_6 y z w a b u))+((c2_16 y z w a b u*(c3_5 y z w a b u))+((c2_17 y z w a b u*(c3_4 y z w a b u))+((c2_18 y z w a b u*(c3_3 y z w a b u))+((c2_19 y z w a b u*(c3_2 y z w a b u))+((c2_20 y z w a b u*(c3_1 y z w a b u))+((c2_21 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))))))+((-1)*(c4_21 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_12,c1_13,c1_14,c1_15,c1_16,c1_17,c1_18,c1_19,c1_20,c1_21,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_21] <;> ring

#print axioms coefficient_21


theorem coefficient_22 (y z w a b u : ℂ) :
    (certificate y z w a b u)[22]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_22 y z w a b u))+((c0_1 y z w a b u*(c1_21 y z w a b u))+((c0_2 y z w a b u*(c1_20 y z w a b u))+((c0_3 y z w a b u*(c1_19 y z w a b u))+((c0_4 y z w a b u*(c1_18 y z w a b u))+((c0_5 y z w a b u*(c1_17 y z w a b u))+((c0_6 y z w a b u*(c1_16 y z w a b u))+((c0_7 y z w a b u*(c1_15 y z w a b u))+((c0_8 y z w a b u*(c1_14 y z w a b u))+(c0_9 y z w a b u*(c1_13 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_22 y z w a b u))+((c2_1 y z w a b u*(c3_21 y z w a b u))+((c2_2 y z w a b u*(c3_20 y z w a b u))+((c2_3 y z w a b u*(c3_19 y z w a b u))+((c2_4 y z w a b u*(c3_18 y z w a b u))+((c2_5 y z w a b u*(c3_17 y z w a b u))+((c2_6 y z w a b u*(c3_16 y z w a b u))+((c2_7 y z w a b u*(c3_15 y z w a b u))+((c2_8 y z w a b u*(c3_14 y z w a b u))+((c2_9 y z w a b u*(c3_13 y z w a b u))+((c2_10 y z w a b u*(c3_12 y z w a b u))+((c2_11 y z w a b u*(c3_11 y z w a b u))+((c2_12 y z w a b u*(c3_10 y z w a b u))+((c2_13 y z w a b u*(c3_9 y z w a b u))+((c2_14 y z w a b u*(c3_8 y z w a b u))+((c2_15 y z w a b u*(c3_7 y z w a b u))+((c2_16 y z w a b u*(c3_6 y z w a b u))+((c2_17 y z w a b u*(c3_5 y z w a b u))+((c2_18 y z w a b u*(c3_4 y z w a b u))+((c2_19 y z w a b u*(c3_3 y z w a b u))+((c2_20 y z w a b u*(c3_2 y z w a b u))+((c2_21 y z w a b u*(c3_1 y z w a b u))+((c2_22 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))))))))+((-1)*(c4_22 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_13,c1_14,c1_15,c1_16,c1_17,c1_18,c1_19,c1_20,c1_21,c1_22,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_22] <;> ring

#print axioms coefficient_22


theorem coefficient_23 (y z w a b u : ℂ) :
    (certificate y z w a b u)[23]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_23 y z w a b u))+((c0_1 y z w a b u*(c1_22 y z w a b u))+((c0_2 y z w a b u*(c1_21 y z w a b u))+((c0_3 y z w a b u*(c1_20 y z w a b u))+((c0_4 y z w a b u*(c1_19 y z w a b u))+((c0_5 y z w a b u*(c1_18 y z w a b u))+((c0_6 y z w a b u*(c1_17 y z w a b u))+((c0_7 y z w a b u*(c1_16 y z w a b u))+((c0_8 y z w a b u*(c1_15 y z w a b u))+(c0_9 y z w a b u*(c1_14 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_23 y z w a b u))+((c2_1 y z w a b u*(c3_22 y z w a b u))+((c2_2 y z w a b u*(c3_21 y z w a b u))+((c2_3 y z w a b u*(c3_20 y z w a b u))+((c2_4 y z w a b u*(c3_19 y z w a b u))+((c2_5 y z w a b u*(c3_18 y z w a b u))+((c2_6 y z w a b u*(c3_17 y z w a b u))+((c2_7 y z w a b u*(c3_16 y z w a b u))+((c2_8 y z w a b u*(c3_15 y z w a b u))+((c2_9 y z w a b u*(c3_14 y z w a b u))+((c2_10 y z w a b u*(c3_13 y z w a b u))+((c2_11 y z w a b u*(c3_12 y z w a b u))+((c2_12 y z w a b u*(c3_11 y z w a b u))+((c2_13 y z w a b u*(c3_10 y z w a b u))+((c2_14 y z w a b u*(c3_9 y z w a b u))+((c2_15 y z w a b u*(c3_8 y z w a b u))+((c2_16 y z w a b u*(c3_7 y z w a b u))+((c2_17 y z w a b u*(c3_6 y z w a b u))+((c2_18 y z w a b u*(c3_5 y z w a b u))+((c2_19 y z w a b u*(c3_4 y z w a b u))+((c2_20 y z w a b u*(c3_3 y z w a b u))+((c2_21 y z w a b u*(c3_2 y z w a b u))+((c2_22 y z w a b u*(c3_1 y z w a b u))+((c2_23 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))))))))+((-1)*(c4_23 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_14,c1_15,c1_16,c1_17,c1_18,c1_19,c1_20,c1_21,c1_22,c1_23,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_23,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_23,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_23] <;> ring

#print axioms coefficient_23


theorem coefficient_24 (y z w a b u : ℂ) :
    (certificate y z w a b u)[24]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_24 y z w a b u))+((c0_1 y z w a b u*(c1_23 y z w a b u))+((c0_2 y z w a b u*(c1_22 y z w a b u))+((c0_3 y z w a b u*(c1_21 y z w a b u))+((c0_4 y z w a b u*(c1_20 y z w a b u))+((c0_5 y z w a b u*(c1_19 y z w a b u))+((c0_6 y z w a b u*(c1_18 y z w a b u))+((c0_7 y z w a b u*(c1_17 y z w a b u))+((c0_8 y z w a b u*(c1_16 y z w a b u))+(c0_9 y z w a b u*(c1_15 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_24 y z w a b u))+((c2_1 y z w a b u*(c3_23 y z w a b u))+((c2_2 y z w a b u*(c3_22 y z w a b u))+((c2_3 y z w a b u*(c3_21 y z w a b u))+((c2_4 y z w a b u*(c3_20 y z w a b u))+((c2_5 y z w a b u*(c3_19 y z w a b u))+((c2_6 y z w a b u*(c3_18 y z w a b u))+((c2_7 y z w a b u*(c3_17 y z w a b u))+((c2_8 y z w a b u*(c3_16 y z w a b u))+((c2_9 y z w a b u*(c3_15 y z w a b u))+((c2_10 y z w a b u*(c3_14 y z w a b u))+((c2_11 y z w a b u*(c3_13 y z w a b u))+((c2_12 y z w a b u*(c3_12 y z w a b u))+((c2_13 y z w a b u*(c3_11 y z w a b u))+((c2_14 y z w a b u*(c3_10 y z w a b u))+((c2_15 y z w a b u*(c3_9 y z w a b u))+((c2_16 y z w a b u*(c3_8 y z w a b u))+((c2_17 y z w a b u*(c3_7 y z w a b u))+((c2_18 y z w a b u*(c3_6 y z w a b u))+((c2_19 y z w a b u*(c3_5 y z w a b u))+((c2_20 y z w a b u*(c3_4 y z w a b u))+((c2_21 y z w a b u*(c3_3 y z w a b u))+((c2_22 y z w a b u*(c3_2 y z w a b u))+((c2_23 y z w a b u*(c3_1 y z w a b u))+((c2_24 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))))))))))+((-1)*(c4_24 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_15,c1_16,c1_17,c1_18,c1_19,c1_20,c1_21,c1_22,c1_23,c1_24,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_23,c2_24,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_23,c3_24,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_24] <;> ring

#print axioms coefficient_24


theorem coefficient_25 (y z w a b u : ℂ) :
    (certificate y z w a b u)[25]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_25 y z w a b u))+((c0_1 y z w a b u*(c1_24 y z w a b u))+((c0_2 y z w a b u*(c1_23 y z w a b u))+((c0_3 y z w a b u*(c1_22 y z w a b u))+((c0_4 y z w a b u*(c1_21 y z w a b u))+((c0_5 y z w a b u*(c1_20 y z w a b u))+((c0_6 y z w a b u*(c1_19 y z w a b u))+((c0_7 y z w a b u*(c1_18 y z w a b u))+((c0_8 y z w a b u*(c1_17 y z w a b u))+(c0_9 y z w a b u*(c1_16 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_25 y z w a b u))+((c2_1 y z w a b u*(c3_24 y z w a b u))+((c2_2 y z w a b u*(c3_23 y z w a b u))+((c2_3 y z w a b u*(c3_22 y z w a b u))+((c2_4 y z w a b u*(c3_21 y z w a b u))+((c2_5 y z w a b u*(c3_20 y z w a b u))+((c2_6 y z w a b u*(c3_19 y z w a b u))+((c2_7 y z w a b u*(c3_18 y z w a b u))+((c2_8 y z w a b u*(c3_17 y z w a b u))+((c2_9 y z w a b u*(c3_16 y z w a b u))+((c2_10 y z w a b u*(c3_15 y z w a b u))+((c2_11 y z w a b u*(c3_14 y z w a b u))+((c2_12 y z w a b u*(c3_13 y z w a b u))+((c2_13 y z w a b u*(c3_12 y z w a b u))+((c2_14 y z w a b u*(c3_11 y z w a b u))+((c2_15 y z w a b u*(c3_10 y z w a b u))+((c2_16 y z w a b u*(c3_9 y z w a b u))+((c2_17 y z w a b u*(c3_8 y z w a b u))+((c2_18 y z w a b u*(c3_7 y z w a b u))+((c2_19 y z w a b u*(c3_6 y z w a b u))+((c2_20 y z w a b u*(c3_5 y z w a b u))+((c2_21 y z w a b u*(c3_4 y z w a b u))+((c2_22 y z w a b u*(c3_3 y z w a b u))+((c2_23 y z w a b u*(c3_2 y z w a b u))+((c2_24 y z w a b u*(c3_1 y z w a b u))+((c2_25 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))))))))))+((-1)*(c4_25 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_16,c1_17,c1_18,c1_19,c1_20,c1_21,c1_22,c1_23,c1_24,c1_25,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_23,c2_24,c2_25,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_23,c3_24,c3_25,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_25] <;> ring

#print axioms coefficient_25


theorem coefficient_26 (y z w a b u : ℂ) :
    (certificate y z w a b u)[26]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_26 y z w a b u))+((c0_1 y z w a b u*(c1_25 y z w a b u))+((c0_2 y z w a b u*(c1_24 y z w a b u))+((c0_3 y z w a b u*(c1_23 y z w a b u))+((c0_4 y z w a b u*(c1_22 y z w a b u))+((c0_5 y z w a b u*(c1_21 y z w a b u))+((c0_6 y z w a b u*(c1_20 y z w a b u))+((c0_7 y z w a b u*(c1_19 y z w a b u))+((c0_8 y z w a b u*(c1_18 y z w a b u))+(c0_9 y z w a b u*(c1_17 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_26 y z w a b u))+((c2_1 y z w a b u*(c3_25 y z w a b u))+((c2_2 y z w a b u*(c3_24 y z w a b u))+((c2_3 y z w a b u*(c3_23 y z w a b u))+((c2_4 y z w a b u*(c3_22 y z w a b u))+((c2_5 y z w a b u*(c3_21 y z w a b u))+((c2_6 y z w a b u*(c3_20 y z w a b u))+((c2_7 y z w a b u*(c3_19 y z w a b u))+((c2_8 y z w a b u*(c3_18 y z w a b u))+((c2_9 y z w a b u*(c3_17 y z w a b u))+((c2_10 y z w a b u*(c3_16 y z w a b u))+((c2_11 y z w a b u*(c3_15 y z w a b u))+((c2_12 y z w a b u*(c3_14 y z w a b u))+((c2_13 y z w a b u*(c3_13 y z w a b u))+((c2_14 y z w a b u*(c3_12 y z w a b u))+((c2_15 y z w a b u*(c3_11 y z w a b u))+((c2_16 y z w a b u*(c3_10 y z w a b u))+((c2_17 y z w a b u*(c3_9 y z w a b u))+((c2_18 y z w a b u*(c3_8 y z w a b u))+((c2_19 y z w a b u*(c3_7 y z w a b u))+((c2_20 y z w a b u*(c3_6 y z w a b u))+((c2_21 y z w a b u*(c3_5 y z w a b u))+((c2_22 y z w a b u*(c3_4 y z w a b u))+((c2_23 y z w a b u*(c3_3 y z w a b u))+((c2_24 y z w a b u*(c3_2 y z w a b u))+((c2_25 y z w a b u*(c3_1 y z w a b u))+((c2_26 y z w a b u*(c3_0 y z w a b u))+0))))))))))))))))))))))))))))+((-1)*(c4_26 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_17,c1_18,c1_19,c1_20,c1_21,c1_22,c1_23,c1_24,c1_25,c1_26,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_23,c2_24,c2_25,c2_26,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_23,c3_24,c3_25,c3_26,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_26] <;> ring

#print axioms coefficient_26


theorem coefficient_27 (y z w a b u : ℂ) :
    (certificate y z w a b u)[27]?=some 0 := by
  change some (((((c0_0 y z w a b u*(c1_27 y z w a b u))+((c0_1 y z w a b u*(c1_26 y z w a b u))+((c0_2 y z w a b u*(c1_25 y z w a b u))+((c0_3 y z w a b u*(c1_24 y z w a b u))+((c0_4 y z w a b u*(c1_23 y z w a b u))+((c0_5 y z w a b u*(c1_22 y z w a b u))+((c0_6 y z w a b u*(c1_21 y z w a b u))+((c0_7 y z w a b u*(c1_20 y z w a b u))+((c0_8 y z w a b u*(c1_19 y z w a b u))+(c0_9 y z w a b u*(c1_18 y z w a b u)))))))))))+((c2_0 y z w a b u*(c3_27 y z w a b u))+((c2_1 y z w a b u*(c3_26 y z w a b u))+((c2_2 y z w a b u*(c3_25 y z w a b u))+((c2_3 y z w a b u*(c3_24 y z w a b u))+((c2_4 y z w a b u*(c3_23 y z w a b u))+((c2_5 y z w a b u*(c3_22 y z w a b u))+((c2_6 y z w a b u*(c3_21 y z w a b u))+((c2_7 y z w a b u*(c3_20 y z w a b u))+((c2_8 y z w a b u*(c3_19 y z w a b u))+((c2_9 y z w a b u*(c3_18 y z w a b u))+((c2_10 y z w a b u*(c3_17 y z w a b u))+((c2_11 y z w a b u*(c3_16 y z w a b u))+((c2_12 y z w a b u*(c3_15 y z w a b u))+((c2_13 y z w a b u*(c3_14 y z w a b u))+((c2_14 y z w a b u*(c3_13 y z w a b u))+((c2_15 y z w a b u*(c3_12 y z w a b u))+((c2_16 y z w a b u*(c3_11 y z w a b u))+((c2_17 y z w a b u*(c3_10 y z w a b u))+((c2_18 y z w a b u*(c3_9 y z w a b u))+((c2_19 y z w a b u*(c3_8 y z w a b u))+((c2_20 y z w a b u*(c3_7 y z w a b u))+((c2_21 y z w a b u*(c3_6 y z w a b u))+((c2_22 y z w a b u*(c3_5 y z w a b u))+((c2_23 y z w a b u*(c3_4 y z w a b u))+((c2_24 y z w a b u*(c3_3 y z w a b u))+((c2_25 y z w a b u*(c3_2 y z w a b u))+((c2_26 y z w a b u*(c3_1 y z w a b u))+((c2_27 y z w a b u*(c3_0 y z w a b u))+0)))))))))))))))))))))))))))))+((-1)*(c4_27 y z w a b u)))) = some 0
  congr 1 <;> simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_18,c1_19,c1_20,c1_21,c1_22,c1_23,c1_24,c1_25,c1_26,c1_27,c2_0,c2_1,c2_10,c2_11,c2_12,c2_13,c2_14,c2_15,c2_16,c2_17,c2_18,c2_19,c2_2,c2_20,c2_21,c2_22,c2_23,c2_24,c2_25,c2_26,c2_27,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_2,c3_20,c3_21,c3_22,c3_23,c3_24,c3_25,c3_26,c3_27,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_27] <;> ring

#print axioms coefficient_27



}
end SmallLevelTwentySixPariIdentity021X

end
end
