module
public import SmallLevelTwentySixMMPPariSyzygyIndexColumnIndexBundleSeriesV4
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column0
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 16 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
  · exact coefficient_15 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column0
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column1
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 15 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column1
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column2
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 16 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
  · exact coefficient_15 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column2
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column3
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 15 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column3
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column4
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 14 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column4
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy6Column5
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 14 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy6Column5
end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column0
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 16 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
  · exact coefficient_15 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column0
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column1
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 15 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column1
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column2
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 16 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
  · exact coefficient_15 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column2
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column3
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 15 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column3
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column4
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 14 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column4
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSyzygy7Column5
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero (y z w a b : ℂ) : ∀ v∈certificate y z w a b,v=0 := by
  apply zero_of_getElem? _ 15 (certificate_length y z w a b)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b
  · exact coefficient_1 y z w a b
  · exact coefficient_2 y z w a b
  · exact coefficient_3 y z w a b
  · exact coefficient_4 y z w a b
  · exact coefficient_5 y z w a b
  · exact coefficient_6 y z w a b
  · exact coefficient_7 y z w a b
  · exact coefficient_8 y z w a b
  · exact coefficient_9 y z w a b
  · exact coefficient_10 y z w a b
  · exact coefficient_11 y z w a b
  · exact coefficient_12 y z w a b
  · exact coefficient_13 y z w a b
  · exact coefficient_14 y z w a b
theorem identity (x y z w a b : ℂ) :
    p0 x y z w a b*p1 x y z w a b = p10 x y z w a b+p2 x y z w a b*p3 x y z w a b+p4 x y z w a b*p5 x y z w a b+p6 x y z w a b*p7 x y z w a b+p8 x y z w a b*p9 x y z w a b := by
  have h:=evaluate_zero x _ (certificate_zero y z w a b)
  simp only [certificate,evaluate_add,evaluate_scale,evaluate_multiply] at h
  unfold p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 
  linear_combination h
#print axioms identity

end SmallLevelTwentySixMMPPariSyzygy7Column5
end
end
