module
public import SmallLevelTwentySixReflectedTranslatedV1
public import SmallLevelTwentySixMMPPariTraceTwentySixV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilyDataV4
public meta import SmallLevelPolynomialCertificateCommandsV4
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public import SmallLevelPolynomialZeroPrefixV1
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace027
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=32 := by
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

end SmallLevelTwentySixMMPPariTrace027
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixMMPPariTrace027
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem identity_shift (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  have h0 : p0 x y z w a b u=1 := by norm_num [p0,coefficients0,c0_0,evaluate]
  have h2 : p2 x y z w a b u=0 := by norm_num [p2,coefficients2,evaluate]
  have h4 : p4 x y z w a b u=0 := by norm_num [p4,coefficients4,evaluate]
  have h5 : p5 x y z w a b u=x^4 := by
    simp only [p5,coefficients5,c5_0,c5_1,c5_2,c5_3,c5_4,evaluate]
    ring
  have hcoeff : coefficients1 y z w a b u=List.replicate 4 0 ++ coefficients6 y z w a b u := by rfl
  rw [h0,h2,h4,h5]
  simp only [one_mul,zero_mul,zero_add,add_zero]
  unfold p1 p6
  rw [hcoeff]
  exact SmallLevelPolynomialZeroPrefix.evaluate_zero_prefix x _ _
#print axioms identity_shift
end SmallLevelTwentySixMMPPariTrace027
end
end
