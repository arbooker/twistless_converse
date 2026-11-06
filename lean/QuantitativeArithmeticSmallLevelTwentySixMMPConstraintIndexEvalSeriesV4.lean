module
public import SmallLevelTwentySixMMPPariTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QuantitativeArithmeticSmallLevelTwentySixMMPConstraint6Eval
open QuantitativeArithmeticSevenLaurentRows SmallLevelTwentySixMMPPari
theorem constraint6_eval (x y z w a b : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b 1 v constraint6Row=constraint6 x y z w a b v := by
  simp only [constraint6Row,eval_append,eval_shift x y z w a b 1 v hx hy hz hw]
  rw [constraint6_base_0,constraint6_base_1,constraint6_base_2,constraint6_base_3,constraint6_base_4,constraint6_base_5,constraint6_base_6,constraint6_base_7,constraint6_base_8,constraint6_base_9,constraint6_base_10,constraint6_base_11,constraint6_base_12,constraint6_base_13,constraint6_base_14,constraint6_base_15]
  norm_num only [monomial]
  unfold constraint6 SmallLevelTwentySixMMPPariSyzygy6Column0.p10 SmallLevelTwentySixMMPPariSyzygy6Column1.p10 SmallLevelTwentySixMMPPariSyzygy6Column0.coefficients10 SmallLevelTwentySixMMPPariSyzygy6Column1.coefficients10
  simp only [SmallLevelPolynomialCoefficientCertificate.evaluate]
  simp only [zpow_natCast,zpow_ofNat]
  ring
#print axioms constraint6_eval

end QuantitativeArithmeticSmallLevelTwentySixMMPConstraint6Eval
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QuantitativeArithmeticSmallLevelTwentySixMMPConstraint7Eval
open QuantitativeArithmeticSevenLaurentRows SmallLevelTwentySixMMPPari
theorem constraint7_eval (x y z w a b : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b 1 v constraint7Row=constraint7 x y z w a b v := by
  simp only [constraint7Row,eval_append,eval_shift x y z w a b 1 v hx hy hz hw]
  rw [constraint7_base_0,constraint7_base_1,constraint7_base_2,constraint7_base_3,constraint7_base_4,constraint7_base_5,constraint7_base_6,constraint7_base_7,constraint7_base_8,constraint7_base_9,constraint7_base_10,constraint7_base_11,constraint7_base_12,constraint7_base_13,constraint7_base_14]
  norm_num only [monomial]
  unfold constraint7 SmallLevelTwentySixMMPPariSyzygy7Column0.p10 SmallLevelTwentySixMMPPariSyzygy7Column1.p10 SmallLevelTwentySixMMPPariSyzygy7Column0.coefficients10 SmallLevelTwentySixMMPPariSyzygy7Column1.coefficients10
  simp only [SmallLevelPolynomialCoefficientCertificate.evaluate]
  simp only [zpow_natCast,zpow_ofNat]
  ring
#print axioms constraint7_eval

end QuantitativeArithmeticSmallLevelTwentySixMMPConstraint7Eval
end
