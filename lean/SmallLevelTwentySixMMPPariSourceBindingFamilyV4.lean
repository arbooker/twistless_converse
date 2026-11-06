module
public import SmallLevelTwentySixMMPPariSourceBindingIndexXBundleSeriesV4
public import SmallLevelTwentySixMMPPariTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSourceBinding6
open SmallLevelPolynomialCoefficientCertificate
theorem coefficients_binding (y z w a b u : ℂ) : coefficients y z w a b u=add (SmallLevelTwentySixMMPPariSyzygy6Column0.coefficients10 y z w a b) (scale u (SmallLevelTwentySixMMPPariSyzygy6Column1.coefficients10 y z w a b)) := by
  change [(canonical0 y z w a b u),(canonical1 y z w a b u),(canonical2 y z w a b u),(canonical3 y z w a b u),(canonical4 y z w a b u),(canonical5 y z w a b u),(canonical6 y z w a b u),(canonical7 y z w a b u),(canonical8 y z w a b u),(canonical9 y z w a b u),(canonical10 y z w a b u),(canonical11 y z w a b u),(canonical12 y z w a b u),(canonical13 y z w a b u),(canonical14 y z w a b u),(canonical15 y z w a b u)]=[(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_0 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_0 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_1 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_1 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_2 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_2 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_3 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_3 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_4 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_4 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_5 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_5 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_6 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_6 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_7 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_7 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_8 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_8 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_9 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_9 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_10 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_10 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_11 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_11 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_12 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_12 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_13 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_13 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_14 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy6Column1.c10_14 y z w a b),(SmallLevelTwentySixMMPPariSyzygy6Column0.c10_15 y z w a b)]
  simp only [coefficient_0,coefficient_1,coefficient_2,coefficient_3,coefficient_4,coefficient_5,coefficient_6,coefficient_7,coefficient_8,coefficient_9,coefficient_10,coefficient_11,coefficient_12,coefficient_13,coefficient_14,coefficient_15,mul_zero,add_zero]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace009.p3 x y z w a b u=SmallLevelTwentySixMMPPari.constraint6 x y z w a b (fun j => if j=0 then 1 else u) := by
  rw [trace_binding,coefficients_binding,evaluate_add,evaluate_scale]
  simp only [SmallLevelTwentySixMMPPari.constraint6,SmallLevelTwentySixMMPPariSyzygy6Column0.p10,SmallLevelTwentySixMMPPariSyzygy6Column1.p10]
  norm_num only [ite_true,ite_false,mul_one]
  ring
#print axioms binding

end SmallLevelTwentySixMMPPariSourceBinding6
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariSourceBinding7
open SmallLevelPolynomialCoefficientCertificate
theorem coefficients_binding (y z w a b u : ℂ) : coefficients y z w a b u=add (SmallLevelTwentySixMMPPariSyzygy7Column0.coefficients10 y z w a b) (scale u (SmallLevelTwentySixMMPPariSyzygy7Column1.coefficients10 y z w a b)) := by
  change [(canonical0 y z w a b u),(canonical1 y z w a b u),(canonical2 y z w a b u),(canonical3 y z w a b u),(canonical4 y z w a b u),(canonical5 y z w a b u),(canonical6 y z w a b u),(canonical7 y z w a b u),(canonical8 y z w a b u),(canonical9 y z w a b u),(canonical10 y z w a b u),(canonical11 y z w a b u),(canonical12 y z w a b u),(canonical13 y z w a b u),(canonical14 y z w a b u)]=[(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_0 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_0 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_1 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_1 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_2 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_2 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_3 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_3 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_4 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_4 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_5 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_5 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_6 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_6 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_7 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_7 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_8 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_8 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_9 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_9 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_10 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_10 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_11 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_11 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_12 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_12 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_13 y z w a b)+u*(SmallLevelTwentySixMMPPariSyzygy7Column1.c10_13 y z w a b),(SmallLevelTwentySixMMPPariSyzygy7Column0.c10_14 y z w a b)]
  simp only [coefficient_0,coefficient_1,coefficient_2,coefficient_3,coefficient_4,coefficient_5,coefficient_6,coefficient_7,coefficient_8,coefficient_9,coefficient_10,coefficient_11,coefficient_12,coefficient_13,coefficient_14,mul_zero,add_zero]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace021.p3 x y z w a b u=SmallLevelTwentySixMMPPari.constraint7 x y z w a b (fun j => if j=0 then 1 else u) := by
  rw [trace_binding,coefficients_binding,evaluate_add,evaluate_scale]
  simp only [SmallLevelTwentySixMMPPari.constraint7,SmallLevelTwentySixMMPPariSyzygy7Column0.p10,SmallLevelTwentySixMMPPariSyzygy7Column1.p10]
  norm_num only [ite_true,ite_false,mul_one]
  ring
#print axioms binding

end SmallLevelTwentySixMMPPariSourceBinding7
end
