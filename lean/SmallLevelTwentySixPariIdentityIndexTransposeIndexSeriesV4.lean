module
public import SmallLevelTwentySixPariIdentity017Transpose1TheoryV4
public import SmallLevelTwentySixPariIdentity021Transpose1FamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace SmallLevelTwentySixPariIdentity017Transpose1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity017.p1 x y z w a b u = SmallLevelTwentySixPariIdentity017X.p1 x y z w a b u := by
  have ho : SmallLevelTwentySixPariIdentity017.p1 x y z w a b u =
      evaluate y (List.ofFn (fun i => evaluate x (List.ofFn (matrix i)))) := by
    change evaluate y (List.ofFn (originalCoefficients x z w a b u)) = _
    apply evaluate_ofFn_congr
    intro i
    fin_cases i
    · exact row_binding_0 x z w a b u
    · exact row_binding_1 x z w a b u
    · exact row_binding_2 x z w a b u
    · exact row_binding_3 x z w a b u
    · exact row_binding_4 x z w a b u
    · exact row_binding_5 x z w a b u
    · exact row_binding_6 x z w a b u
    · exact row_binding_7 x z w a b u
    · exact row_binding_8 x z w a b u
    · exact row_binding_9 x z w a b u
  have hn : SmallLevelTwentySixPariIdentity017X.p1 x y z w a b u =
      evaluate x (List.ofFn (fun j => evaluate y (List.ofFn (fun i => matrix i j)))) := by
    change evaluate x (List.ofFn (newCoefficients y z w a b u)) = _
    apply evaluate_ofFn_congr
    intro j
    fin_cases j
    · exact column_binding_0 y z w a b u
    · exact column_binding_1 y z w a b u
    · exact column_binding_2 y z w a b u
    · exact column_binding_3 y z w a b u
    · exact column_binding_4 y z w a b u
    · exact column_binding_5 y z w a b u
    · exact column_binding_6 y z w a b u
    · exact column_binding_7 y z w a b u
    · exact column_binding_8 y z w a b u
    · exact column_binding_9 y z w a b u
    · exact column_binding_10 y z w a b u
    · exact column_binding_11 y z w a b u
    · exact column_binding_12 y z w a b u
    · exact column_binding_13 y z w a b u
    · exact column_binding_14 y z w a b u
    · exact column_binding_15 y z w a b u
    · exact column_binding_16 y z w a b u
    · exact column_binding_17 y z w a b u
    · exact column_binding_18 y z w a b u
    · exact column_binding_19 y z w a b u
    · exact column_binding_20 y z w a b u
    · exact column_binding_21 y z w a b u
    · exact column_binding_22 y z w a b u
    · exact column_binding_23 y z w a b u
    · exact column_binding_24 y z w a b u
    · exact column_binding_25 y z w a b u
    · exact column_binding_26 y z w a b u
    · exact column_binding_27 y z w a b u
    · exact column_binding_28 y z w a b u
    · exact column_binding_29 y z w a b u
    · exact column_binding_30 y z w a b u
    · exact column_binding_31 y z w a b u
    · exact column_binding_32 y z w a b u
    · exact column_binding_33 y z w a b u
    · exact column_binding_34 y z w a b u
    · exact column_binding_35 y z w a b u
    · exact column_binding_36 y z w a b u
    · exact column_binding_37 y z w a b u
    · exact column_binding_38 y z w a b u
    · exact column_binding_39 y z w a b u
    · exact column_binding_40 y z w a b u
    · exact column_binding_41 y z w a b u
    · exact column_binding_42 y z w a b u
    · exact column_binding_43 y z w a b u
    · exact column_binding_44 y z w a b u
    · exact column_binding_45 y z w a b u
    · exact column_binding_46 y z w a b u
    · exact column_binding_47 y z w a b u
    · exact column_binding_48 y z w a b u
    · exact column_binding_49 y z w a b u
    · exact column_binding_50 y z w a b u
    · exact column_binding_51 y z w a b u
    · exact column_binding_52 y z w a b u
    · exact column_binding_53 y z w a b u
    · exact column_binding_54 y z w a b u
    · exact column_binding_55 y z w a b u
    · exact column_binding_56 y z w a b u
    · exact column_binding_57 y z w a b u
    · exact column_binding_58 y z w a b u
    · exact column_binding_59 y z w a b u
    · exact column_binding_60 y z w a b u
    · exact column_binding_61 y z w a b u
    · exact column_binding_62 y z w a b u
    · exact column_binding_63 y z w a b u
    · exact column_binding_64 y z w a b u
    · exact column_binding_65 y z w a b u
    · exact column_binding_66 y z w a b u
    · exact column_binding_67 y z w a b u
    · exact column_binding_68 y z w a b u
    · exact column_binding_69 y z w a b u
    · exact column_binding_70 y z w a b u
    · exact column_binding_71 y z w a b u
    · exact column_binding_72 y z w a b u
    · exact column_binding_73 y z w a b u
    · exact column_binding_74 y z w a b u
    · exact column_binding_75 y z w a b u
    · exact column_binding_76 y z w a b u
    · exact column_binding_77 y z w a b u
    · exact column_binding_78 y z w a b u
    · exact column_binding_79 y z w a b u
    · exact column_binding_80 y z w a b u
    · exact column_binding_81 y z w a b u
    · exact column_binding_82 y z w a b u
    · exact column_binding_83 y z w a b u
    · exact column_binding_84 y z w a b u
    · exact column_binding_85 y z w a b u
    · exact column_binding_86 y z w a b u
    · exact column_binding_87 y z w a b u
    · exact column_binding_88 y z w a b u
    · exact column_binding_89 y z w a b u
    · exact column_binding_90 y z w a b u
    · exact column_binding_91 y z w a b u
    · exact column_binding_92 y z w a b u
    · exact column_binding_93 y z w a b u
    · exact column_binding_94 y z w a b u
    · exact column_binding_95 y z w a b u
    · exact column_binding_96 y z w a b u
    · exact column_binding_97 y z w a b u
    · exact column_binding_98 y z w a b u
    · exact column_binding_99 y z w a b u
    · exact column_binding_100 y z w a b u
    · exact column_binding_101 y z w a b u
    · exact column_binding_102 y z w a b u
    · exact column_binding_103 y z w a b u
    · exact column_binding_104 y z w a b u
    · exact column_binding_105 y z w a b u
    · exact column_binding_106 y z w a b u
    · exact column_binding_107 y z w a b u
    · exact column_binding_108 y z w a b u
    · exact column_binding_109 y z w a b u
    · exact column_binding_110 y z w a b u
    · exact column_binding_111 y z w a b u
    · exact column_binding_112 y z w a b u
    · exact column_binding_113 y z w a b u
    · exact column_binding_114 y z w a b u
    · exact column_binding_115 y z w a b u
    · exact column_binding_116 y z w a b u
    · exact column_binding_117 y z w a b u
    · exact column_binding_118 y z w a b u
    · exact column_binding_119 y z w a b u
    · exact column_binding_120 y z w a b u
    · exact column_binding_121 y z w a b u
    · exact column_binding_122 y z w a b u
    · exact column_binding_123 y z w a b u
    · exact column_binding_124 y z w a b u
    · exact column_binding_125 y z w a b u
    · exact column_binding_126 y z w a b u
    · exact column_binding_127 y z w a b u
    · exact column_binding_128 y z w a b u
    · exact column_binding_129 y z w a b u
    · exact column_binding_130 y z w a b u
    · exact column_binding_131 y z w a b u
    · exact column_binding_132 y z w a b u
    · exact column_binding_133 y z w a b u
    · exact column_binding_134 y z w a b u
    · exact column_binding_135 y z w a b u
    · exact column_binding_136 y z w a b u
    · exact column_binding_137 y z w a b u
    · exact column_binding_138 y z w a b u
    · exact column_binding_139 y z w a b u
    · exact column_binding_140 y z w a b u
    · exact column_binding_141 y z w a b u
    · exact column_binding_142 y z w a b u
    · exact column_binding_143 y z w a b u
    · exact column_binding_144 y z w a b u
    · exact column_binding_145 y z w a b u
    · exact column_binding_146 y z w a b u
    · exact column_binding_147 y z w a b u
    · exact column_binding_148 y z w a b u
    · exact column_binding_149 y z w a b u
    · exact column_binding_150 y z w a b u
    · exact column_binding_151 y z w a b u
    · exact column_binding_152 y z w a b u
    · exact column_binding_153 y z w a b u
  exact ho.trans ((evaluate_transpose x y matrix).trans hn.symm)

#print axioms binding

end SmallLevelTwentySixPariIdentity017Transpose1
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace SmallLevelTwentySixPariIdentity021Transpose1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity021.p1 x y z w a b u = SmallLevelTwentySixPariIdentity021X.p1 x y z w a b u := by
  have ho : SmallLevelTwentySixPariIdentity021.p1 x y z w a b u =
      evaluate y (List.ofFn (fun i => evaluate x (List.ofFn (matrix i)))) := by
    change evaluate y (List.ofFn (originalCoefficients x z w a b u)) = _
    apply evaluate_ofFn_congr
    intro i
    fin_cases i
    · exact row_binding_0 x z w a b u
    · exact row_binding_1 x z w a b u
    · exact row_binding_2 x z w a b u
    · exact row_binding_3 x z w a b u
    · exact row_binding_4 x z w a b u
    · exact row_binding_5 x z w a b u
    · exact row_binding_6 x z w a b u
    · exact row_binding_7 x z w a b u
    · exact row_binding_8 x z w a b u
    · exact row_binding_9 x z w a b u
  have hn : SmallLevelTwentySixPariIdentity021X.p1 x y z w a b u =
      evaluate x (List.ofFn (fun j => evaluate y (List.ofFn (fun i => matrix i j)))) := by
    change evaluate x (List.ofFn (newCoefficients y z w a b u)) = _
    apply evaluate_ofFn_congr
    intro j
    fin_cases j
    · exact column_binding_0 y z w a b u
    · exact column_binding_1 y z w a b u
    · exact column_binding_2 y z w a b u
    · exact column_binding_3 y z w a b u
    · exact column_binding_4 y z w a b u
    · exact column_binding_5 y z w a b u
    · exact column_binding_6 y z w a b u
    · exact column_binding_7 y z w a b u
    · exact column_binding_8 y z w a b u
    · exact column_binding_9 y z w a b u
    · exact column_binding_10 y z w a b u
    · exact column_binding_11 y z w a b u
    · exact column_binding_12 y z w a b u
    · exact column_binding_13 y z w a b u
    · exact column_binding_14 y z w a b u
    · exact column_binding_15 y z w a b u
    · exact column_binding_16 y z w a b u
    · exact column_binding_17 y z w a b u
    · exact column_binding_18 y z w a b u
    · exact column_binding_19 y z w a b u
    · exact column_binding_20 y z w a b u
    · exact column_binding_21 y z w a b u
    · exact column_binding_22 y z w a b u
    · exact column_binding_23 y z w a b u
    · exact column_binding_24 y z w a b u
    · exact column_binding_25 y z w a b u
    · exact column_binding_26 y z w a b u
    · exact column_binding_27 y z w a b u
    · exact column_binding_28 y z w a b u
    · exact column_binding_29 y z w a b u
    · exact column_binding_30 y z w a b u
    · exact column_binding_31 y z w a b u
    · exact column_binding_32 y z w a b u
    · exact column_binding_33 y z w a b u
    · exact column_binding_34 y z w a b u
    · exact column_binding_35 y z w a b u
    · exact column_binding_36 y z w a b u
    · exact column_binding_37 y z w a b u
    · exact column_binding_38 y z w a b u
    · exact column_binding_39 y z w a b u
    · exact column_binding_40 y z w a b u
    · exact column_binding_41 y z w a b u
    · exact column_binding_42 y z w a b u
    · exact column_binding_43 y z w a b u
    · exact column_binding_44 y z w a b u
    · exact column_binding_45 y z w a b u
    · exact column_binding_46 y z w a b u
    · exact column_binding_47 y z w a b u
    · exact column_binding_48 y z w a b u
    · exact column_binding_49 y z w a b u
    · exact column_binding_50 y z w a b u
    · exact column_binding_51 y z w a b u
    · exact column_binding_52 y z w a b u
    · exact column_binding_53 y z w a b u
    · exact column_binding_54 y z w a b u
    · exact column_binding_55 y z w a b u
    · exact column_binding_56 y z w a b u
    · exact column_binding_57 y z w a b u
    · exact column_binding_58 y z w a b u
    · exact column_binding_59 y z w a b u
    · exact column_binding_60 y z w a b u
    · exact column_binding_61 y z w a b u
    · exact column_binding_62 y z w a b u
    · exact column_binding_63 y z w a b u
    · exact column_binding_64 y z w a b u
    · exact column_binding_65 y z w a b u
    · exact column_binding_66 y z w a b u
    · exact column_binding_67 y z w a b u
    · exact column_binding_68 y z w a b u
    · exact column_binding_69 y z w a b u
    · exact column_binding_70 y z w a b u
    · exact column_binding_71 y z w a b u
    · exact column_binding_72 y z w a b u
    · exact column_binding_73 y z w a b u
    · exact column_binding_74 y z w a b u
    · exact column_binding_75 y z w a b u
    · exact column_binding_76 y z w a b u
    · exact column_binding_77 y z w a b u
    · exact column_binding_78 y z w a b u
    · exact column_binding_79 y z w a b u
    · exact column_binding_80 y z w a b u
    · exact column_binding_81 y z w a b u
    · exact column_binding_82 y z w a b u
    · exact column_binding_83 y z w a b u
    · exact column_binding_84 y z w a b u
    · exact column_binding_85 y z w a b u
    · exact column_binding_86 y z w a b u
    · exact column_binding_87 y z w a b u
    · exact column_binding_88 y z w a b u
    · exact column_binding_89 y z w a b u
    · exact column_binding_90 y z w a b u
    · exact column_binding_91 y z w a b u
    · exact column_binding_92 y z w a b u
    · exact column_binding_93 y z w a b u
    · exact column_binding_94 y z w a b u
    · exact column_binding_95 y z w a b u
    · exact column_binding_96 y z w a b u
    · exact column_binding_97 y z w a b u
    · exact column_binding_98 y z w a b u
    · exact column_binding_99 y z w a b u
    · exact column_binding_100 y z w a b u
    · exact column_binding_101 y z w a b u
    · exact column_binding_102 y z w a b u
    · exact column_binding_103 y z w a b u
    · exact column_binding_104 y z w a b u
    · exact column_binding_105 y z w a b u
    · exact column_binding_106 y z w a b u
    · exact column_binding_107 y z w a b u
    · exact column_binding_108 y z w a b u
    · exact column_binding_109 y z w a b u
    · exact column_binding_110 y z w a b u
    · exact column_binding_111 y z w a b u
    · exact column_binding_112 y z w a b u
    · exact column_binding_113 y z w a b u
    · exact column_binding_114 y z w a b u
    · exact column_binding_115 y z w a b u
    · exact column_binding_116 y z w a b u
    · exact column_binding_117 y z w a b u
    · exact column_binding_118 y z w a b u
    · exact column_binding_119 y z w a b u
    · exact column_binding_120 y z w a b u
    · exact column_binding_121 y z w a b u
    · exact column_binding_122 y z w a b u
    · exact column_binding_123 y z w a b u
    · exact column_binding_124 y z w a b u
    · exact column_binding_125 y z w a b u
    · exact column_binding_126 y z w a b u
    · exact column_binding_127 y z w a b u
    · exact column_binding_128 y z w a b u
    · exact column_binding_129 y z w a b u
    · exact column_binding_130 y z w a b u
    · exact column_binding_131 y z w a b u
    · exact column_binding_132 y z w a b u
    · exact column_binding_133 y z w a b u
    · exact column_binding_134 y z w a b u
    · exact column_binding_135 y z w a b u
    · exact column_binding_136 y z w a b u
    · exact column_binding_137 y z w a b u
    · exact column_binding_138 y z w a b u
    · exact column_binding_139 y z w a b u
    · exact column_binding_140 y z w a b u
    · exact column_binding_141 y z w a b u
    · exact column_binding_142 y z w a b u
    · exact column_binding_143 y z w a b u
    · exact column_binding_144 y z w a b u
    · exact column_binding_145 y z w a b u
    · exact column_binding_146 y z w a b u
    · exact column_binding_147 y z w a b u
    · exact column_binding_148 y z w a b u
    · exact column_binding_149 y z w a b u
    · exact column_binding_150 y z w a b u
    · exact column_binding_151 y z w a b u
    · exact column_binding_152 y z w a b u
    · exact column_binding_153 y z w a b u
    · exact column_binding_154 y z w a b u
    · exact column_binding_155 y z w a b u
  exact ho.trans ((evaluate_transpose x y matrix).trans hn.symm)

#print axioms binding

end SmallLevelTwentySixPariIdentity021Transpose1
end
