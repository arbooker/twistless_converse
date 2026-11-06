module
public import QuantitativeArithmeticSmallLevelThirtyThreePlusEliminationPivotBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem all_pivot_certificates (i : Fin 64) :
    substituteCompute (baseRows 1) (pivotOperations i)=pivotRow i := by
  fin_cases i
  · exact pivot_certificate_00
  · exact pivot_certificate_01
  · exact pivot_certificate_02
  · exact pivot_certificate_03
  · exact pivot_certificate_04
  · exact pivot_certificate_05
  · exact pivot_certificate_06
  · exact pivot_certificate_07
  · exact pivot_certificate_08
  · exact pivot_certificate_09
  · exact pivot_certificate_10
  · exact pivot_certificate_11
  · exact pivot_certificate_12
  · exact pivot_certificate_13
  · exact pivot_certificate_14
  · exact pivot_certificate_15
  · exact pivot_certificate_16
  · exact pivot_certificate_17
  · exact pivot_certificate_18
  · exact pivot_certificate_19
  · exact pivot_certificate_20
  · exact pivot_certificate_21
  · exact pivot_certificate_22
  · exact pivot_certificate_23
  · exact pivot_certificate_24
  · exact pivot_certificate_25
  · exact pivot_certificate_26
  · exact pivot_certificate_27
  · exact pivot_certificate_28
  · exact pivot_certificate_29
  · exact pivot_certificate_30
  · exact pivot_certificate_31
  · exact pivot_certificate_32
  · exact pivot_certificate_33
  · exact pivot_certificate_34
  · exact pivot_certificate_35
  · exact pivot_certificate_36
  · exact pivot_certificate_37
  · exact pivot_certificate_38
  · exact pivot_certificate_39
  · exact pivot_certificate_40
  · exact pivot_certificate_41
  · exact pivot_certificate_42
  · exact pivot_certificate_43
  · exact pivot_certificate_44
  · exact pivot_certificate_45
  · exact pivot_certificate_46
  · exact pivot_certificate_47
  · exact pivot_certificate_48
  · exact pivot_certificate_49
  · exact pivot_certificate_50
  · exact pivot_certificate_51
  · exact pivot_certificate_52
  · exact pivot_certificate_53
  · exact pivot_certificate_54
  · exact pivot_certificate_55
  · exact pivot_certificate_56
  · exact pivot_certificate_57
  · exact pivot_certificate_58
  · exact pivot_certificate_59
  · exact pivot_certificate_60
  · exact pivot_certificate_61
  · exact pivot_certificate_62
  · exact pivot_certificate_63

theorem pivot_rows_of_sources (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hsource : ∀ j,eval x y z 1 a 1 1 v (baseRows 1 j)=0) (i : Fin 64) :
    eval x y z 1 a 1 1 v (pivotRow i)=0 := by
  apply eval_of_substitution x y z 1 a 1 1 v hx hy hz (by norm_num)
    (baseRows 1) (pivotOperations i) (pivotRow i)
  · rw [← substituteCompute_eq]
    exact all_pivot_certificates i
  · intro t _
    exact hsource t.2.1

#print axioms all_pivot_certificates
#print axioms pivot_rows_of_sources
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
