module
public import SmallLevelTwentySixGridShiftSupportBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorTarget_restrict (v : Fin 780→ℂ) (i : Fin 71) :
    gridSample (gridTaylorQ i) (gridTaylorPartner i) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ i) (gridTaylorPartner i) v := by
  fin_cases i
  · exact taylorTarget_restrict_0 v
  · exact taylorTarget_restrict_1 v
  · exact taylorTarget_restrict_2 v
  · exact taylorTarget_restrict_3 v
  · exact taylorTarget_restrict_4 v
  · exact taylorTarget_restrict_5 v
  · exact taylorTarget_restrict_6 v
  · exact taylorTarget_restrict_7 v
  · exact taylorTarget_restrict_8 v
  · exact taylorTarget_restrict_9 v
  · exact taylorTarget_restrict_10 v
  · exact taylorTarget_restrict_11 v
  · exact taylorTarget_restrict_12 v
  · exact taylorTarget_restrict_13 v
  · exact taylorTarget_restrict_14 v
  · exact taylorTarget_restrict_15 v
  · exact taylorTarget_restrict_16 v
  · exact taylorTarget_restrict_17 v
  · exact taylorTarget_restrict_18 v
  · exact taylorTarget_restrict_19 v
  · exact taylorTarget_restrict_20 v
  · exact taylorTarget_restrict_21 v
  · exact taylorTarget_restrict_22 v
  · exact taylorTarget_restrict_23 v
  · exact taylorTarget_restrict_24 v
  · exact taylorTarget_restrict_25 v
  · exact taylorTarget_restrict_26 v
  · exact taylorTarget_restrict_27 v
  · exact taylorTarget_restrict_28 v
  · exact taylorTarget_restrict_29 v
  · exact taylorTarget_restrict_30 v
  · exact taylorTarget_restrict_31 v
  · exact taylorTarget_restrict_32 v
  · exact taylorTarget_restrict_33 v
  · exact taylorTarget_restrict_34 v
  · exact taylorTarget_restrict_35 v
  · exact taylorTarget_restrict_36 v
  · exact taylorTarget_restrict_37 v
  · exact taylorTarget_restrict_38 v
  · exact taylorTarget_restrict_39 v
  · exact taylorTarget_restrict_40 v
  · exact taylorTarget_restrict_41 v
  · exact taylorTarget_restrict_42 v
  · exact taylorTarget_restrict_43 v
  · exact taylorTarget_restrict_44 v
  · exact taylorTarget_restrict_45 v
  · exact taylorTarget_restrict_46 v
  · exact taylorTarget_restrict_47 v
  · exact taylorTarget_restrict_48 v
  · exact taylorTarget_restrict_49 v
  · exact taylorTarget_restrict_50 v
  · exact taylorTarget_restrict_51 v
  · exact taylorTarget_restrict_52 v
  · exact taylorTarget_restrict_53 v
  · exact taylorTarget_restrict_54 v
  · exact taylorTarget_restrict_55 v
  · exact taylorTarget_restrict_56 v
  · exact taylorTarget_restrict_57 v
  · exact taylorTarget_restrict_58 v
  · exact taylorTarget_restrict_59 v
  · exact taylorTarget_restrict_60 v
  · exact taylorTarget_restrict_61 v
  · exact taylorTarget_restrict_62 v
  · exact taylorTarget_restrict_63 v
  · exact taylorTarget_restrict_64 v
  · exact taylorTarget_restrict_65 v
  · exact taylorTarget_restrict_66 v
  · exact taylorTarget_restrict_67 v
  · exact taylorTarget_restrict_68 v
  · exact taylorTarget_restrict_69 v
  · exact taylorTarget_restrict_70 v

theorem shiftRows_restrict (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s (extension support (fun j => v (support j))) i=
      gridShiftRows m f ε n s v i := by
  cases i <;> simp only [gridShiftRows,groupTarget_restrict,taylorTarget_restrict]

#print axioms groupTargetSupport_spec
#print axioms taylorTarget_restrict
#print axioms shiftRows_restrict

end SmallLevelTwentySixGrid
