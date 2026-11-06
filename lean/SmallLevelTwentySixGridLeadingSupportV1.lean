module
public import SmallLevelTwentySixGridLeadingSupportBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorSource_restrict (v : Fin 780→ℂ) (i : Fin 71) :
    gridSample (gridTaylorQ i) (gridTaylorT i) (extension support (fun j => v (support j)))=gridSample (gridTaylorQ i) (gridTaylorT i) v := by
  fin_cases i
  · exact taylorSource_restrict_0 v
  · exact taylorSource_restrict_1 v
  · exact taylorSource_restrict_2 v
  · exact taylorSource_restrict_3 v
  · exact taylorSource_restrict_4 v
  · exact taylorSource_restrict_5 v
  · exact taylorSource_restrict_6 v
  · exact taylorSource_restrict_7 v
  · exact taylorSource_restrict_8 v
  · exact taylorSource_restrict_9 v
  · exact taylorSource_restrict_10 v
  · exact taylorSource_restrict_11 v
  · exact taylorSource_restrict_12 v
  · exact taylorSource_restrict_13 v
  · exact taylorSource_restrict_14 v
  · exact taylorSource_restrict_15 v
  · exact taylorSource_restrict_16 v
  · exact taylorSource_restrict_17 v
  · exact taylorSource_restrict_18 v
  · exact taylorSource_restrict_19 v
  · exact taylorSource_restrict_20 v
  · exact taylorSource_restrict_21 v
  · exact taylorSource_restrict_22 v
  · exact taylorSource_restrict_23 v
  · exact taylorSource_restrict_24 v
  · exact taylorSource_restrict_25 v
  · exact taylorSource_restrict_26 v
  · exact taylorSource_restrict_27 v
  · exact taylorSource_restrict_28 v
  · exact taylorSource_restrict_29 v
  · exact taylorSource_restrict_30 v
  · exact taylorSource_restrict_31 v
  · exact taylorSource_restrict_32 v
  · exact taylorSource_restrict_33 v
  · exact taylorSource_restrict_34 v
  · exact taylorSource_restrict_35 v
  · exact taylorSource_restrict_36 v
  · exact taylorSource_restrict_37 v
  · exact taylorSource_restrict_38 v
  · exact taylorSource_restrict_39 v
  · exact taylorSource_restrict_40 v
  · exact taylorSource_restrict_41 v
  · exact taylorSource_restrict_42 v
  · exact taylorSource_restrict_43 v
  · exact taylorSource_restrict_44 v
  · exact taylorSource_restrict_45 v
  · exact taylorSource_restrict_46 v
  · exact taylorSource_restrict_47 v
  · exact taylorSource_restrict_48 v
  · exact taylorSource_restrict_49 v
  · exact taylorSource_restrict_50 v
  · exact taylorSource_restrict_51 v
  · exact taylorSource_restrict_52 v
  · exact taylorSource_restrict_53 v
  · exact taylorSource_restrict_54 v
  · exact taylorSource_restrict_55 v
  · exact taylorSource_restrict_56 v
  · exact taylorSource_restrict_57 v
  · exact taylorSource_restrict_58 v
  · exact taylorSource_restrict_59 v
  · exact taylorSource_restrict_60 v
  · exact taylorSource_restrict_61 v
  · exact taylorSource_restrict_62 v
  · exact taylorSource_restrict_63 v
  · exact taylorSource_restrict_64 v
  · exact taylorSource_restrict_65 v
  · exact taylorSource_restrict_66 v
  · exact taylorSource_restrict_67 v
  · exact taylorSource_restrict_68 v
  · exact taylorSource_restrict_69 v
  · exact taylorSource_restrict_70 v

theorem entireSource_restrict (v : Fin 780→ℂ) (i : Fin 11) :
    gridSample (gridEntireQ i) 0 (extension support (fun j => v (support j)))=gridSample (gridEntireQ i) 0 v := by
  fin_cases i
  · exact entireSource_restrict_0 v
  · exact entireSource_restrict_1 v
  · exact entireSource_restrict_2 v
  · exact entireSource_restrict_3 v
  · exact entireSource_restrict_4 v
  · exact entireSource_restrict_5 v
  · exact entireSource_restrict_6 v
  · exact entireSource_restrict_7 v
  · exact entireSource_restrict_8 v
  · exact entireSource_restrict_9 v
  · exact entireSource_restrict_10 v

theorem heckeSource_restrict (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) (i : Fin 51) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) i=gridHeckeLeading m f s v i := by
  fin_cases i
  · exact heckeSource_restrict_0 m f s v
  · exact heckeSource_restrict_1 m f s v
  · exact heckeSource_restrict_2 m f s v
  · exact heckeSource_restrict_3 m f s v
  · exact heckeSource_restrict_4 m f s v
  · exact heckeSource_restrict_5 m f s v
  · exact heckeSource_restrict_6 m f s v
  · exact heckeSource_restrict_7 m f s v
  · exact heckeSource_restrict_8 m f s v
  · exact heckeSource_restrict_9 m f s v
  · exact heckeSource_restrict_10 m f s v
  · exact heckeSource_restrict_11 m f s v
  · exact heckeSource_restrict_12 m f s v
  · exact heckeSource_restrict_13 m f s v
  · exact heckeSource_restrict_14 m f s v
  · exact heckeSource_restrict_15 m f s v
  · exact heckeSource_restrict_16 m f s v
  · exact heckeSource_restrict_17 m f s v
  · exact heckeSource_restrict_18 m f s v
  · exact heckeSource_restrict_19 m f s v
  · exact heckeSource_restrict_20 m f s v
  · exact heckeSource_restrict_21 m f s v
  · exact heckeSource_restrict_22 m f s v
  · exact heckeSource_restrict_23 m f s v
  · exact heckeSource_restrict_24 m f s v
  · exact heckeSource_restrict_25 m f s v
  · exact heckeSource_restrict_26 m f s v
  · exact heckeSource_restrict_27 m f s v
  · exact heckeSource_restrict_28 m f s v
  · exact heckeSource_restrict_29 m f s v
  · exact heckeSource_restrict_30 m f s v
  · exact heckeSource_restrict_31 m f s v
  · exact heckeSource_restrict_32 m f s v
  · exact heckeSource_restrict_33 m f s v
  · exact heckeSource_restrict_34 m f s v
  · exact heckeSource_restrict_35 m f s v
  · exact heckeSource_restrict_36 m f s v
  · exact heckeSource_restrict_37 m f s v
  · exact heckeSource_restrict_38 m f s v
  · exact heckeSource_restrict_39 m f s v
  · exact heckeSource_restrict_40 m f s v
  · exact heckeSource_restrict_41 m f s v
  · exact heckeSource_restrict_42 m f s v
  · exact heckeSource_restrict_43 m f s v
  · exact heckeSource_restrict_44 m f s v
  · exact heckeSource_restrict_45 m f s v
  · exact heckeSource_restrict_46 m f s v
  · exact heckeSource_restrict_47 m f s v
  · exact heckeSource_restrict_48 m f s v
  · exact heckeSource_restrict_49 m f s v
  · exact heckeSource_restrict_50 m f s v

theorem leadingRows_restrict (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    gridLeadingRows m f ε s (extension support (fun j => v (support j))) i=
      gridLeadingRows m f ε s v i := by
  cases i with
  | word i => simp only [gridLeadingRows,gridGroupLeading,groupIndex_restrict,groupTarget_restrict]
  | taylor i => simp only [gridLeadingRows,gridRamanujanLeading,taylorSource_restrict,taylorTarget_restrict]
  | entire i => exact entireSource_restrict v i
  | hecke i => exact heckeSource_restrict m f s v i
  | infinity i => fin_cases i; exact infinity_restrict_0 v; exact infinity_restrict_1 v

#print axioms leadingRows_restrict

end SmallLevelTwentySixGrid
