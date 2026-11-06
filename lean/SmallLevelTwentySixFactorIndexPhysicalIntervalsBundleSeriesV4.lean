module
public import SmallLevelTwentySixFactorIndexXRootNormBoundsSeriesV4
public import SmallLevelTwentySixFactorIndexYRootNormBoundsSeriesV4
public import SmallLevelTwentySixPhysicalModulusTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixFactor6Physical
open SmallLevelTwentySixPhysicalModulus

section
local notation "aQ" => SmallLevelTwentySixFactor6XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor6XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor6YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor6YRoot.upperQ
theorem row0_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 0:ℝ) (bQ 0:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 0 ∧ 0≤cQ j ∧
      ((1<aQ 0 ∧ ((dQ j)^6<(aQ 0)^19 ∨ (bQ 0)^127<(cQ j)^40)) ∨
       (bQ 0<1 ∧ ((dQ j)^40<(aQ 0)^127 ∨ (bQ 0)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row0_excluded
theorem row1_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 1:ℝ) (bQ 1:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 1 ∧ 0≤cQ j ∧
      ((1<aQ 1 ∧ ((dQ j)^6<(aQ 1)^19 ∨ (bQ 1)^127<(cQ j)^40)) ∨
       (bQ 1<1 ∧ ((dQ j)^40<(aQ 1)^127 ∨ (bQ 1)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row1_excluded
theorem row2_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 2:ℝ) (bQ 2:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 2 ∧ 0≤cQ j ∧
      ((1<aQ 2 ∧ ((dQ j)^6<(aQ 2)^19 ∨ (bQ 2)^127<(cQ j)^40)) ∨
       (bQ 2<1 ∧ ((dQ j)^40<(aQ 2)^127 ∨ (bQ 2)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row2_excluded
end

section
local notation "aQ" => SmallLevelTwentySixFactor6XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor6XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor6YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor6YRoot.upperQ
theorem row3_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 3:ℝ) (bQ 3:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 3 ∧ 0≤cQ j ∧
      ((1<aQ 3 ∧ ((dQ j)^6<(aQ 3)^19 ∨ (bQ 3)^127<(cQ j)^40)) ∨
       (bQ 3<1 ∧ ((dQ j)^40<(aQ 3)^127 ∨ (bQ 3)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row3_excluded
theorem row4_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 4:ℝ) (bQ 4:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 4 ∧ 0≤cQ j ∧
      ((1<aQ 4 ∧ ((dQ j)^6<(aQ 4)^19 ∨ (bQ 4)^127<(cQ j)^40)) ∨
       (bQ 4<1 ∧ ((dQ j)^40<(aQ 4)^127 ∨ (bQ 4)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row4_excluded
theorem row5_excluded (j : Fin 18) :
    SharpIntervalExcluded (aQ 5:ℝ) (bQ 5:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 18, (0:ℚ)≤aQ 5 ∧ 0≤cQ j ∧
      ((1<aQ 5 ∧ ((dQ j)^6<(aQ 5)^19 ∨ (bQ 5)^127<(cQ j)^40)) ∨
       (bQ 5<1 ∧ ((dQ j)^40<(aQ 5)^127 ∨ (bQ 5)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row5_excluded
end

end SmallLevelTwentySixFactor6Physical
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixFactor7Physical
open SmallLevelTwentySixPhysicalModulus

section
local notation "aQ" => SmallLevelTwentySixFactor7XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor7XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor7YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor7YRoot.upperQ
theorem row0_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 0:ℝ) (bQ 0:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 0 ∧ 0≤cQ j ∧
      ((1<aQ 0 ∧ ((dQ j)^6<(aQ 0)^19 ∨ (bQ 0)^127<(cQ j)^40)) ∨
       (bQ 0<1 ∧ ((dQ j)^40<(aQ 0)^127 ∨ (bQ 0)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row0_excluded
theorem row1_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 1:ℝ) (bQ 1:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 1 ∧ 0≤cQ j ∧
      ((1<aQ 1 ∧ ((dQ j)^6<(aQ 1)^19 ∨ (bQ 1)^127<(cQ j)^40)) ∨
       (bQ 1<1 ∧ ((dQ j)^40<(aQ 1)^127 ∨ (bQ 1)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row1_excluded
theorem row2_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 2:ℝ) (bQ 2:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 2 ∧ 0≤cQ j ∧
      ((1<aQ 2 ∧ ((dQ j)^6<(aQ 2)^19 ∨ (bQ 2)^127<(cQ j)^40)) ∨
       (bQ 2<1 ∧ ((dQ j)^40<(aQ 2)^127 ∨ (bQ 2)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row2_excluded
end

section
local notation "aQ" => SmallLevelTwentySixFactor7XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor7XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor7YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor7YRoot.upperQ
theorem row3_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 3:ℝ) (bQ 3:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 3 ∧ 0≤cQ j ∧
      ((1<aQ 3 ∧ ((dQ j)^6<(aQ 3)^19 ∨ (bQ 3)^127<(cQ j)^40)) ∨
       (bQ 3<1 ∧ ((dQ j)^40<(aQ 3)^127 ∨ (bQ 3)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row3_excluded
theorem row4_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 4:ℝ) (bQ 4:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 4 ∧ 0≤cQ j ∧
      ((1<aQ 4 ∧ ((dQ j)^6<(aQ 4)^19 ∨ (bQ 4)^127<(cQ j)^40)) ∨
       (bQ 4<1 ∧ ((dQ j)^40<(aQ 4)^127 ∨ (bQ 4)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row4_excluded
theorem row5_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 5:ℝ) (bQ 5:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 5 ∧ 0≤cQ j ∧
      ((1<aQ 5 ∧ ((dQ j)^6<(aQ 5)^19 ∨ (bQ 5)^127<(cQ j)^40)) ∨
       (bQ 5<1 ∧ ((dQ j)^40<(aQ 5)^127 ∨ (bQ 5)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row5_excluded
end

section
local notation "aQ" => SmallLevelTwentySixFactor7XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor7XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor7YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor7YRoot.upperQ
theorem row6_excluded (j : Fin 14) :
    SharpIntervalExcluded (aQ 6:ℝ) (bQ 6:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 14, (0:ℚ)≤aQ 6 ∧ 0≤cQ j ∧
      ((1<aQ 6 ∧ ((dQ j)^6<(aQ 6)^19 ∨ (bQ 6)^127<(cQ j)^40)) ∨
       (bQ 6<1 ∧ ((dQ j)^40<(aQ 6)^127 ∨ (bQ 6)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row6_excluded
end

end SmallLevelTwentySixFactor7Physical
end
