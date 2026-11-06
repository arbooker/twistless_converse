module

public import SmallLevelTwentySixExceptionalSevenXRootTheoryV4
public import SmallLevelTwentySixExceptionalSevenYRootTheoryV4
public import SmallLevelTwentySixPhysicalModulusTheoryV4

/-! Consolidated chapter: SmallLevelTwentySixExceptionalSevenPhysical. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixExceptionalSevenPhysicalIntervalsBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixExceptionalSevenPhysical
open SmallLevelTwentySixPhysicalModulus

section
local notation "aQ" => SmallLevelTwentySixExceptionalSevenXRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixExceptionalSevenXRoot.upperQ
local notation "cQ" => SmallLevelTwentySixExceptionalSevenYRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixExceptionalSevenYRoot.upperQ
theorem row0_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 0:ℝ) (bQ 0:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 0 ∧ 0≤cQ j ∧
      ((1<aQ 0 ∧ ((dQ j)^6<(aQ 0)^19 ∨ (bQ 0)^127<(cQ j)^40)) ∨
       (bQ 0<1 ∧ ((dQ j)^40<(aQ 0)^127 ∨ (bQ 0)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row0_excluded
theorem row1_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 1:ℝ) (bQ 1:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 1 ∧ 0≤cQ j ∧
      ((1<aQ 1 ∧ ((dQ j)^6<(aQ 1)^19 ∨ (bQ 1)^127<(cQ j)^40)) ∨
       (bQ 1<1 ∧ ((dQ j)^40<(aQ 1)^127 ∨ (bQ 1)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row1_excluded
theorem row2_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 2:ℝ) (bQ 2:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 2 ∧ 0≤cQ j ∧
      ((1<aQ 2 ∧ ((dQ j)^6<(aQ 2)^19 ∨ (bQ 2)^127<(cQ j)^40)) ∨
       (bQ 2<1 ∧ ((dQ j)^40<(aQ 2)^127 ∨ (bQ 2)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row2_excluded
end

section
local notation "aQ" => SmallLevelTwentySixExceptionalSevenXRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixExceptionalSevenXRoot.upperQ
local notation "cQ" => SmallLevelTwentySixExceptionalSevenYRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixExceptionalSevenYRoot.upperQ
theorem row3_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 3:ℝ) (bQ 3:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 3 ∧ 0≤cQ j ∧
      ((1<aQ 3 ∧ ((dQ j)^6<(aQ 3)^19 ∨ (bQ 3)^127<(cQ j)^40)) ∨
       (bQ 3<1 ∧ ((dQ j)^40<(aQ 3)^127 ∨ (bQ 3)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row3_excluded
theorem row4_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 4:ℝ) (bQ 4:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 4 ∧ 0≤cQ j ∧
      ((1<aQ 4 ∧ ((dQ j)^6<(aQ 4)^19 ∨ (bQ 4)^127<(cQ j)^40)) ∨
       (bQ 4<1 ∧ ((dQ j)^40<(aQ 4)^127 ∨ (bQ 4)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row4_excluded
theorem row5_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 5:ℝ) (bQ 5:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 5 ∧ 0≤cQ j ∧
      ((1<aQ 5 ∧ ((dQ j)^6<(aQ 5)^19 ∨ (bQ 5)^127<(cQ j)^40)) ∨
       (bQ 5<1 ∧ ((dQ j)^40<(aQ 5)^127 ∨ (bQ 5)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row5_excluded
end

section
local notation "aQ" => SmallLevelTwentySixExceptionalSevenXRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixExceptionalSevenXRoot.upperQ
local notation "cQ" => SmallLevelTwentySixExceptionalSevenYRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixExceptionalSevenYRoot.upperQ
theorem row6_excluded (j : Fin 7) :
    SharpIntervalExcluded (aQ 6:ℝ) (bQ 6:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  have h : ∀ j : Fin 7, (0:ℚ)≤aQ 6 ∧ 0≤cQ j ∧
      ((1<aQ 6 ∧ ((dQ j)^6<(aQ 6)^19 ∨ (bQ 6)^127<(cQ j)^40)) ∨
       (bQ 6<1 ∧ ((dQ j)^40<(aQ 6)^127 ∨ (bQ 6)^19<(cQ j)^6))) := by decide +kernel
  unfold SharpIntervalExcluded
  exact_mod_cast h j
#print axioms row6_excluded
end

end SmallLevelTwentySixExceptionalSevenPhysical
end
end

/-! ## SmallLevelTwentySixExceptionalSevenPhysicalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalSevenPhysical
open SmallLevelTwentySixPhysicalModulus
local notation "aQ" => SmallLevelTwentySixExceptionalSevenXRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixExceptionalSevenXRoot.upperQ
local notation "cQ" => SmallLevelTwentySixExceptionalSevenYRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixExceptionalSevenYRoot.upperQ
theorem all_intervals_excluded (i j : Fin 7) :
    SharpIntervalExcluded (aQ i:ℝ) (bQ i:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  fin_cases i
  · exact row0_excluded j
  · exact row1_excluded j
  · exact row2_excluded j
  · exact row3_excluded j
  · exact row4_excluded j
  · exact row5_excluded j
  · exact row6_excluded j

theorem no_signed_constant (h u : ℂ) (hu : ‖u‖=1)
    (hx : SmallLevelTwentySixExceptionalCurve.extraFactor7 (u*(2:ℂ)^h) ((9:ℂ)^h)=0)
    (hc : SmallLevelTwentySixPariFirstChart.constantTerm (u*(2:ℂ)^h) ((9:ℂ)^h)=0) : False := by
  have hx0 : SmallLevelTwentySixExceptionalSevenXRoot.pRoot.eval (u*(2:ℂ)^h)=0 :=
    (mul_eq_zero.mp ((SmallLevelTwentySixExceptionalSevenXRoot.polynomial_binding _ _).symm.trans hx)).resolve_left (by norm_num)
  have hy0 : SmallLevelTwentySixExceptionalSevenYRoot.pRoot.eval ((9:ℂ)^h)=0 :=
    (SmallLevelTwentySixExceptionalSevenYRoot.polynomial_binding _ _).symm.trans
      (SmallLevelTwentySixExceptionalCurve.exceptional_resultant_zero _ _ hx hc)
  obtain ⟨i,hi⟩:=SmallLevelTwentySixExceptionalSevenXRoot.root_norm_bounds _ hx0
  obtain ⟨j,hj⟩:=SmallLevelTwentySixExceptionalSevenYRoot.root_norm_bounds _ hy0
  rw [norm_mul,hu,one_mul] at hi
  exact sharp_interval_excludes_physical _ _ _ _ (all_intervals_excluded i j) h hi hj

/-- The two exceptional elimination factors cannot occur on the physical
constant-zero locus. Their derivation from the original small rows is separate. -/
theorem no_signed_exceptional_branches (h u : ℂ) (hu : ‖u‖=1)
    (hc : SmallLevelTwentySixPariFirstChart.constantTerm (u*(2:ℂ)^h) ((9:ℂ)^h)=0)
    (hx : SmallLevelTwentySixPariFinalFactors.factor6 (u*(2:ℂ)^h)=0 ∨
      SmallLevelTwentySixExceptionalCurve.extraFactor7 (u*(2:ℂ)^h) ((9:ℂ)^h)=0) : False := by
  rcases hx with hx|hx
  · exact SmallLevelTwentySixExceptionalCurve.no_factor6_constant h u hu hc hx
  · exact no_signed_constant h u hu hx hc

#print axioms no_signed_constant
#print axioms no_signed_exceptional_branches

end SmallLevelTwentySixExceptionalSevenPhysical
end
end
