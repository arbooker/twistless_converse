module
public import SmallLevelTwentySixFactorIndexPhysicalIntervalsBundleSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6Physical
open SmallLevelTwentySixPhysicalModulus
local notation "aQ" => SmallLevelTwentySixFactor6XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor6XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor6YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor6YRoot.upperQ
theorem all_intervals_excluded (i : Fin 6) (j : Fin 18) :
    SharpIntervalExcluded (aQ i:ℝ) (bQ i:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  fin_cases i
  · exact row0_excluded j
  · exact row1_excluded j
  · exact row2_excluded j
  · exact row3_excluded j
  · exact row4_excluded j
  · exact row5_excluded j

/-- Exclusion of this entire extra factor on the physical low curve, for
any unit-modulus sign. Only ordinary kernel-checked root certificates are used. -/
theorem no_signed_low_curve (h u : ℂ) (hu : ‖u‖=1)
    (hx : SmallLevelTwentySixPariFinalFactors.factor6 (u*(2:ℂ)^h)=0)
    (hy : SmallLevelTwentySixPariFirstChart.lowCurve (u*(2:ℂ)^h) ((9:ℂ)^h) 0 0 0 0 0=0) : False := by
  have hx0 : SmallLevelTwentySixFactor6XRoot.pRoot.eval (u*(2:ℂ)^h)=0 :=
    (mul_eq_zero.mp ((SmallLevelTwentySixFactor6XRoot.factor_binding _).symm.trans hx)).resolve_left (by norm_num)
  have hy0 : SmallLevelTwentySixFactor6YRoot.pRoot.eval ((9:ℂ)^h)=0 :=
    (SmallLevelTwentySixFactor6YRoot.squarefree_binding _ _).symm.trans
      (SmallLevelTwentySixLowCurveFactor6.low_curve_squarefree _ _ hx hy)
  obtain ⟨i,hi⟩:=SmallLevelTwentySixFactor6XRoot.root_norm_bounds _ hx0
  obtain ⟨j,hj⟩:=SmallLevelTwentySixFactor6YRoot.root_norm_bounds _ hy0
  rw [norm_mul,hu,one_mul] at hi
  exact sharp_interval_excludes_physical _ _ _ _ (all_intervals_excluded i j) h hi hj

#print axioms all_intervals_excluded
#print axioms no_signed_low_curve

end SmallLevelTwentySixFactor6Physical
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7Physical
open SmallLevelTwentySixPhysicalModulus
local notation "aQ" => SmallLevelTwentySixFactor7XRoot.lowerQ
local notation "bQ" => SmallLevelTwentySixFactor7XRoot.upperQ
local notation "cQ" => SmallLevelTwentySixFactor7YRoot.lowerQ
local notation "dQ" => SmallLevelTwentySixFactor7YRoot.upperQ
theorem all_intervals_excluded (i : Fin 7) (j : Fin 14) :
    SharpIntervalExcluded (aQ i:ℝ) (bQ i:ℝ) (cQ j:ℝ) (dQ j:ℝ) := by
  fin_cases i
  · exact row0_excluded j
  · exact row1_excluded j
  · exact row2_excluded j
  · exact row3_excluded j
  · exact row4_excluded j
  · exact row5_excluded j
  · exact row6_excluded j

/-- Exclusion of this entire extra factor on the physical low curve, for
any unit-modulus sign. Only ordinary kernel-checked root certificates are used. -/
theorem no_signed_low_curve (h u : ℂ) (hu : ‖u‖=1)
    (hx : SmallLevelTwentySixPariFinalFactors.factor7 (u*(2:ℂ)^h)=0)
    (hy : SmallLevelTwentySixPariFirstChart.lowCurve (u*(2:ℂ)^h) ((9:ℂ)^h) 0 0 0 0 0=0) : False := by
  have hx0 : SmallLevelTwentySixFactor7XRoot.pRoot.eval (u*(2:ℂ)^h)=0 :=
    (mul_eq_zero.mp ((SmallLevelTwentySixFactor7XRoot.factor_binding _).symm.trans hx)).resolve_left (by norm_num)
  have hy0 : SmallLevelTwentySixFactor7YRoot.pRoot.eval ((9:ℂ)^h)=0 :=
    (SmallLevelTwentySixFactor7YRoot.squarefree_binding _ _).symm.trans
      (SmallLevelTwentySixLowCurveFactor7.low_curve_squarefree _ _ hx hy)
  obtain ⟨i,hi⟩:=SmallLevelTwentySixFactor7XRoot.root_norm_bounds _ hx0
  obtain ⟨j,hj⟩:=SmallLevelTwentySixFactor7YRoot.root_norm_bounds _ hy0
  rw [norm_mul,hu,one_mul] at hi
  exact sharp_interval_excludes_physical _ _ _ _ (all_intervals_excluded i j) h hi hj

#print axioms all_intervals_excluded
#print axioms no_signed_low_curve

end SmallLevelTwentySixFactor7Physical
end
