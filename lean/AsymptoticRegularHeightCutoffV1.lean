module

public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitDiagonal

open ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

theorem corner_comp_of_subset {s t : Set α} (hst : s⊆t) (x : α) :
    (corner (G:=G) s x).comp (corner t x)=corner s x := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  classical
  simp only [comp_apply,corner_apply]
  by_cases hg : g • x∈s
  · simp only [ite_eq_left hg,ite_eq_left (hst hg)]
  · simp only [ite_eq_right hg]

end AsymptoticOrbitDiagonal

namespace AsymptoticRegularHeightCutoff

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularFoldedLow (Space)
open AsymptoticRegularInclusion

noncomputable def region (Y : ℝ) : Set ℍ := {z | Y≤z.im}

theorem region_measurable (Y : ℝ) : MeasurableSet (region Y) :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_im).measurableSet

noncomputable def projection (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitDiagonal.corner (region Y) z

theorem projection_norm_le (Y : ℝ) (z : ℍ) : ‖projection Y z‖≤1 :=
  AsymptoticOrbitRegion.corner_norm_le _ _

theorem projection_covariant (Y : ℝ) : Covariant (projection Y) :=
  AsymptoticOrbitDiagonal.corner_covariant _

theorem projection_matrix_measurable (Y : ℝ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (projection Y z) a b) :=
  AsymptoticOrbitDiagonal.corner_matrix_measurable
    (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) (region_measurable Y) a b

noncomputable def removedCoefficient (ε Y : ℝ) (z : ℍ) : ℂ :=
  if Y≤z.im then 0 else (weight ε z:ℂ)

theorem removedCoefficient_norm_le {ε Y : ℝ} (hε : 0<ε) (hY : 0≤Y) (z : ℍ) :
    ‖removedCoefficient ε Y z‖≤Y/ε := by
  unfold removedCoefficient
  split_ifs with hz
  · simpa only [norm_zero] using div_nonneg hY hε.le
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos hε z)]
    exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (le_of_not_ge hz) hε.le)

noncomputable def removed {ε Y : ℝ} (hε : 0<ε) (hY : 0≤Y) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator 1 (removedCoefficient ε Y) (div_nonneg hY hε.le)
    (removedCoefficient_norm_le hε hY) z

theorem inclusion_sub_cut {ε Y : ℝ} (hε : 0<ε) (hY : 0≤Y) (z : ℍ) :
    inclusion hε z-(projection Y z).comp (inclusion hε z)=removed hε hY z := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  classical
  simp only [sub_apply,comp_apply,lp.coeFn_sub,Pi.sub_apply,projection,
    AsymptoticOrbitDiagonal.corner_apply,inclusion_apply,removed,AsymptoticOrbitBranch.operator_apply,
    one_mul,removedCoefficient,region,Set.mem_ofPred_eq]
  split_ifs <;> simp

theorem inclusion_cut_error {ε Y : ℝ} (hε : 0<ε) (hY : 0≤Y) (z : ℍ) :
    ‖inclusion hε z-(projection Y z).comp (inclusion hε z)‖≤Y/ε := by
  rw [inclusion_sub_cut hε hY z]
  exact AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

#print axioms AsymptoticOrbitDiagonal.corner_comp_of_subset
#print axioms projection_norm_le
#print axioms projection_covariant
#print axioms projection_matrix_measurable
#print axioms inclusion_cut_error

end AsymptoticRegularHeightCutoff
