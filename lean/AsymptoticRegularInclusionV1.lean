module

public import AsymptoticRegularReconstructionTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularInclusion

open UpperHalfPlane Set MeasureTheory AsymptoticRegularTrace
open AsymptoticRegularFoldedLow (Space)

noncomputable def weight (ε : ℝ) (z : ℍ) : ℝ := min (z.im/ε) 1

theorem weight_pos {ε : ℝ} (hε : 0<ε) (z : ℍ) : 0<weight ε z :=
  lt_min (div_pos z.im_pos hε) zero_lt_one

theorem weight_norm_le {ε : ℝ} (hε : 0<ε) (z : ℍ) : ‖(weight ε z:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos hε z)]
  exact min_le_right _ _

theorem weight_continuous (ε : ℝ) : Continuous (weight ε) := by
  unfold weight
  fun_prop

theorem weight_eq_one {ε : ℝ} (hε : 0<ε) (z : ℍ) (hz : ε≤z.im) : weight ε z=1 :=
  min_eq_right ((le_div_iff₀ hε).mpr (by simpa using hz))

/-- Inclusion from capped exponent t to t+1 on counting coordinates. -/
noncomputable def inclusion {ε : ℝ} (hε : 0<ε) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator 1 (fun z => (weight ε z:ℂ)) zero_le_one (weight_norm_le hε) z

theorem inclusion_apply {ε : ℝ} (hε : 0<ε) (z : ℍ) (f : Space)
    (g : AsymptoticRationalGroup.Group) : inclusion hε z f g=(weight ε (g • z):ℂ)*f g := by
  change (weight ε (g • z):ℂ)*f (1*g)=_
  rw [one_mul]

theorem inclusion_norm_le {ε : ℝ} (hε : 0<ε) (z : ℍ) : ‖inclusion hε z‖≤1 :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

theorem inclusion_covariant {ε : ℝ} (hε : 0<ε) : Covariant (inclusion hε) :=
  AsymptoticOrbitBranch.operator_covariant _ _ _ (weight_norm_le hε)

theorem inclusion_matrix_measurable {ε : ℝ} (hε : 0<ε) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (inclusion hε z) g h) :=
  AsymptoticOrbitBranch.operator_matrix_measurable
    (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) _ _ _ _
    (Complex.continuous_ofReal.comp (weight_continuous ε)).measurable g h

theorem corner_inclusion {ε : ℝ} (hε : 0<ε) (s : Set ℍ) (hs : s⊆{z | ε≤z.im})
    (z : ℍ) (f : Space) :
    AsymptoticOrbitDiagonal.corner s z (inclusion hε z f)=AsymptoticOrbitDiagonal.corner s z f := by
  apply lp.ext
  funext g
  classical
  simp only [AsymptoticOrbitDiagonal.corner_apply,inclusion_apply]
  by_cases hg : g • z∈s
  · rw [ite_eq_left hg,ite_eq_left hg,weight_eq_one hε _ (hs hg),Complex.ofReal_one,one_mul]
  · rw [ite_eq_right hg,ite_eq_right hg]

#print axioms inclusion_norm_le
#print axioms inclusion_covariant
#print axioms inclusion_matrix_measurable
#print axioms corner_inclusion

end AsymptoticRegularInclusion
