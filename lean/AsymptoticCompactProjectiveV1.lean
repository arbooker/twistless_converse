module

public import AsymptoticRegularCompactSelectionV1
public import AsymptoticIntegralTranslationsV1
public import AsymptoticIntegralBranchSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRationalBranches

open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticIntegralSubgroup UpperHalfPlane

theorem ofMatrix_eq_of_projective (g h : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) (hh : 0<(realMatrix h).det.val)
    (he : rationalMap g=rationalMap h) : ofMatrix g hg=ofMatrix h hh := by
  apply Subtype.ext
  apply Subtype.ext
  exact he

theorem action_eq_of_projective (g h : GL (Fin 2) ℚ)
    (he : rationalMap g=rationalMap h) (z : ℍ) : realMatrix g • z=realMatrix h • z := by
  have hz := congrArg (fun a => a • z) he
  simpa only [rationalMap,MonoidHom.comp_apply,pglMk_smul,realMatrix] using hz

theorem compactFold_label_eq (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (n : ℤ) :
    compactFold g hg n=translationLabel (-(n:ℚ))*ofMatrix g hg := by
  apply Subtype.ext
  apply Subtype.ext
  exact map_mul rationalMap _ _

theorem compactFold_projective_eq (g h : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) (hh : 0<(realMatrix h).det.val)
    (he : rationalMap g=rationalMap h) (n : ℤ) : compactFold g hg n=compactFold h hh n := by
  rw [compactFold_label_eq,compactFold_label_eq,ofMatrix_eq_of_projective g h hg hh he]

#print axioms ofMatrix_eq_of_projective
#print axioms action_eq_of_projective
#print axioms compactFold_label_eq
#print axioms compactFold_projective_eq

end AsymptoticRationalBranches

namespace AsymptoticRegularCompactBranch

open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches UpperHalfPlane
open AsymptoticCompactBranch (Data coefficient ratio)

/-- The actual compact counting operator depends only on the projective
matrix, including its cap ratio and selected strip fold. -/
theorem operator_projective_eq (g h : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) (hh : 0<(realMatrix h).det.val)
    (he : rationalMap g=rationalMap h) {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (E : Data (realMatrix h) s ε t) (x : ℍ) :
    operator g hg hε t D x=operator h hh hε t E x := by
  have ha := action_eq_of_projective g h he
  have hc : coefficient (realMatrix g) s ε t=coefficient (realMatrix h) s ε t := by
    unfold coefficient ratio
    simp only [ha]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  rw [operator_selected,operator_selected,hc,ha,compactFold_projective_eq g h hg hh he]

#print axioms operator_projective_eq

end AsymptoticRegularCompactBranch

namespace AsymptoticIntegralSubgroup

open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticSubgroupSupport UpperHalfPlane
open AsymptoticCompactBranch (Data)

variable (q : ℕ) [Fact q.Prime]

theorem compactFold_mem_of_label (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (hi : ofMatrix g hg∈integralGroup q) (n : ℤ) : compactFold g hg n∈integralGroup q := by
  rw [compactFold_label_eq]
  apply (integralGroup q).mul_mem _ hi
  simpa only [Int.cast_neg] using translationLabel_integer_mem q (-n)

/-- Integrality of the projective label suffices. In particular this
covers unreduced fresh-prime matrices whose entries have denominators q. -/
theorem compact_operator_supported_of_label (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (hi : ofMatrix g hg∈integralGroup q) {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (x : ℍ) :
    Supported (integralGroup q) (AsymptoticRegularCompactBranch.operator g hg hε t D x) := by
  apply supported_comp
  · exact supported_finsetSum _ _ _ (fun n _ =>
      supported_weighted_branch _ _ (compactFold_mem_of_label q g hg hi n) _ _ _ x)
  · exact supported_corner _ _ _

#print axioms compactFold_mem_of_label
#print axioms compact_operator_supported_of_label

end AsymptoticIntegralSubgroup
