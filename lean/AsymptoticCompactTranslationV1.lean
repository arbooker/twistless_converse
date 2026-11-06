module

public import AsymptoticCompactProjectiveV1
public import AsymptoticSubgroupOrthogonalityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCompactTranslation

open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticRationalGroup
open AsymptoticIntegralSubgroup AsymptoticRegularCompactBranch
open AsymptoticCompactBranch (Data cap ratio coefficient)
open UpperHalfPlane Matrix

theorem label_action (r : ℚ) (z : ℍ) :
    translationLabel r • z=AsymptoticMobiusFold.translation (r:ℝ) • z := by
  rw [translationLabel,ofMatrix_action,realMatrix_translation]

theorem label_im (r : ℚ) (z : ℍ) : (translationLabel r • z).im=z.im := by
  rw [label_action]
  have he := congrArg Complex.im (AsymptoticMobiusFold.translation_action (r:ℝ) z)
  simpa using he

theorem cap_translate (r : ℚ) (ε : ℝ) (t : ℕ) (z : ℍ) :
    cap ε t (translationLabel r • z)=cap ε t z := by
  simp only [cap,label_im]

theorem product_action (g : GL (Fin 2) ℚ) (r : ℚ) (z : ℍ) :
    realMatrix (g*AsymptoticMobiusFold.translation r) • z=
      realMatrix g • (translationLabel r • z) := by
  change (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g*AsymptoticMobiusFold.translation r)) • z=_
  rw [map_mul,mul_smul]
  change realMatrix g • (realMatrix (AsymptoticMobiusFold.translation r) • z)=_
  rw [realMatrix_translation,label_action]

theorem product_positive (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (r : ℚ) :
    0<(realMatrix (g*AsymptoticMobiusFold.translation r)).det.val := by
  change 0<((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (g*AsymptoticMobiusFold.translation r)).det).val
  rw [map_mul,map_mul,Units.val_mul]
  change 0<(realMatrix g).det.val*(realMatrix (AsymptoticMobiusFold.translation r)).det.val
  rw [realMatrix_translation,AsymptoticMobiusFold.translation_det,mul_one]
  exact hg

theorem fold_product (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (r : ℚ) (n : ℤ) :
    compactFold (g*AsymptoticMobiusFold.translation r) (product_positive g hg r) n=
      compactFold g hg n*translationLabel r := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticMobiusFold.translation (-(n:ℚ))*(g*AsymptoticMobiusFold.translation r))=
    rationalMap (AsymptoticMobiusFold.translation (-(n:ℚ))*g)*rationalMap (AsymptoticMobiusFold.translation r)
  rw [← map_mul,mul_assoc]

theorem coefficient_translate (g : GL (Fin 2) ℚ) (r : ℚ) (s : Set ℍ) (ε : ℝ) (t : ℕ) (z : ℍ) :
    coefficient (realMatrix g) s ε t (translationLabel r • z)=
      coefficient (realMatrix (g*AsymptoticMobiusFold.translation r))
        ((fun z : ℍ => translationLabel r • z) ⁻¹' s) ε t z := by
  classical
  simp only [coefficient,Set.indicator_apply,Set.mem_preimage,ratio,product_action,cap_translate]

/-- Translating the full-orbit output moves the compact cutoff and
right-multiplies the input branch matrix. Cap weights are unchanged by
translations, so this is an identity of the actual bounded operators. -/
theorem operator_translate (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (r : ℚ) {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t)
    (E : Data (realMatrix (g*AsymptoticMobiusFold.translation r))
      ((fun z : ℍ => translationLabel r • z) ⁻¹' s) ε t) (x : ℍ) :
    (AsymptoticSubgroupSupport.translation (translationLabel r)).comp (operator g hg hε t D x)=
      operator (g*AsymptoticMobiusFold.translation r) (product_positive g hg r) hε t E x := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  change operator g hg hε t D x f (translationLabel r*a)=_
  rw [operator_selected,operator_selected,mul_smul,coefficient_translate,product_action,fold_product]
  rw [mul_assoc]

theorem preimage_compact (r : ℚ) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact ((fun z : ℍ => translationLabel r • z) ⁻¹' s) := by
  have he : ((fun z : ℍ => translationLabel r • z) ⁻¹' s)=
      (fun z : ℍ => (translationLabel r)⁻¹ • z) '' s := by
    ext z
    constructor
    · intro hz
      exact ⟨translationLabel r • z,hz,inv_smul_smul _ _⟩
    · rintro ⟨w,hw,rfl⟩
      simpa only [Set.mem_preimage,smul_inv_smul] using hw
  rw [he]
  exact hs.image (action_continuous _)

#print axioms label_action
#print axioms label_im
#print axioms cap_translate
#print axioms product_action
#print axioms product_positive
#print axioms fold_product
#print axioms coefficient_translate
#print axioms operator_translate
#print axioms preimage_compact

end AsymptoticCompactTranslation
