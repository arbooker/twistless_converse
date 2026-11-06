module

public import AsymptoticCompactTranslationV1
public import AsymptoticRegularBranchFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCompactFamilyTranslation

open AsymptoticRegularBranchFamily AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRationalGroup AsymptoticIntegralSubgroup AsymptoticCompactTranslation UpperHalfPlane

noncomputable def right (b : Branch) (r : ℚ) : Branch :=
  ⟨b.matrix*AsymptoticMobiusFold.translation r,product_positive b.matrix b.positive r⟩

theorem right_label (b : Branch) (r : ℚ) :
    ofMatrix (right b r).matrix (right b r).positive=ofMatrix b.matrix b.positive*translationLabel r := by
  apply Subtype.ext
  apply Subtype.ext
  exact map_mul rationalMap _ _

theorem compact_translate (b : Branch) (r : ℚ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticSubgroupSupport.translation (translationLabel r)).comp (compact b hs hε t x)=
      compact (right b r) (preimage_compact r hs) hε t x :=
  operator_translate b.matrix b.positive r hε t _ _ x

def shifted (r : ℚ) (s : Set ℍ) : Set ℍ := (fun z : ℍ => translationLabel r • z) '' s

theorem shifted_compact (r : ℚ) {s : Set ℍ} (hs : IsCompact s) : IsCompact (shifted r s) :=
  hs.image (action_continuous _)

theorem preimage_shifted (r : ℚ) (s : Set ℍ) :
    (fun z : ℍ => translationLabel r • z) ⁻¹' shifted r s=s := by
  apply Set.preimage_image_eq
  intro z w h
  have he := congrArg (fun v : ℍ => (translationLabel r)⁻¹ • v) h
  simpa only [inv_smul_smul] using he

/-- A row observed on Ω+r translates back to the common output Ω. -/
theorem compact_translate_shifted (b : Branch) (r : ℚ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticSubgroupSupport.translation (translationLabel r)).comp
      (compact b (shifted_compact r hs) hε t x)=compact (right b r) hs hε t x := by
  simpa only [preimage_shifted] using compact_translate b r (shifted_compact r hs) hε t x

theorem compact_eq_of_label (b c : Branch)
    (he : ofMatrix b.matrix b.positive=ofMatrix c.matrix c.positive)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compact b hs hε t x=compact c hs hε t x :=
  AsymptoticRegularCompactBranch.operator_projective_eq _ _ _ _
    (congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) he) hε t _ _ x

#print axioms right_label
#print axioms compact_translate
#print axioms shifted_compact
#print axioms preimage_shifted
#print axioms compact_translate_shifted
#print axioms compact_eq_of_label

end AsymptoticCompactFamilyTranslation
