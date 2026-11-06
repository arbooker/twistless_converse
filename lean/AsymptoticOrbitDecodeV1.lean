module

public import AsymptoticFreshCompactDefectsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticOrbitDecode

open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticIntegralSubgroup AsymptoticCompactTranslation AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap coefficient ratio)
open UpperHalfPlane
open scoped Classical

/-- Read the unique representative of a group coordinate in the
translation strip. This is a pointwise operation, not a bounded lift
from strip square-summable vectors to full-orbit square-summable vectors. -/
noncomputable def foldLabel (x : ℍ) (a : AsymptoticRationalGroup.Group) :
    AsymptoticRationalGroup.Group :=
  translationLabel (-(Int.floor (a • x).re:ℚ))*a

/-- Remove the positive cap weight after the strip fold. The result is
an ordinary function on group coordinates, with no summability claim. -/
noncomputable def decode (ε : ℝ) (t : ℕ) (x : ℍ) (f : Space)
    (a : AsymptoticRationalGroup.Group) : ℂ :=
  f (foldLabel x a)/(cap ε t (a • x):ℂ)

theorem foldLabel_integer (x : ℍ) (a : AsymptoticRationalGroup.Group) (n : ℤ) :
    foldLabel x (translationLabel (n:ℚ)*a)=foldLabel x a := by
  have hr : (translationLabel (n:ℚ) • (a • x)).re=(a • x).re+(n:ℝ) := by
    rw [label_action]
    have he := congrArg Complex.re (AsymptoticMobiusFold.translation_action (n:ℝ) (a • x))
    simpa using he
  unfold foldLabel
  rw [mul_smul,hr,Int.floor_add_intCast]
  rw [← mul_assoc,translationLabel_mul]
  congr 2
  push_cast
  ring

theorem decode_periodic (ε : ℝ) (t : ℕ) (x : ℍ) (f : Space)
    (a : AsymptoticRationalGroup.Group) (n : ℤ) :
    decode ε t x f (translationLabel (n:ℚ)*a)=decode ε t x f a := by
  simp only [decode,foldLabel_integer,mul_smul,cap_translate]

/-- The selected compact branch is exactly the decoded group action,
multiplied by the positive cap at the output and the compact cutoff. -/
theorem compact_decode (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) (a : AsymptoticRationalGroup.Group) :
    compact b hs hε t x f a=
      if a • x∈s then (cap ε t (a • x):ℂ)*
        decode ε t x f (ofMatrix b.matrix b.positive*a) else 0 := by
  classical
  have he : realMatrix b.matrix • (a • x)=(ofMatrix b.matrix b.positive*a) • x := by
    rw [mul_smul,ofMatrix_action]
  rw [compact,AsymptoticRegularCompactBranch.operator_selected,compactFold_label_eq]
  by_cases ha : a • x∈s
  · simp only [ite_eq_left ha,coefficient,Set.indicator_of_mem ha,ratio,he,
      decode,foldLabel,Complex.ofReal_div,mul_assoc]
    ring
  · simp only [ite_eq_right ha,coefficient,Set.indicator_of_notMem ha,zero_mul]

theorem cap_ne_zero {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : (cap ε t z:ℂ)≠0 :=
  Complex.ofReal_ne_zero.mpr (AsymptoticCompactBranch.cap_pos hε t z).ne'

#print axioms foldLabel_integer
#print axioms decode_periodic
#print axioms compact_decode
#print axioms cap_ne_zero

end AsymptoticOrbitDecode
