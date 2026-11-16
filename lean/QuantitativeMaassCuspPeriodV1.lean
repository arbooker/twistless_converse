module

public import QuantitativeMaassHeckeActionV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeMaass

/-- The conjugate of translation by N in an arbitrary integral cusp chart. -/
def cuspTranslation (N : ℕ) (s : SL(2,ℤ)) : SL(2,ℤ) := s * upperSL (N : ℤ) * s⁻¹

theorem cuspTranslation_bottom_left (N : ℕ) (s : SL(2,ℤ)) :
    (cuspTranslation N s).val 1 0 = -(N : ℤ) * (s.val 1 0)^2 := by
  change (∑ k : Fin 2, (s.val * (upperSL (N : ℤ)).val) 1 k * (s⁻¹).val k 0) = _
  rw [SpecialLinearGroup.SL2_inv_expl]
  simp only [Fin.sum_univ_two]
  change (∑ k : Fin 2, s.val 1 k * (upperSL (N : ℤ)).val k 0) * s.val 1 1 +
    (∑ k : Fin 2, s.val 1 k * (upperSL (N : ℤ)).val k 1) * (-s.val 1 0) = _
  simp only [Fin.sum_univ_two]
  change (s.val 1 0 * 1 + s.val 1 1 * 0) * s.val 1 1 +
    (s.val 1 0 * (N : ℤ) + s.val 1 1 * 1) * (-s.val 1 0) = _
  ring

theorem cuspTranslation_mem (N : ℕ) (s : SL(2,ℤ)) :
    cuspTranslation N s ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, cuspTranslation_bottom_left]
  simp

/-- Every integral cusp chart has horocycle period N for a level-N function.
Using this common period avoids any unproved classification of cusp labels
or widths; every rational cusp admits such an integral chart. -/
theorem cusp_chart_translation (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z) = f z) (z : ℍ) :
    f (integralLabel s • (integralLabel (upperSL (N : ℤ)) • z)) = f (integralLabel s • z) := by
  have hi := hinv ⟨integralLabel (cuspTranslation N s),
    ⟨cuspTranslation N s,cuspTranslation_mem N s,rfl⟩⟩ (integralLabel s • z)
  simpa only [cuspTranslation,map_mul,map_inv,mul_smul,inv_smul_smul] using hi

/-- Cartesian horocycle coordinates, with positivity recorded in the point. -/
def horocyclePoint (x y : ℝ) (hy : 0 < y) : ℍ := ⟨⟨x,y⟩,hy⟩

theorem horocyclePoint_translate (n : ℤ) (x y : ℝ) (hy : 0 < y) :
    integralLabel (upperSL n) • horocyclePoint x y hy = horocyclePoint (x+n) y hy := by
  rw [upper_label]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · exact translation_re n (horocyclePoint x y hy)
  · exact AsymptoticCompactTranslation.label_im (n : ℚ) (horocyclePoint x y hy)

/-- The actual function at every integral cusp is periodic, not merely the
one at infinity. This is the domain for all-cusp constant-term extraction. -/
theorem cusp_chart_periodic (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z) = f z) (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x => f (integralLabel s • horocyclePoint x y hy)) (N : ℝ) := by
  intro x
  have hi := cusp_chart_translation N s f hinv (horocyclePoint x y hy)
  rw [horocyclePoint_translate] at hi
  simpa only [Int.cast_natCast] using hi

#print axioms cuspTranslation_mem
#print axioms cusp_chart_periodic

end QuantitativeMaass
