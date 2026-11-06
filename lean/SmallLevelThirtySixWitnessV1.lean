module

public import SmallLevelThirtySixWordsV1

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

def witness : SL(2,ℤ) := ⟨!![11,30;-150,-409], by norm_num [det_fin_two]⟩
def witnessFinite (j : ℤ) : SL(2,ℤ) :=
  ⟨!![11-900*j, 6-504*j+1080*j^2; -750, -409+900*j], by simp [det_fin_two]; ring⟩
def witnessInfinity : SL(2,ℤ) := ⟨!![11,150;-30,-409], by norm_num [det_fin_two]⟩

/-- Kernel-checked integer matrix words, not imported external certificates. -/
theorem witness_word : wordMatrix [0,14,3,4] 3=(-1)*witness := by decide
theorem finite_zero_word : wordMatrix [0,68,-6,-2] 0=(-1)*witnessFinite 0 := by decide
theorem finite_one_word : wordMatrix [1,-5,3,2,-9,-3] (-1)=witnessFinite 1 := by decide
theorem finite_two_word : wordMatrix [2,-3,-2,2,-8,-7] (-2)=(-1)*witnessFinite 2 := by decide
theorem finite_three_word : wordMatrix [4,2,-2,2,-3,18] (-3)=(-1)*witnessFinite 3 := by decide
theorem finite_four_word : wordMatrix [5,5,3,14,4] (-4)=(-1)*witnessFinite 4 := by decide
theorem infinity_word : wordMatrix [0,3,4,3] 14=(-1)*witnessInfinity := by decide

theorem witness_coefficients : wordCoefficients [0,14,3,4] 3 (1,0,0)=(1,0,-2) := by decide
theorem finite_zero_coefficients : wordCoefficients [0,68,-6,-2] 0 (1,0,0)=(1,0,0) := by decide
theorem finite_one_coefficients : wordCoefficients [1,-5,3,2,-9,-3] (-1) (1,0,0)=(1,0,-4) := by decide
theorem finite_two_coefficients : wordCoefficients [2,-3,-2,2,-8,-7] (-2) (1,0,0)=(1,0,2) := by decide
theorem finite_three_coefficients : wordCoefficients [4,2,-2,2,-3,18] (-3) (1,0,0)=(1,0,-2) := by decide
theorem finite_four_coefficients : wordCoefficients [5,5,3,14,4] (-4) (1,0,0)=(1,0,2) := by decide
theorem infinity_coefficients : wordCoefficients [0,3,4,3] 14 (1,0,0)=(1,0,2) := by decide

variable (m : ℕ) (g : ℍ → ℂ)
  (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
  (hS : g ∣[((2*m:ℕ):ℤ)] S = -g)

include hT hS

theorem defect_of_word (qs : List ℤ) (t c : ℤ) (γ : SL(2,ℤ))
    (hm : wordMatrix qs t=γ ∨ wordMatrix qs t=(-1)*γ)
    (hc : wordCoefficients qs t (1,0,0)=(1,0,c)) :
    g ∣[((2*m:ℕ):ℤ)] γ=g+(c:ℂ) • obstruction m g := by
  have hh := original_word m g hT hS qs t
  rw [hc] at hh
  rcases hm with hm | hm
  · simpa only [hm, combo, Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero] using hh
  · simpa only [hm, SlashAction.slash_mul, slash_neg_one_even,
      combo, Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero] using hh

theorem witness_action :
    g ∣[((2*m:ℕ):ℤ)] witness=g+(-2:ℂ) • obstruction m g := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    defect_of_word m g hT hS _ _ _ _ (.inr witness_word) witness_coefficients

theorem finite_zero_action : g ∣[((2*m:ℕ):ℤ)] witnessFinite 0=g := by
  simpa only [Int.cast_zero, zero_smul, add_zero] using
    defect_of_word m g hT hS _ _ _ _ (.inr finite_zero_word) finite_zero_coefficients

theorem finite_one_action : g ∣[((2*m:ℕ):ℤ)] witnessFinite 1=g+(-4:ℂ) • obstruction m g := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    defect_of_word m g hT hS _ _ _ _ (.inl finite_one_word) finite_one_coefficients

theorem finite_two_action : g ∣[((2*m:ℕ):ℤ)] witnessFinite 2=g+(2:ℂ) • obstruction m g :=
  defect_of_word m g hT hS _ _ _ _ (.inr finite_two_word) finite_two_coefficients

theorem finite_three_action : g ∣[((2*m:ℕ):ℤ)] witnessFinite 3=g+(-2:ℂ) • obstruction m g := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    defect_of_word m g hT hS _ _ _ _ (.inr finite_three_word) finite_three_coefficients

theorem finite_four_action : g ∣[((2*m:ℕ):ℤ)] witnessFinite 4=g+(2:ℂ) • obstruction m g :=
  defect_of_word m g hT hS _ _ _ _ (.inr finite_four_word) finite_four_coefficients

theorem infinity_action : g ∣[((2*m:ℕ):ℤ)] witnessInfinity=g+(2:ℂ) • obstruction m g :=
  defect_of_word m g hT hS _ _ _ _ (.inr infinity_word) infinity_coefficients

#print axioms witness_word
#print axioms witness_coefficients
#print axioms witness_action
#print axioms finite_zero_action
#print axioms finite_one_action
#print axioms finite_two_action
#print axioms finite_three_action
#print axioms finite_four_action
#print axioms infinity_action

end SmallLevelThirtySix
