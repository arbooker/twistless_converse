module
public import QuantitativeArithmeticSmallLevelThirtyThreeSourceWordsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords

def frickeCount : Word → ℕ
  | .one => 0
  | .generator i => if i=3 then 1 else 0
  | .mul w v => frickeCount w+frickeCount v
  | .inv w => frickeCount w

def threeCount : Word → ℕ
  | .one => 0
  | .generator i => if i=4 then 1 else 0
  | .mul w v => threeCount w+threeCount v
  | .inv w => threeCount w

theorem character_counts (η δ : ℂ) (w : Word) :
    character η δ w=η^(frickeCount w)*δ^(threeCount w) := by
  induction w with
  | one => simp [character,frickeCount,threeCount]
  | generator i => fin_cases i <;> simp [character,seedSign,frickeCount,threeCount]
  | mul w v hw hv => simp only [character,frickeCount,threeCount,hw,hv,pow_add]; ring
  | inv w hw => exact hw

theorem character_parities (η δ : ℂ) (hη : η=1 ∨ η= -1) (hδ : δ=1 ∨ δ= -1)
    (w : Word) : character η δ w=η^(frickeCount w%2)*δ^(threeCount w%2) := by
  rw [character_counts]
  have hη2 : η^2=1 := by rcases hη with rfl|rfl <;> norm_num
  have hδ2 : δ^2=1 := by rcases hδ with rfl|rfl <;> norm_num
  rw [pow_eq_pow_mod _ hη2,pow_eq_pow_mod _ hδ2]

#print axioms character_parities
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
