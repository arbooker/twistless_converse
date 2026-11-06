module
public import QuantitativeArithmeticSmallLevelThirtyFiveFullTaylorLaurentV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

/-- In this sign representative every Ramanujan root factor is one,
including composite moduli and higher prime powers. -/
theorem all_roots_one_of_negative_bad_signs {f : ℕ → ℂ}
    (h5 : badFive f= -1) (h7 : badSeven f= -1) (q : ℕ) : root 35 f q=1 := by
  unfold root
  apply Finset.prod_eq_one
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  unfold FinitenessNormalizedTwistLocal.sign
  split_ifs with hzero hbad
  · rfl
  · have hmem : p ∈ (35:ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime,hbad.1,by decide⟩
    have h35 : (35:ℕ).primeFactors={5,7} := by
      rw [show (35:ℕ)=5*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
      rw [(by decide : Nat.Prime 5).primeFactors,(by decide : Nat.Prime 7).primeFactors]
      decide
    rw [h35] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl|rfl
    · change (Real.sqrt 5:ℂ)*f 5= -1 at h5
      linear_combination -h5
    · change (Real.sqrt 7:ℂ)*f 7= -1 at h7
      linear_combination -h7
  · rfl

#print axioms all_roots_one_of_negative_bad_signs
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
