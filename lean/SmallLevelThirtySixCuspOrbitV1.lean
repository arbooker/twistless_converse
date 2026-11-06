module

public import SmallLevelThirtySixCongruenceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

theorem positive_orbit (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S=g) (γ : SL(2,ℤ)) :
    g ∣[((2*m:ℕ):ℤ)] γ=positiveCombo m g (residueCoefficients (reductionSix γ)).1 := by
  let w := fun A : ResidueGroup => positiveCombo m g (residueCoefficients A).1
  have hs (A) : w A ∣[((2*m:ℕ):ℤ)] S=w (A*reductionSix S) := by
    dsimp only [w]; rw [positiveCombo_S m g hS, residue_S]
  have ht (A) : w A ∣[((2*m:ℕ):ℤ)] T=w (A*reductionSix T) := by
    dsimp only [w]; rw [positiveCombo_T m g hT hS, residue_T]
  simpa only [w, one_mul, residue_one, positiveCombo, Int.cast_one, Int.cast_zero,
    one_smul, zero_smul, add_zero] using finite_orbit_lift ((2*m:ℕ):ℤ) w hs ht γ 1

theorem negative_orbit (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S= -g) (hH : obstruction m g=0) (γ : SL(2,ℤ)) :
    g ∣[((2*m:ℕ):ℤ)] γ=negativeCombo m g (residueCoefficients (reductionSix γ)).2 := by
  let w := fun A : ResidueGroup => negativeCombo m g (residueCoefficients A).2
  have hs (A) : w A ∣[((2*m:ℕ):ℤ)] S=w (A*reductionSix S) := by
    dsimp only [w]; rw [negativeCombo_S m g hS hH, residue_S]
  have ht (A) : w A ∣[((2*m:ℕ):ℤ)] T=w (A*reductionSix T) := by
    dsimp only [w]; rw [negativeCombo_T m g hT, residue_T]
  simpa only [w, one_mul, residue_one, negativeCombo, Int.cast_one, Int.cast_zero,
    one_smul, zero_smul, add_zero] using finite_orbit_lift ((2*m:ℕ):ℤ) w hs ht γ 1

theorem positive_antiperiod (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S=g) (v : Coefficients) :
    positiveCombo m g v ∣[((2*m:ℕ):ℤ)] (T^3)= -positiveCombo m g v := by
  rw [show T^3=T*T*T by simp only [pow_succ, pow_zero, one_mul]]
  simp only [SlashAction.slash_mul, positiveCombo_T m g hT hS]
  ext z
  simp only [positiveCombo, positiveStepT, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, Int.cast_add, Int.cast_neg]
  ring

theorem negative_antiperiod (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (v : Coefficients) :
    negativeCombo m g v ∣[((2*m:ℕ):ℤ)] (T^3)= -negativeCombo m g v := by
  rw [show T^3=T*T*T by simp only [pow_succ, pow_zero, one_mul]]
  simp only [SlashAction.slash_mul, negativeCombo_T m g hT]
  ext z
  simp only [negativeCombo, negativeStepT, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, Int.cast_add, Int.cast_neg]
  ring

/-- Every rational-cusp transform is negated by translation through three.
Combined with polynomial growth, this will exclude its cusp constant term. -/
theorem original_cusp_antiperiod {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 36 (2*m) f) (γ : SL(2,ℤ)) :
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ) ∣[((2*m:ℕ):ℤ)] (T^3)=
      -(scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ) := by
  have hT := scaledFunction_quadratic hf.toEulerData (2*m)
  obtain ⟨chi,hchi,hS⟩ := scaledFunction_sign m hf
  rcases hchi with rfl | rfl
  · simp only [one_smul] at hS
    rw [positive_orbit m _ hT hS γ, positive_antiperiod m _ hT hS]
  · simp only [neg_one_smul] at hS
    have hH := original_obstruction_zero m hm hf hS
    rw [negative_orbit m _ hT hS hH γ, negative_antiperiod m _ hT]

theorem original_cusp_period {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 36 (2*m) f) (γ : SL(2,ℤ)) :
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ) ∣[((2*m:ℕ):ℤ)] (T^6)=
      scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ := by
  rw [show T^6=T^3*T^3 by group, SlashAction.slash_mul,
    original_cusp_antiperiod m hm hf γ, SlashAction.neg_slash,
    original_cusp_antiperiod m hm hf γ, neg_neg]

#print axioms positive_orbit
#print axioms negative_orbit
#print axioms original_cusp_antiperiod
#print axioms original_cusp_period

end SmallLevelThirtySix
