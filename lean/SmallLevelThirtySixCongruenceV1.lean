module

public import SmallLevelThirtySixResiduesV1
public import SmallLevelThirtySixObstructionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

/-- Generator covariance lifts through the full modular group. The inverse
step uses the group action, so no independence of orbit functions is needed. -/
theorem finite_orbit_lift (k : ℤ) (w : ResidueGroup → ℍ → ℂ)
    (hS : ∀ A, w A ∣[k] S=w (A*reductionSix S))
    (hT : ∀ A, w A ∣[k] T=w (A*reductionSix T))
    (γ : SL(2,ℤ)) : ∀ A, w A ∣[k] γ=w (A*reductionSix γ) := by
  have hmem : γ ∈ Subgroup.closure {S,T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem γ hγ =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  | one => intro A; simp
  | mul γ δ _ _ ihγ ihδ =>
    intro A
    rw [SlashAction.slash_mul, ihγ, ihδ, map_mul, mul_assoc]
  | inv γ _ ih =>
    intro A
    have hh := congrArg (fun f : ℍ → ℂ => f ∣[k] γ⁻¹) (ih (A*(reductionSix γ)⁻¹))
    simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      mul_assoc, inv_mul_cancel, mul_one] at hh
    simpa only [map_inv] using hh.symm

def positiveCombo (m : ℕ) (g : ℍ → ℂ) (v : Coefficients) : ℍ → ℂ :=
  (v.1:ℂ) • g+(v.2.1:ℂ) • (g ∣[((2*m:ℕ):ℤ)] T)+
    (v.2.2:ℂ) • ((g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] S)

def negativeCombo (m : ℕ) (g : ℍ → ℂ) (v : Coefficients) : ℍ → ℂ :=
  (v.1:ℂ) • g+(v.2.1:ℂ) • (g ∣[((2*m:ℕ):ℤ)] T)

theorem positiveCombo_S (m : ℕ) (g : ℍ → ℂ)
    (hS : g ∣[((2*m:ℕ):ℤ)] S=g) (v : Coefficients) :
    positiveCombo m g v ∣[((2*m:ℕ):ℤ)] S=positiveCombo m g (positiveStepS v) := by
  simp only [positiveCombo, SlashAction.add_slash, ModularForm.SL_smul_slash,
    hS, slash_S_twice_even, positiveStepS]
  abel

theorem positiveCombo_T (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S=g) (v : Coefficients) :
    positiveCombo m g v ∣[((2*m:ℕ):ℤ)] T=positiveCombo m g (positiveStepT v) := by
  have hi : g ∣[((2*m:ℕ):ℤ)] T⁻¹=g-(g ∣[((2*m:ℕ):ℤ)] T) := by
    have hh := congrArg (fun f : ℍ → ℂ => f ∣[((2*m:ℕ):ℤ)] T⁻¹) hT
    simp only [sub_slash, ← SlashAction.slash_mul, mul_assoc,
      mul_inv_cancel, mul_one, SlashAction.slash_one] at hh
    linear_combination hh
  have hh : ((g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] S) ∣[((2*m:ℕ):ℤ)] T=
      g-((g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] S) := by
    rw [slash_TST_even, hS, hi, sub_slash, hS]
  simp only [positiveCombo, SlashAction.add_slash, ModularForm.SL_smul_slash,
    hT, hh, positiveStepT]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_add, Int.cast_neg]
  ring

theorem negativeCombo_S (m : ℕ) (g : ℍ → ℂ)
    (hS : g ∣[((2*m:ℕ):ℤ)] S= -g) (hH : obstruction m g=0) (v : Coefficients) :
    negativeCombo m g v ∣[((2*m:ℕ):ℤ)] S=negativeCombo m g (negativeStepS v) := by
  have hh : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] S= -(g ∣[((2*m:ℕ):ℤ)] T) := by
    dsimp only [obstruction] at hH
    linear_combination hH
  simp only [negativeCombo, SlashAction.add_slash, ModularForm.SL_smul_slash,
    hS, hh, negativeStepS, Int.cast_neg, _root_.neg_smul, smul_neg]

theorem negativeCombo_T (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (v : Coefficients) :
    negativeCombo m g v ∣[((2*m:ℕ):ℤ)] T=negativeCombo m g (negativeStepT v) := by
  simp only [negativeCombo, SlashAction.add_slash, ModularForm.SL_smul_slash,
    hT, negativeStepT]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_add, Int.cast_neg]
  ring

theorem positive_congruence (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S=g) (γ : SL(2,ℤ))
    (hγ : reductionSix γ=1 ∨ reductionSix γ= -1) : g ∣[((2*m:ℕ):ℤ)] γ=g := by
  let w := fun A : ResidueGroup => positiveCombo m g (residueCoefficients A).1
  have hs (A) : w A ∣[((2*m:ℕ):ℤ)] S=w (A*reductionSix S) := by
    dsimp only [w]; rw [positiveCombo_S m g hS, residue_S]
  have ht (A) : w A ∣[((2*m:ℕ):ℤ)] T=w (A*reductionSix T) := by
    dsimp only [w]; rw [positiveCombo_T m g hT hS, residue_T]
  have hh := finite_orbit_lift ((2*m:ℕ):ℤ) w hs ht γ 1
  rcases hγ with hγ | hγ <;>
    simpa only [w, one_mul, hγ, residue_one, residue_neg_one, positiveCombo,
      Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero] using hh

theorem negative_congruence (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
    (hS : g ∣[((2*m:ℕ):ℤ)] S= -g) (hH : obstruction m g=0) (γ : SL(2,ℤ))
    (hγ : reductionSix γ=1 ∨ reductionSix γ= -1) : g ∣[((2*m:ℕ):ℤ)] γ=g := by
  let w := fun A : ResidueGroup => negativeCombo m g (residueCoefficients A).2
  have hs (A) : w A ∣[((2*m:ℕ):ℤ)] S=w (A*reductionSix S) := by
    dsimp only [w]; rw [negativeCombo_S m g hS hH, residue_S]
  have ht (A) : w A ∣[((2*m:ℕ):ℤ)] T=w (A*reductionSix T) := by
    dsimp only [w]; rw [negativeCombo_T m g hT, residue_T]
  have hh := finite_orbit_lift ((2*m:ℕ):ℤ) w hs ht γ 1
  rcases hγ with hγ | hγ <;>
    simpa only [w, one_mul, hγ, residue_one, residue_neg_one, negativeCombo,
      Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero] using hh

/-- Both original Fricke signs give invariance under matrices congruent to
plus or minus the identity modulo six. -/
theorem original_congruence {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 36 (2*m) f) (γ : SL(2,ℤ))
    (hγ : reductionSix γ=1 ∨ reductionSix γ= -1) :
    scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=scaledFunction (2*m) f := by
  have hT := scaledFunction_quadratic hf.toEulerData (2*m)
  obtain ⟨chi,hchi,hS⟩ := scaledFunction_sign m hf
  rcases hchi with rfl | rfl
  · simp only [one_smul] at hS
    exact positive_congruence m _ hT hS γ hγ
  · simp only [neg_one_smul] at hS
    exact negative_congruence m _ hT hS (original_obstruction_zero m hm hf hS) γ hγ

#print axioms finite_orbit_lift
#print axioms positive_congruence
#print axioms negative_congruence
#print axioms original_congruence

end SmallLevelThirtySix
