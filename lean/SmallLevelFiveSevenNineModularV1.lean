module

public import SmallLevelOddGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_five_seven_nine {N : ℕ} (hN : N=5 ∨ N=7 ∨ N=9)
    (m : ℕ) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower N∈K := original_lower (by omega) hf
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  change γ∈K
  rcases hN with rfl | rfl | rfl
  · exact gamma0_5_mem K ht hu hz
      (original_odd (by decide) (by decide : 2*3=5+1) (by decide) hf) γ hγ
  · exact gamma0_7_mem K ht hu hz
      (original_odd (by decide) (by decide : 2*4=7+1) (by decide) hf) γ hγ
  · exact gamma0_9_mem K ht hu hz
      (original_odd (by decide) (by decide : 2*5=9+1) (by decide) hf) γ hγ

/-- The literal original solutions at levels 5, 7 and 9 give actual
Mathlib modular forms, with holomorphy at every cusp. -/
theorem levels_five_seven_nine {N k : ℕ} (hN : N=5 ∨ N=7 ∨ N=9)
    (heven : Even k) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N k f) :
    IsModular N k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by omega) hf (gamma_zero_five_seven_nine hN m hf)

theorem level_five {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 5 k f) : IsModular 5 k f :=
  levels_five_seven_nine (Or.inl rfl) heven hf

theorem level_seven {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 7 k f) : IsModular 7 k f :=
  levels_five_seven_nine (Or.inr (Or.inl rfl)) heven hf

theorem level_nine {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 9 k f) : IsModular 9 k f :=
  levels_five_seven_nine (Or.inr (Or.inr rfl)) heven hf

#print axioms gamma_zero_five_seven_nine
#print axioms levels_five_seven_nine
#print axioms level_five
#print axioms level_seven
#print axioms level_nine

end SmallLevelOriginal
