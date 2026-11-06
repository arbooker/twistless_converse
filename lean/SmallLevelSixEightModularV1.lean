module

public import SmallLevelSixGeneratorsV1
public import SmallLevelEightGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_six {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 6 k f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 6) :
    fourierFunction k f ∣[(k:ℤ)] γ=fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (fourierFunction k f)
  have ht : T∈K := original_T k f
  have hu : lower 6∈K := original_lower (by decide) hf
  have hz : -1∈K := by
    obtain ⟨m,hm⟩ := heven
    have hk : k=2*m := by omega
    change fourierFunction k f ∣[(k:ℤ)] (-1 : SL(2,ℤ))=fourierFunction k f
    rw [hk]
    exact SmallLevelThirtySix.slash_neg_one_even _ m
  exact gamma0_6_mem K ht hu hz
    (original_halfConjugate_of_lcm (by decide) (by decide : 0<3) (by decide) hf) γ hγ

theorem gamma_zero_eight {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 8 k f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 8) :
    fourierFunction k f ∣[(k:ℤ)] γ=fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (fourierFunction k f)
  have ht : T∈K := original_T k f
  have hu : lower 8∈K := original_lower (by decide) hf
  have hz : -1∈K := by
    obtain ⟨m,hm⟩ := heven
    have hk : k=2*m := by omega
    change fourierFunction k f ∣[(k:ℤ)] (-1 : SL(2,ℤ))=fourierFunction k f
    rw [hk]
    exact SmallLevelThirtySix.slash_neg_one_even _ m
  exact gamma0_8_mem K ht hu hz (original_halfConjugate (by decide : 0<2) hf) γ hγ

theorem level_six {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 6 k f) : IsModular 6 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf
    (gamma_zero_six (even_two_mul m) hf)

theorem level_eight {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 8 k f) : IsModular 8 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf
    (gamma_zero_eight (even_two_mul m) hf)

#print axioms gamma_zero_six
#print axioms gamma_zero_eight
#print axioms level_six
#print axioms level_eight

end SmallLevelOriginal
