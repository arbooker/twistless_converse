module

public import SmallLevelTenGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_ten (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 10 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 10) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  change γ∈K
  exact SmallLevelTen.gamma0_mem K (SmallLevelTen.original_kernel m hf)
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Complete original-input level-ten modularity, including every even
weight and the required cusp conditions. -/
theorem level_ten {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 10 k f) : IsModular 10 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_ten m hf)

#print axioms gamma_zero_ten
#print axioms level_ten

end SmallLevelOriginal
