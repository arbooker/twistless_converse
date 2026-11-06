module

public import SmallLevelThirtyKernelV1
public import SmallLevelThirtyGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_thirty (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 30) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have hK (i : Fin 26) : SmallLevelThirty.generator i∈K := SmallLevelThirty.original_kernel m hm hf i
  change γ∈K
  exact SmallLevelThirty.gamma0_mem K hK
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Level30 original Euler solutions are genuine modular forms at every
positive even weight, with no additional eigenvalue or cusp premise. -/
theorem level_thirty {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 k f) : IsModular 30 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_thirty m (by omega) hf)

#print axioms gamma_zero_thirty
#print axioms level_thirty

end SmallLevelOriginal
