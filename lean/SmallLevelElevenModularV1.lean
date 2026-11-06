module

public import SmallLevelElevenRigidityV1
public import SmallLevelElevenGeneratorsV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_eleven (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 11 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 11) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 11∈K := original_lower (by decide) hf
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  change γ∈K
  exact SmallLevelEleven.gamma0_mem K ht hu hz
    (original_odd (by decide) (by decide : 2*6=11+1) (by decide) hf)
    (SmallLevelEleven.original_A m hm hf) γ hγ

/-- The literal original Euler input at level eleven gives an actual
Mathlib modular form, including boundedness at every cusp. -/
theorem level_eleven {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 11 k f) : IsModular 11 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_eleven m (by omega) hf)

#print axioms gamma_zero_eleven
#print axioms level_eleven

end SmallLevelOriginal
