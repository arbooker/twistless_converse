module

public import SmallLevelThirtyTwoCovarianceV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelEvenScale SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_thirty_two (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 32) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  have hc : (32:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 32).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hc' : γ 1 0=4*(8:ℤ)*c := by simpa using hc
  apply descend_invariance (2*m) f 8 γ c hc'
  have hh := SmallLevelThirtyTwo.eight_signed m (scaledFunction (2*m) f)
    (scaled_T (L:=8) hf.toEulerData) (scaled_lower (L:=8) (by decide) hf)
    (SmallLevelThirtyTwo.actual_C m hm hf)
    (rescaledMatrix 8 γ c hc') (rescaled_mem 8 γ c hc')
  simpa only [SmallLevelEightCharacter.rescaled_sign, Int.cast_one, one_smul] using hh

/-- Complete level-32 modularity from the literal original Euler input,
including every positive even weight and every cusp condition. -/
theorem level_thirty_two {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 k f) : IsModular 32 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_thirty_two m (by omega) hf)

#print axioms gamma_zero_thirty_two
#print axioms level_thirty_two

end SmallLevelOriginal
