module

public import SmallLevelTwentyFourCovarianceV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelEvenScale SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_twenty_four (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 24) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  have hc : (24:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hc' : γ 1 0=4*(6:ℤ)*c := by simpa using hc
  apply descend_invariance (2*m) f 6 γ c hc'
  have hh := SmallLevelTwentyFour.six_signed m (scaledFunction (2*m) f)
    (scaled_T (L:=6) hf.toEulerData) (scaled_lower (L:=6) (by decide) hf)
    (SmallLevelTwentyFour.actual_C m hm hf)
    (rescaledMatrix 6 γ c hc') (rescaled_mem 6 γ c hc')
  simpa only [SmallLevelSixCharacter.rescaled_sign, Int.cast_one, one_smul] using hh

/-- Level24 modularity from original input at every positive even weight,
including all cusp conditions. -/
theorem level_twenty_four {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 k f) : IsModular 24 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_twenty_four m (by omega) hf)

#print axioms gamma_zero_twenty_four
#print axioms level_twenty_four

end SmallLevelOriginal
