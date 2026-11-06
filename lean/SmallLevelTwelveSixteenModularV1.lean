module

public import SmallLevelEvenDescentV1
public import SmallLevelModularCriterionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open Matrix SmallLevelEvenScale SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_zero_twelve (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 12 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 12) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  have hc : (12:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hc' : γ 1 0=4*(3:ℤ)*c := by simpa using hc
  apply descend_invariance (2*m) f 3 γ c hc'
  have hh := three_signed m (scaledFunction (2*m) f)
    (scaled_T (L:=3) hf.toEulerData) (scaled_lower (L:=3) (by decide) hf)
    (rescaledMatrix 3 γ c hc') (rescaled_mem 3 γ c hc')
  simpa only [rescaled_sign_two, Int.cast_one, one_smul] using hh

theorem gamma_zero_sixteen (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 16 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 16) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  have hc : (16:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hc' : γ 1 0=4*(4:ℤ)*c := by simpa using hc
  apply descend_invariance (2*m) f 4 γ c hc'
  have hh := four_signed m (scaledFunction (2*m) f)
    (scaled_T (L:=4) hf.toEulerData) (scaled_lower (L:=4) (by decide) hf)
    (rescaledMatrix 4 γ c hc') (rescaled_mem 4 γ c hc')
  simpa only [rescaled_sign_eight, Int.cast_one, one_smul] using hh

/-- The level-12 case with literal original input and every cusp condition. -/
theorem level_twelve {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 12 k f) : IsModular 12 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_twelve m hf)

/-- The level-16 case; the scaled character is proved trivial on the
conjugated Gamma0(16), rather than assumed away. -/
theorem level_sixteen {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 16 k f) : IsModular 16 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_sixteen m hf)

#print axioms gamma_zero_twelve
#print axioms gamma_zero_sixteen
#print axioms level_twelve
#print axioms level_sixteen

end SmallLevelOriginal
