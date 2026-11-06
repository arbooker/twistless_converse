module

public import SmallLevelThirtySixFourierV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open Complex UpperHalfPlane ModularGroup FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction
open scoped ModularForm MatrixGroups

def scaledFunction (k : ℕ) (f : ℕ → ℂ) (z : ℍ) : ℂ := scaledFourier k f z

theorem scaledFunction_T (k : ℕ) (f : ℕ → ℂ) (z : ℍ) :
    (scaledFunction k f ∣[(k : ℤ)] T) z=scaledFourier k f ((z : ℂ)+1) := by
  rw [ModularForm.SL_slash_apply, modular_T_smul]
  have hd : denom T z=1 := by simp [ModularGroup.denom_apply, ModularGroup.T]
  rw [hd, one_zpow, mul_one]
  simp only [scaledFunction, coe_vadd, Complex.ofReal_one, add_comm]

theorem scaledFunction_quadratic {f : ℕ → ℂ} (hf : EulerData 36 f) (k : ℕ) :
    (scaledFunction k f ∣[(k : ℤ)] T) ∣[(k : ℤ)] T=
      (scaledFunction k f ∣[(k : ℤ)] T)-scaledFunction k f := by
  funext z
  rw [ModularForm.SL_slash_apply, modular_T_smul]
  have hd : denom T z=1 := by simp [ModularGroup.denom_apply, ModularGroup.T]
  rw [hd, one_zpow, mul_one, scaledFunction_T]
  simp only [Pi.sub_apply, scaledFunction_T, scaledFunction, coe_vadd, Complex.ofReal_one]
  have hh := scaled_translation_quadratic hf k z.im_pos
  rw [show (1:ℂ)+(z:ℂ)+1=(z:ℂ)+2 by ring]
  linear_combination hh

/-- The original untwisted functional equation gives one coherent sign
for the scaled S-action. Neither sign is discarded. -/
theorem scaledFunction_sign {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 36 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ = -1) ∧
      scaledFunction (2*m) f ∣[((2*m : ℕ) : ℤ)] ModularGroup.S=χ • scaledFunction (2*m) f := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  obtain ⟨ε, hε, hfr⟩ := FinitenessOriginalFricke.fricke_of_continuation
    (by decide : 0 < (36:ℕ)) hf.zero hg hf.continuation
  let χ : ℂ := ε*Complex.I^(2*m)
  have hχ : χ^2=1 := by
    have he : ε^2=1 := by rcases hε with he | he <;> simp [he]
    have hi : (Complex.I^(2*m))^2=1 := by
      rw [← pow_mul, show 2*m*2=4*m by omega, pow_mul]
      norm_num
    dsimp only [χ]
    rw [mul_pow, he, hi, one_mul]
  refine ⟨χ, (sq_eq_one_iff.mp hχ), ?_⟩
  funext z
  have he := hfr ((z:ℂ)/6) (by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<6))
  have hsqrt : Real.sqrt (36:ℝ)=6 := by norm_num
  norm_num only [Nat.cast_ofNat, hsqrt, Complex.ofReal_ofNat] at he
  rw [show (6:ℂ)*((z:ℂ)/6)=(z:ℂ) by ring,
    show -1/((36:ℂ)*((z:ℂ)/6))=(-1/(z:ℂ))/6 by ring] at he
  have hh := congrArg (fun v : ℂ => χ*v) he
  change χ*scaledFourier (2*m) f (z:ℂ)=
    χ*(χ/(z:ℂ)^(2*m)*scaledFourier (2*m) f (-1/(z:ℂ))) at hh
  have halg : χ*(χ/(z:ℂ)^(2*m)*scaledFourier (2*m) f (-1/(z:ℂ)))=
      scaledFourier (2*m) f (-1/(z:ℂ))*((z:ℂ)^(2*m))⁻¹ := by
    rw [div_eq_mul_inv]
    calc
      _ = χ^2*(scaledFourier (2*m) f (-1/(z:ℂ))*((z:ℂ)^(2*m))⁻¹) := by ring
      _ = _ := by rw [hχ, one_mul]
  rw [halg] at hh
  simpa only [ModularForm.SL_slash_apply, denom_S, scaledFunction, modular_S_smul,
    UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div, zpow_neg, zpow_natCast,
    Pi.smul_apply, smul_eq_mul] using hh.symm

#print axioms scaledFunction_T
#print axioms scaledFunction_quadratic
#print axioms scaledFunction_sign

end SmallLevelThirtySix
