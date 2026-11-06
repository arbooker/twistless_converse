module

public import SmallLevelThirtySixCongruenceV1
public import SmallLevelOriginalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane Matrix
open scoped ModularForm MatrixGroups

/-- The integral conjugate of a Gamma0(36) matrix under z ↦ z/6. -/
def rescaledMatrix (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=36*c) : SL(2,ℤ) :=
  ⟨!![γ 0 0,6*γ 0 1;6*c,γ 1 1], by
    have hh := γ.property
    rw [det_fin_two] at hh ⊢
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at *
    rw [hc] at hh
    nlinarith⟩

theorem units_six : ∀ a d : ZMod 6, a*d=1 →
    (a=1 ∧ d=1) ∨ (a= -1 ∧ d= -1) := by decide

theorem rescaled_congruence (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=36*c) :
    reductionSix (rescaledMatrix γ c hc)=1 ∨
      reductionSix (rescaledMatrix γ c hc)= -1 := by
  have hd : (γ 0 0 : ZMod 6)*(γ 1 1 : ZMod 6)=1 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 6)) γ.property
    rw [det_fin_two, hc] at hh
    push_cast at hh
    simpa only [show (36:ZMod 6)=0 by decide, zero_mul, mul_zero, sub_zero] using hh
  rcases units_six _ _ hd with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reductionSix, rescaledMatrix, ha, hb, show (6:ZMod 6)=0 by decide]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reductionSix, rescaledMatrix, ha, hb, show (6:ZMod 6)=0 by decide]

def scaleSix (z : ℍ) : ℍ := ⟨6*(z:ℂ), by simpa using mul_pos (by norm_num : (0:ℝ)<6) z.im_pos⟩

theorem rescaled_denom (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=36*c) (z : ℍ) :
    denom (rescaledMatrix γ c hc) (scaleSix z)=denom γ z := by
  simp only [denom, SpecialLinearGroup.toGL]
  change ((6*c:ℤ):ℂ)*(6*(z:ℂ))+(γ 1 1:ℂ)=(γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ)
  rw [hc]
  push_cast
  ring

theorem rescaled_point (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=36*c) (z : ℍ) :
    (((rescaledMatrix γ c hc) • scaleSix z : ℍ) : ℂ)/6=((γ • z : ℍ):ℂ) := by
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  change (((γ 0 0:ℂ)*(6*(z:ℂ))+((6*γ 0 1:ℤ):ℂ))/
    (((6*c:ℤ):ℂ)*(6*(z:ℂ))+(γ 1 1:ℂ)))/6=
      ((γ 0 0:ℂ)*(z:ℂ)+(γ 0 1:ℂ))/((γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ))
  rw [hc]
  push_cast
  rw [show (6:ℂ)*c*(6*(z:ℂ))+(γ 1 1:ℂ)=36*c*(z:ℂ)+(γ 1 1:ℂ) by ring]
  ring

theorem scaled_slash (k : ℕ) (f : ℕ → ℂ) (γ : SL(2,ℤ)) (c : ℤ)
    (hc : γ 1 0=36*c) (z : ℍ) :
    (scaledFunction k f ∣[(k:ℤ)] rescaledMatrix γ c hc) (scaleSix z)=
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] γ) z := by
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, rescaled_denom]
  simp only [scaledFunction, scaledFourier, SmallLevelOriginal.fourierFunction, rescaled_point]

/-- The actual original Fourier function satisfies every Gamma0(36)
transformation, for both Fricke signs and every positive even weight.
This theorem does not yet assert the separate all-cusp condition. -/
theorem original_gamma_zero {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 36 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 36) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  have hc : (36:ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 36).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hh := original_congruence m hm hf (rescaledMatrix γ c hc) (rescaled_congruence γ c hc)
  funext z
  have he := congrFun hh (scaleSix z)
  rw [scaled_slash] at he
  simpa only [scaledFunction, scaledFourier, scaleSix, coe_mk,
    SmallLevelOriginal.fourierFunction, mul_div_cancel_left₀ _ (by norm_num : (6:ℂ)≠0)] using he

#print axioms rescaled_congruence
#print axioms rescaled_point
#print axioms scaled_slash
#print axioms original_gamma_zero

end SmallLevelThirtySix
