module

public import SmallLevelEvenScaleV1
public import SmallLevelSignedCovarianceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelEvenScale

open Matrix UpperHalfPlane SmallLevelGenerators
open scoped MatrixGroups ModularForm

/-- Integral conjugation under z ↦ z/2 at levels divisible by four. -/
def rescaledMatrix (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(L:ℤ)*c) : SL(2,ℤ) :=
  ⟨!![γ 0 0,2*γ 0 1;2*(L:ℤ)*c,γ 1 1], by
    have hh := γ.property
    rw [det_fin_two] at hh ⊢
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at *
    rw [hc] at hh
    nlinarith⟩

theorem rescaled_mem (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(L:ℤ)*c) :
    rescaledMatrix L γ c hc∈CongruenceSubgroup.Gamma0 L := by
  apply CongruenceSubgroup.Gamma0_mem.mpr
  simp [rescaledMatrix]

def scaleTwo (z : ℍ) : ℍ :=
  ⟨2*(z:ℂ), by simpa using mul_pos (by norm_num : (0:ℝ)<2) z.im_pos⟩

theorem rescaled_denom (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(L:ℤ)*c) (z : ℍ) :
    denom (rescaledMatrix L γ c hc) (scaleTwo z)=denom γ z := by
  simp only [denom, SpecialLinearGroup.toGL]
  change ((2*(L:ℤ)*c:ℤ):ℂ)*(2*(z:ℂ))+(γ 1 1:ℂ)=(γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ)
  rw [hc]
  push_cast
  ring

theorem rescaled_point (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(L:ℤ)*c) (z : ℍ) :
    (((rescaledMatrix L γ c hc) • scaleTwo z : ℍ):ℂ)/2=((γ • z : ℍ):ℂ) := by
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  change (((γ 0 0:ℂ)*(2*(z:ℂ))+((2*γ 0 1:ℤ):ℂ))/
    (((2*(L:ℤ)*c:ℤ):ℂ)*(2*(z:ℂ))+(γ 1 1:ℂ)))/2=
      ((γ 0 0:ℂ)*(z:ℂ)+(γ 0 1:ℂ))/((γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ))
  rw [hc]
  push_cast
  rw [show (2:ℂ)*L*c*(2*(z:ℂ))+(γ 1 1:ℂ)=4*L*c*(z:ℂ)+(γ 1 1:ℂ) by ring]
  ring

theorem scaled_slash (k : ℕ) (f : ℕ → ℂ) (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ)
    (hc : γ 1 0=4*(L:ℤ)*c) (z : ℍ) :
    (scaledFunction k f ∣[(k:ℤ)] rescaledMatrix L γ c hc) (scaleTwo z)=
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] γ) z := by
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, rescaled_denom]
  simp only [scaledFunction, scaledFourier, SmallLevelOriginal.fourierFunction, rescaled_point]

theorem descend_invariance (k : ℕ) (f : ℕ → ℂ) (L : ℕ) (γ : SL(2,ℤ)) (c : ℤ)
    (hc : γ 1 0=4*(L:ℤ)*c)
    (hs : scaledFunction k f ∣[(k:ℤ)] rescaledMatrix L γ c hc=scaledFunction k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] γ=SmallLevelOriginal.fourierFunction k f := by
  funext z
  have he := congrFun hs (scaleTwo z)
  rw [scaled_slash] at he
  simpa only [scaledFunction, scaledFourier, scaleTwo, coe_mk,
    SmallLevelOriginal.fourierFunction, mul_div_cancel_left₀ _ (by norm_num : (2:ℂ)≠0)] using he

theorem rescaled_sign_two (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(3:ℤ)*c) :
    signTwo (reduction 2 (rescaledMatrix 3 γ c hc))=1 := by
  apply signTwo_diagonal
  · change ((2*γ 0 1:ℤ):ZMod 2)=0
    push_cast
    rw [show (2:ZMod 2)=0 by decide, zero_mul]
  · change ((6*c:ℤ):ZMod 2)=0
    push_cast
    rw [show (6:ZMod 2)=0 by decide, zero_mul]

theorem rescaled_sign_eight (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(4:ℤ)*c) :
    signEight (reduction 8 (rescaledMatrix 4 γ c hc))=1 := by
  apply signEight_even_upper
  · change ((8*c:ℤ):ZMod 8)=0
    push_cast
    rw [show (8:ZMod 8)=0 by decide, zero_mul]
  · have hb : (reduction 8 (rescaledMatrix 4 γ c hc)).1 0 1=2*(γ 0 1:ZMod 8) := by
      simp [reduction, rescaledMatrix]
    rw [hb]
    exact eight_two_multiple _

#print axioms rescaled_mem
#print axioms rescaled_point
#print axioms descend_invariance
#print axioms rescaled_sign_two
#print axioms rescaled_sign_eight

end SmallLevelEvenScale
