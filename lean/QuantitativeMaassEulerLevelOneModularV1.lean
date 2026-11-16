module

public import QuantitativeMaassEulerComplexPhysicalV1
public import QuantitativeEulerEndpointLevelOneSignsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane ModularGroup
open scoped ModularForm MatrixGroups

namespace QuantitativeMaass

/-- Actual weight-zero translation law of the original Fourier wave. -/
theorem principalEulerPhysical_slash_T (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) :
    (fun z : ℍ => principalEulerPhysical b r σ z) ∣[(0:ℤ)] T=
      fun z : ℍ => principalEulerPhysical b r σ z := by
  funext z
  rw [ModularForm.SL_slash_apply,modular_T_smul,neg_zero,zpow_zero,mul_one]
  simpa only [coe_vadd,Complex.ofReal_one,add_comm] using principalEulerPhysical_periodic b r σ z

/-- At level one the exact S,T relation removes the possible Fricke sign.
This is full modular invariance of the actual original Maass reconstruction,
derived without a modularity hypothesis. -/
theorem principalEulerPhysical_level_one_modular {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
    (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b) :
    ∀ g : SL(2,ℤ),(fun z : ℍ => principalEulerPhysical b r σ z) ∣[(0:ℤ)] g=
      fun z : ℍ => principalEulerPhysical b r σ z := by
  obtain ⟨η,hη,hcont⟩ := hb.continuation
  let w : ℂ := (-1)^σ*η
  have hw : w^2=1 := by
    dsimp only [w]
    rw [mul_pow,pow_right_comm,show η^2=1 from sq_eq_one_iff.mpr hη]
    norm_num
  have hn : ‖η‖=1 := by rcases hη with rfl|rfl <;> simp
  have hfr := principalEulerWave_fricke hb.polynomialGrowth 1 (by norm_num) r σ hb.parity η hn
    (by simpa only [Nat.cast_one] using hcont)
  have hS : (fun z : ℍ => principalEulerPhysical b r σ z) ∣[(0:ℤ)] S=
      w • (fun z : ℍ => principalEulerPhysical b r σ z) := by
    funext z
    have he : principalEulerPhysical b r σ z=w*principalEulerPhysical b r σ (-1/(z:ℂ)) := by
      unfold principalEulerPhysical
      rw [show (-1/(z:ℂ))=(-1/(((1:ℝ):ℂ)*(z:ℂ))) by simp,
        fricke_complex_coordinates 1 (by norm_num) z z.im_pos]
      exact hfr z.re z.im z.im_pos
    have hh := congrArg (fun a : ℂ => w*a) he
    have heq : w*(w*principalEulerPhysical b r σ (-1/(z:ℂ)))=
        principalEulerPhysical b r σ (-1/(z:ℂ)) := by
      rw [←mul_assoc,←pow_two,hw,one_mul]
    rw [heq] at hh
    simpa only [ModularForm.SL_slash_apply,neg_zero,zpow_zero,mul_one,modular_S_smul,
      UpperHalfPlane.coe_mk,inv_neg,neg_div,one_div,Pi.smul_apply,smul_eq_mul] using hh.symm
  exact QuantitativeEulerEndpointLevelOne.signed_S_periodic_modular _ 0 w hw hS
    (principalEulerPhysical_slash_T b r σ)

#print axioms principalEulerPhysical_slash_T
#print axioms principalEulerPhysical_level_one_modular

end QuantitativeMaass
