module

public import QuantitativeEulerEndpointLevelOneSignsV1
public import FinitenessOriginalFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLevelOne
open UpperHalfPlane ModularGroup Complex
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped ModularForm MatrixGroups

def solutionFunction (m : ℕ) (f : ℕ → ℂ) (z : ℍ) : ℂ := fourier (fullCoefficients f (2*m)) z

theorem solutionFunction_T (m : ℕ) (f : ℕ → ℂ) :
    solutionFunction m f ∣[((2*m : ℕ) : ℤ)] T=solutionFunction m f := by
  funext z
  rw [ModularForm.SL_slash_apply,modular_T_smul]
  have hd : denom T z=1 := by simp [ModularGroup.denom_apply,ModularGroup.T]
  rw [hd,one_zpow,mul_one]
  simpa only [solutionFunction,coe_vadd,Complex.ofReal_one,add_comm] using periodic (fullCoefficients f (2*m)) (z:ℂ)

/-- The literal original Euler-product solution at level one is invariant
under the full modular group. Its Fricke sign is eliminated by the exact
S,T relation rather than postulated as modularity. -/
theorem solutionFunction_modular (m : ℕ) (f : ℕ → ℂ) (hf : IsSolution 1 (2*m) f) :
    ∀ g : SL(2,ℤ), solutionFunction m f ∣[((2*m : ℕ) : ℤ)] g=solutionFunction m f := by
  obtain ⟨τ,_hτ,hg⟩ := hf.growth
  obtain ⟨ε,hε,hfr⟩ := FinitenessOriginalFricke.fricke_of_continuation
    (by norm_num : 0<(1:ℕ)) hf.zero hg hf.continuation
  let w := ε*Complex.I^(2*m)
  have heps : ε^2=1 := by rcases hε with he | he <;> simp [he]
  have hI : (Complex.I^(2*m))^2=1 := by
    have hfour : Complex.I^4=1 := by norm_num
    rw [←pow_mul,show 2*m*2=4*m by omega,pow_mul,hfour,one_pow]
  have hw : w^2=1 := by
    dsimp only [w]
    rw [mul_pow,heps,hI,one_mul]
  have hS : solutionFunction m f ∣[((2*m : ℕ) : ℤ)] ModularGroup.S=w • solutionFunction m f := by
    funext z
    have he := hfr (z:ℂ) z.im_pos
    simp only [Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,one_mul] at he
    have hh := congrArg (fun a : ℂ => w*a) he
    have heq : w*(w/(z:ℂ)^(2*m)*fourier (fullCoefficients f (2*m)) (-1/(z:ℂ)))=
        fourier (fullCoefficients f (2*m)) (-1/(z:ℂ))*((z:ℂ)^(2*m))⁻¹ := by
      rw [div_eq_mul_inv]
      calc
        _ = w^2*(fourier (fullCoefficients f (2*m)) (-1/(z:ℂ))*((z:ℂ)^(2*m))⁻¹) := by ring
        _ = _ := by rw [hw,one_mul]
    change w*fourier (fullCoefficients f (2*m)) (z:ℂ)=
      w*(w/(z:ℂ)^(2*m)*fourier (fullCoefficients f (2*m)) (-1/(z:ℂ))) at hh
    rw [heq] at hh
    simpa only [ModularForm.SL_slash_apply,denom_S,solutionFunction,modular_S_smul,
      UpperHalfPlane.coe_mk,inv_neg,neg_div,one_div,zpow_neg,zpow_natCast,
      Pi.smul_apply,smul_eq_mul] using hh.symm
  exact signed_S_periodic_modular (solutionFunction m f) _ w hw hS (solutionFunction_T m f)

#print axioms solutionFunction_modular
end QuantitativeEulerEndpointLevelOne
