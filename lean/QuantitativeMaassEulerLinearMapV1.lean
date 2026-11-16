module

public import QuantitativeMaassPolynomialSpaceV1
public import QuantitativeMaassSmoothEigenSpaceV1
public import QuantitativeMaassEulerInjectiveV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

theorem principalEulerWave_add {b c : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (hc : MaassOriginal.PolynomialGrowth c)
    (r : ℝ) (σ : ℕ) (z : ℝ×ℝ) (hz : 0<z.2) :
    principalEulerWave (b+c) r σ z=principalEulerWave b r σ z+principalEulerWave c r σ z := by
  have ht : (fun n => principalEulerTerm (b+c) r σ n z)=
      fun n => principalEulerTerm b r σ n z+principalEulerTerm c r σ n z := by
    funext n
    simp only [principalEulerTerm,Pi.add_apply,add_mul]
  unfold principalEulerWave principalEulerCore
  rw [ht,(principalEulerTerm_summable hb r σ z hz).tsum_add (principalEulerTerm_summable hc r σ z hz)]
  ring

theorem principalEulerWave_smul (b : ℕ → ℂ) (c : ℂ) (r : ℝ) (σ : ℕ) (z : ℝ×ℝ) :
    principalEulerWave (c•b) r σ z=c*principalEulerWave b r σ z := by
  have ht : (fun n => principalEulerTerm (c•b) r σ n z)=
      fun n => c*principalEulerTerm b r σ n z := by
    funext n
    simp only [principalEulerTerm,Pi.smul_apply,smul_eq_mul]
    ring
  unfold principalEulerWave principalEulerCore
  rw [ht,tsum_mul_left]
  ring

/-- The literal Fourier-Bessel reconstruction, as an injective linear map
on all individually polynomially bounded cusp coefficient sequences. -/
def principalEulerSmoothMap (r : ℝ) (σ : ℕ) : polynomialCoefficientSpace →ₗ[ℂ] smoothUpperSpace where
  toFun a := principalEulerSmooth (polynomialCoefficientSpace_growth a) r σ
  map_add' a b := by
    apply Subtype.ext
    funext z
    by_cases hz : 0<z.2
    · exact principalEulerWave_add (polynomialCoefficientSpace_growth a) (polynomialCoefficientSpace_growth b) r σ z hz
    · simp [principalEulerSmooth,principalEulerWave,Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hz)]
  map_smul' c a := by
    apply Subtype.ext
    funext z
    exact principalEulerWave_smul a.val c r σ z

theorem principalEulerSmoothMap_injective (r : ℝ) (σ : ℕ) :
    Function.Injective (principalEulerSmoothMap r σ) := by
  intro a b hab
  apply Subtype.ext
  apply principalEulerWave_injective (polynomialCoefficientSpace_growth a) (polynomialCoefficientSpace_growth b)
    (a.property.1.trans b.property.1.symm) r σ
  intro x y _
  exact congrFun (congrArg Subtype.val hab) (x,y)

#print axioms principalEulerWave_add
#print axioms principalEulerWave_smul
#print axioms principalEulerSmoothMap
#print axioms principalEulerSmoothMap_injective

end QuantitativeMaass
