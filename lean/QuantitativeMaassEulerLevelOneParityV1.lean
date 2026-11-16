module

public import QuantitativeMaassEulerLevelOneHilbertV1
public import QuantitativeMaassParityKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticClassicalPetersson AsymptoticCongruenceStrip

namespace QuantitativeMaass

/-- Literal geometric reflection of the original Fourier-Bessel function. -/
theorem principalEulerPhysical_reflection (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (z : ℍ) :
    principalEulerPhysical b r σ ((J•z:ℍ):ℂ)=(-1:ℂ)^σ*principalEulerPhysical b r σ z := by
  simp only [principalEulerPhysical,coe_J_smul,Complex.neg_re,Complex.neg_im,
    Complex.conj_re,Complex.conj_im,neg_neg,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  exact principalEulerWave_reflection b r σ z.re z.im

/-- Original parity becomes the actual quotient reflection eigenvalue. -/
theorem principalEulerLevelOneClass_reflection {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
    (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b) :
    reflectionIsometry 1 (principalEulerLevelOneClass r σ hb)=
      (-1:ℂ)^σ • principalEulerLevelOneClass r σ hb := by
  unfold principalEulerLevelOneClass
  rw [reflectionIsometry_apply,←map_smul]
  apply congrArg (AutomorphicL2.denseEmbedding (gamma 1) (quotientMeasure 1))
  apply Subtype.ext
  funext z
  exact principalEulerPhysical_reflection b r σ z

/-- The genuine parity projector fixes every original level-one solution. -/
theorem principalEulerLevelOneClass_parity {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
    (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b) :
    parityProjection 1 ((-1:ℝ)^σ) (principalEulerLevelOneClass r σ hb)=
      principalEulerLevelOneClass r σ hb := by
  rw [parityProjection_apply,principalEulerLevelOneClass_reflection,smul_smul]
  have hh : (((-1:ℝ)^σ:ℝ):ℂ)*(-1:ℂ)^σ=1 := by
    push_cast
    rw [←pow_two,pow_right_comm]
    norm_num
  rw [hh,one_smul]
  module

#print axioms principalEulerPhysical_reflection
#print axioms principalEulerLevelOneClass_reflection
#print axioms principalEulerLevelOneClass_parity

end QuantitativeMaass
