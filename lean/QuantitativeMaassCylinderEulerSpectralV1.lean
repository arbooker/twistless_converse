module

public import QuantitativeMaassCylinderKernelActionV1
public import QuantitativeMaassClassicalAbelMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual bounded capped cylinder operator has the exact spectral
multiplier on every original Euler solution. The proof uses the classical
PDE, the local Abel initial conditions and the literal kernel action. -/
theorem cylinderCappedAbelOperator_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs) P.ε P.epsilon_pos (P.s+3)
      (principalEulerCylinderLp hN A P r σ hb)=
      cosinePacket (coshTimeTest F) r • principalEulerCylinderLp hN A P r σ hb := by
  apply Lp.ext
  filter_upwards [cylinderCappedRadialOperator_original hN A P r σ hb
    (abelProfile F) (abelProfile_smooth F hF hc) R hR (abelProfile_support F _ hs),
    principalEulerCylinderLp_coeFn hN A P r σ hb,
    Lp.coeFn_smul (cosinePacket (coshTimeTest F) r) (principalEulerCylinderLp hN A P r σ hb)]
    with x hx hf hsx
  rw [hx,hsx]
  simp only [Pi.smul_apply]
  rw [hf,weighted_zero_eq_capped,
    principalEuler_abel_multiplier hb.polynomialGrowth r σ F hF hc hr R hR hs x]
  change (cappedHeightWeight P.ε (P.s+3) x:ℂ)*(cosinePacket (coshTimeTest F) r*
    principalEulerPhysical b r σ x)=cosinePacket (coshTimeTest F) r*
    ((cappedHeightWeight P.ε (P.s+3) x:ℂ)*principalEulerPhysical b r σ x)
  ring

#print axioms cylinderCappedAbelOperator_original

end QuantitativeMaass
