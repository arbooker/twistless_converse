module

public import QuantitativeMaassCylinderTimePacketV1
public import QuantitativeMaassTimePacketScalarLimitV1
public import QuantitativeMaassPhysicalEulerSpectralV1
public import QuantitativeMaassCylinderCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual capped wave packet has its exact scalar action on every
original polynomial-growth Euler solution, with no global unweighted L2 premise. -/
theorem cylinderCappedTimePacket_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    cylinderCappedTimePacket f hf he hc hr R hR hs P.ε P.epsilon_pos (P.s+3)
      (principalEulerCylinderLp hN A P r σ hb)=
      cosinePacket f r • principalEulerCylinderLp hN A P r σ hb := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F (n : ℕ) := radialShiftApprox (evenCoshLift f) (a n)
  have hF (n : ℕ) := radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha n)
  have hFc (n : ℕ) := radialShiftApprox_compact _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  have hFr (n : ℕ) := radialShiftApprox_real _ (evenCoshLift_real f hr) (a n)
  have hFs (n : ℕ) := radialShiftApprox_upper_support _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  let B (n : ℕ) := cylinderCappedRadialOperator (abelProfile (F n))
    (abelProfile_smooth _ (hF n) (hFc n)) R hR (abelProfile_support _ _ (hFs n))
    P.ε P.epsilon_pos (P.s+3)
  let g := principalEulerCylinderLp hN A P r σ hb
  have hB : Tendsto B atTop
      (𝓝 (cylinderCappedTimePacket f hf he hc hr R hR hs P.ε P.epsilon_pos (P.s+3))) :=
    cylinderCappedTimePacket_shift_tendsto atTop f hf he hc hr R hR hs a ha ha0 P.ε P.epsilon_pos (P.s+3)
  have hleft := ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (quotientMeasure 0)) g).continuous.tendsto _).comp hB
  have hright := (radialShiftTime_cosinePacket_tendsto atTop f hf he hc R hR hs a ha ha0 r).smul
    (tendsto_const_nhds (x:=g))
  have heq (n : ℕ) : B n g=cosinePacket (radialShiftTime f (a n)) r • g :=
    cylinderCappedAbelOperator_original hN A P r σ hb (F n) (hF n) (hFc n) (hFr n) R hR (hFs n)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall (fun n => (heq n).symm))

/-- Zero extension of the genuine smooth time packet into the physical
Hilbert space used by residual reconstruction. -/
def physicalCappedTimePacket (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :=
  cylinderZeroExtension.toContinuousLinearMap.comp
    ((cylinderCappedTimePacket f hf he hc hr R hR hs ε hε t).comp
      cylinderZeroExtension.toContinuousLinearMap.adjoint)

theorem physicalCappedTimePacket_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    physicalCappedTimePacket f hf he hc hr R hR hs P.ε P.epsilon_pos (P.s+3)
      (principalEulerWeightedLp hN A P r σ hb)=
      cosinePacket f r • principalEulerWeightedLp hN A P r σ hb := by
  rw [←principalEulerCylinderLp_physical hN A P r σ hb]
  change cylinderZeroExtension (cylinderCappedTimePacket f hf he hc hr R hR hs P.ε P.epsilon_pos (P.s+3)
    (cylinderZeroExtension.toContinuousLinearMap.adjoint
      (cylinderZeroExtension (principalEulerCylinderLp hN A P r σ hb))))=_
  rw [cylinderZeroExtension_adjoint_self,
    cylinderCappedTimePacket_original hN A P r σ hb f hf he hc hr R hR hs,map_smul]

#print axioms cylinderCappedTimePacket_original
#print axioms physicalCappedTimePacket_original

end QuantitativeMaass
