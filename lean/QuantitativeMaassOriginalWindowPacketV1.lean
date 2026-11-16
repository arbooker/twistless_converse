module

public import QuantitativeMaassEulerTimePacketV1
public import QuantitativeMaassWindowMajorantV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- One propagation constant chosen from the proved compact Fourier support. -/
def windowSupportRadius (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) : ℝ :=
  (symmetricWindowTimeTest_uniform_support K hc).choose

theorem windowSupportRadius_pos (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) : 0<windowSupportRadius K hc :=
  (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1

theorem windowSupportRadius_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Function.support (symmetricWindowTimeTest K R a b)⊆
      Icc (-(windowSupportRadius K hc*R)) (windowSupportRadius K hc*R) :=
  (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hR a b

/-- Actual bounded physical operator for a smoothed symmetric interval.
Its propagation radius and all spectral-action data are constructed here. -/
def physicalWindowPacket (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b ε : ℝ) (hε : 0<ε) (t : ℕ) :=
  physicalCappedTimePacket (symmetricWindowTimeTest K R a b)
    (symmetricWindowTimeTest_smooth K R a b) (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_compact K hc R a b hR) (symmetricWindowTimeTest_real K he R a b)
    (windowSupportRadius K hc*R) (mul_pos (windowSupportRadius_pos K hc) hR).le
    (windowSupportRadius_support K hc R hR a b) ε hε t

theorem physicalWindowPacket_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a c : ℝ) (ha : 0<a) :
    physicalWindowPacket K he hc R hR a c P.ε P.epsilon_pos (P.s+3)
      (principalEulerWeightedLp hN A P r σ hb)=
      (smoothedWindow K R (Icc a c∪Icc (-c) (-a)) r:ℂ) •
        principalEulerWeightedLp hN A P r σ hb := by
  unfold physicalWindowPacket
  rw [physicalCappedTimePacket_original hN A P r σ hb,
    symmetricWindowTimeTest_cosinePacket K he hc R a c r hR ha]

def windowInteriorConstant (K : SchwartzMap ℝ ℝ) (R δ : ℝ) (k : ℕ) : ℝ :=
  1-(∫ u,|u|^k*K u)/(R*δ)^k

/-- The normalized original-window majorant is an actual bounded operator,
with its normalization determined by the explicit scalar tail estimate. -/
def originalWindowMajorant (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b δ : ℝ) (k : ℕ) (ε : ℝ) (hε : 0<ε) (t : ℕ) :=
  ((windowInteriorConstant K R δ k)⁻¹:ℂ) •
    physicalWindowPacket K he hc R hR (a-δ) (b+δ) ε hε t

theorem originalWindowMajorant_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a c δ : ℝ) (k : ℕ) (ha : 0<a-δ) :
    originalWindowMajorant K he hc R hR a c δ k P.ε P.epsilon_pos (P.s+3)
      (principalEulerWeightedLp hN A P r σ hb)=
      (smoothedWindow K R (Icc (a-δ) (c+δ)∪Icc (-(c+δ)) (-(a-δ))) r /
        windowInteriorConstant K R δ k:ℂ) • principalEulerWeightedLp hN A P r σ hb := by
  unfold originalWindowMajorant
  rw [smul_apply,physicalWindowPacket_original hN A P r σ hb K he hc R hR _ _ ha,
    smul_smul]
  congr 1
  ring

theorem originalWindowMajorant_scalar_lower (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (a b δ r : ℝ) (k : ℕ)
    (hδ : 0<δ) (hr : r∈Icc a b) (htail : (∫ u,|u|^k*K u)/(R*δ)^k<1) :
    1≤smoothedWindow K R (Icc (a-δ) (b+δ)∪Icc (-(b+δ)) (-(a-δ))) r /
      windowInteriorConstant K R δ k := by
  apply (le_div_iff₀ (sub_pos.mpr htail)).mpr
  simpa only [one_mul,windowInteriorConstant] using
    enlarged_symmetricWindow_lower K hK hm R hR a b δ r hδ hr k

#print axioms windowSupportRadius_support
#print axioms physicalWindowPacket_original
#print axioms originalWindowMajorant_original
#print axioms originalWindowMajorant_scalar_lower

end QuantitativeMaass
