module

public import QuantitativeMaassCrossCylinderPacketV1
public import QuantitativeArithmeticMaassResidualColumnGraphV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The broad-packet approximation uses precisely the residual column
whose integrated energy has already been estimated. -/
theorem broadPacket_cross_spectralResidual_error_sq (N : ℕ) (b : SmoothUpperSeed)
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0), (∀ g ∈ S, g • z ∈ K) → S.card ≤ m0)
    (B H C : ℝ) (hB : 0≤B) (hH : 0≤H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖≤H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (t L : ℝ) (ht : 0<t) (hL : 0<L)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    let g := cylinderTimeColumn f hc he R hR hs z
    let d := cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even t f he)
      R hR (spectralTimeResidual_support t f R hs) z
    let T := crossQuotientLocalization N 0 K hK b hbound
    ‖broadQuotientPacket N L hL t (T (cylinderAutomorphic g))-T (cylinderAutomorphic g)‖^2 ≤
      ((2*Real.cosh ((1/L)/2)/(t*L))^2*(3*(mN:ℝ)*(m0:ℝ)))*
        ((B^2+4*C^2)*‖d‖^2+(H^2+8*C^2*(1+(t^2+1/4)))*‖g‖^2) := by
  intro g d T
  have hg := cylinderTimeColumn_spectralResidual_graph f hc he R hR hs z t
  have hcast : ((t^2+1/4 : ℝ) : ℂ)=(t:ℂ)^2+1/4 := by push_cast; rfl
  rw [hcast] at hg
  have hp := broadPacket_cross_graph_error_sq N 0 b hreal K hK hbK mN m0 hmN hm0
    B H C hB hH hbound hlap hgrad t L ht hL
    (cylinderAutomorphic g) (cylinderAutomorphic d)
    (cylinderTimeColumn_exists_seed f hc he R hR hs z) hg
  simpa only [cylinderAutomorphic.norm_map,mul_assoc] using hp

/-- Integrating the actual compact-transfer error requires only the two
already available cylinder-column energies on the chosen center region. -/
theorem broadPacket_cross_cylinder_energy (N : ℕ) (b : SmoothUpperSeed)
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0), (∀ g ∈ S, g • z ∈ K) → S.card ≤ m0)
    (B H C : ℝ) (hB : 0≤B) (hH : 0≤H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖≤H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (t L : ℝ) (ht : 0<t) (hL : 0<L)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f ⊆ Icc (-R) R)
    (Ω : Set ℍ) (hΩ : IsCompact Ω) :
    let g := cylinderTimeColumn f hc he R hR hs
    let d := cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even t f he)
      R hR (spectralTimeResidual_support t f R hs)
    let T := crossQuotientLocalization N 0 K hK b hbound
    (∫ z in Ω, ‖broadQuotientPacket N L hL t (T (cylinderAutomorphic (g z)))-
      T (cylinderAutomorphic (g z))‖^2) ≤
      ((2*Real.cosh ((1/L)/2)/(t*L))^2*(3*(mN:ℝ)*(m0:ℝ)))*
        ((B^2+4*C^2)*(∫ z in Ω,‖d z‖^2)+
          (H^2+8*C^2*(1+(t^2+1/4)))*(∫ z in Ω,‖g z‖^2)) := by
  intro g d T
  let Q := broadQuotientPacket N L hL t
  let A := (2*Real.cosh ((1/L)/2)/(t*L))^2*(3*(mN:ℝ)*(m0:ℝ))
  let U := B^2+4*C^2
  let V := H^2+8*C^2*(1+(t^2+1/4))
  have hg : Continuous g := cylinderAbelColumn_continuous _ _ R hR _
  have hd : Continuous d := cylinderAbelColumn_continuous _ _ R hR _
  have hgI : IntegrableOn (fun z => ‖g z‖^2) Ω :=
    (hg.norm.pow 2).continuousOn.integrableOn_compact hΩ
  have hdI : IntegrableOn (fun z => ‖d z‖^2) Ω :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact hΩ
  have hx := T.continuous.comp (cylinderAutomorphic.continuous.comp hg)
  have herror : IntegrableOn (fun z => ‖Q (T (cylinderAutomorphic (g z)))-
      T (cylinderAutomorphic (g z))‖^2) Ω :=
    (((Q.continuous.comp hx).sub hx).norm.pow 2).continuousOn.integrableOn_compact hΩ
  have hmajor : IntegrableOn (fun z => A*(U*‖d z‖^2+V*‖g z‖^2)) Ω :=
    ((hdI.const_mul U).add (hgI.const_mul V)).const_mul A
  have hp := integral_mono herror hmajor (fun z =>
    broadPacket_cross_spectralResidual_error_sq N b hreal K hK hbK mN m0 hmN hm0
      B H C hB hH hbound hlap hgrad t L ht hL f hc he R hR hs z)
  apply hp.trans_eq
  rw [integral_const_mul,integral_add (hdI.const_mul U) (hgI.const_mul V),
    integral_const_mul,integral_const_mul]

#print axioms broadPacket_cross_spectralResidual_error_sq
#print axioms broadPacket_cross_cylinder_energy
end QuantitativeMaass
