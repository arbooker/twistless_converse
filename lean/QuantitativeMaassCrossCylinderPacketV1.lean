module

public import QuantitativeMaassCrossGraphPacketV1
public import QuantitativeMaassCylinderColumnLaplacianV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

theorem cylinderTimeColumn_exists_seed (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    ∃ v : SmoothUpperSeed, poincareSeedVector 0 v=
      cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z) :=
  ⟨_, (cylinderAbelColumn_eq_physicalRadialSeed (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs) z).symm⟩

/-- Literal cylinder packet columns satisfy the broad approximation
estimate after compact transfer to level N. The source residual is the
actual second time derivative, not an assumed spectral concentration. -/
theorem broadPacket_cross_cylinder_error_sq (N : ℕ) (b : SmoothUpperSeed)
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m0)
    (B H C : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖ ≤ H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (t L : ℝ) (ht : 0<t) (hL : 0<L)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    let g := cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z)
    let d := -cylinderAutomorphic (cylinderTimeColumn (timeSecondDerivative f)
      (timeSecondDerivative_compact f hc) (timeSecondDerivative_even f he)
      R hR (timeSecondDerivative_support f R hs) z)-(t:ℂ)^2 • g
    let T := crossQuotientLocalization N 0 K hK b hbound
    ‖broadQuotientPacket N L hL t (T g)-T g‖^2 ≤
      (2*Real.cosh ((1/L)/2)/(t*L))^2 * (3*(mN : ℝ)*(m0 : ℝ)*
        ((B^2+4*C^2)*‖d‖^2+(H^2+8*C^2*(1+(t^2+1/4)))*‖g‖^2)) :=
  broadPacket_cross_graph_error_sq N 0 b hreal K hK hbK mN m0 hmN hm0
    B H C hB hH hbound hlap hgrad t L ht hL _ _
    (cylinderTimeColumn_exists_seed f hc he R hR hs z)
    (cylinderTimeColumn_residual_friedrichsGraph f hc he R hR hs z t)

#print axioms cylinderTimeColumn_exists_seed
#print axioms broadPacket_cross_cylinder_error_sq

end QuantitativeMaass
