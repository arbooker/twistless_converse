module

public import QuantitativeMaassCrossSeedPacketV1
public import QuantitativeMaassCrossQuotientLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The estimate for a genuine graph-core vector is stated using the
completed transfer operator and its actual source graph residual. -/
theorem broadPacket_cross_graph_error_sq (N M : ℕ) (b : SmoothUpperSeed)
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B H C : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖ ≤ H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (t L : ℝ) (ht : 0<t) (hL : 0<L)
    (g d : AutomorphicSpace M) (hseed : ∃ v : SmoothUpperSeed, poincareSeedVector M v=g)
    (hg : FriedrichsGraph M g ((((t:ℂ)^2+1/4) • g)+d)) :
    let T := crossQuotientLocalization N M K hK b hbound
    ‖broadQuotientPacket N L hL t (T g)-T g‖^2 ≤
      (2*Real.cosh ((1/L)/2)/(t*L))^2 * (3*(mN : ℝ)*(mM : ℝ)*
        ((B^2+4*C^2)*‖d‖^2+(H^2+8*C^2*(1+(t^2+1/4)))*‖g‖^2)) := by
  obtain ⟨v,rfl⟩ := hseed
  have he := friedrichsGraph_singleValued M (friedrichsGraph_poincareSeed M v) hg
  have hd : poincareSeedVector M v.laplacian-
      (((t:ℂ)^2+1/4) • poincareSeedVector M v)=d := by
    rw [he]
    module
  dsimp only
  rw [crossQuotientLocalization_on_seed N M K hK b hbound hbK v]
  have hp := broadPacket_cross_seed_error_sq N M v b hreal K hK hbK mN mM hmN hmM
    B H C hB hH hbound hlap hgrad t L ht hL
  rw [hd] at hp
  exact hp

#print axioms broadPacket_cross_graph_error_sq

end QuantitativeMaass
