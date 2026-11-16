module

public import QuantitativeMaassCrossSeedResidualV1
public import QuantitativeMaassBroadPacketV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The broad packet approximates the actual compact cross-quotient
transfer, with the cutoff retained inside the wave. The estimate uses
only the original source L2 mass and spectral residual. -/
theorem broadPacket_cross_seed_error_sq (N M : ℕ) (v b : SmoothUpperSeed)
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
    (t L : ℝ) (ht : 0<t) (hL : 0<L) :
    let q := b.localized (congruencePoincareCartesian M v.toFun)
      (congruencePoincareCartesian_smooth M v.smooth v.compact)
    ‖broadQuotientPacket N L hL t (poincareSeedVector N q)-poincareSeedVector N q‖^2 ≤
      (2*Real.cosh ((1/L)/2)/(t*L))^2 * (3*(mN : ℝ)*(mM : ℝ)*
        ((B^2+4*C^2)*‖poincareSeedVector M v.laplacian-
          (((t:ℂ)^2+1/4) • poincareSeedVector M v)‖^2+
          (H^2+8*C^2*(1+(t^2+1/4)))*‖poincareSeedVector M v‖^2)) := by
  intro q
  let μ : ℂ := (t:ℂ)^2+1/4
  let d := poincareSeedVector N q.laplacian-μ • poincareSeedVector N q
  have hw := broadQuotientPacket_residual_norm N (poincareSeedVector N q) d t L ht hL
    (friedrichsGraph_seed_residual N q μ)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hw
  rw [mul_pow] at hs
  have hr := cross_seed_residual_norm_sq_le N M v b hreal K hK hbK mN mM hmN hmM
    μ B H C hB hH hbound hlap hgrad
  have he := poincare_energy_residual_bound M v (t^2+1/4) (by positivity)
  have hcast : ((t^2+1/4 : ℝ) : ℂ)=μ := by
    dsimp only [μ]
    push_cast
    rfl
  rw [hcast] at he
  have hres : ‖d‖^2 ≤ 3*(mN : ℝ)*(mM : ℝ)*
      ((B^2+4*C^2)*‖poincareSeedVector M v.laplacian-μ • poincareSeedVector M v‖^2+
        (H^2+8*C^2*(1+(t^2+1/4)))*‖poincareSeedVector M v‖^2) := by
    apply (hr.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left he (by positivity)))
      (by positivity))).trans_eq
    ring
  exact hs.trans (mul_le_mul_of_nonneg_left hres (sq_nonneg _))

#print axioms broadPacket_cross_seed_error_sq

end QuantitativeMaass
