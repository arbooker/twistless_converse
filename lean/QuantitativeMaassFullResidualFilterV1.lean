module

public import QuantitativeMaassFullTerminalLeftInverseV1
public import QuantitativeHolomorphicCommonRowBoundV1
public import QuantitativeHolomorphicFilterStabilityV1
public import QuantitativeMaassEulerResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open AsymptoticCompactObservationCount
open QuantitativeHolomorphic
open scoped Topology

namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

theorem original_normalized_range (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
        FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
          multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
            (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  obtain ⟨e,g,hg,hFE⟩ := EulerHilbert.original_normalized_range A hN P r σ hb
  refine ⟨e,g,?_,hFE⟩
  apply MeasureTheory.Lp.ext
  exact hg.trans (principalEulerWeightedLp_coeFn hN A
    (AsymptoticReconstructedCount.parameters A P) r σ hb).symm

/-- Original twist residual on the normalized full terminal space. -/
def residualRow (e : Sector N) (q : ℕ) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s) :=
  (AsymptoticTwistObservation.residual N q hN hq hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q)).comp
      (physicalIsometry A hN P e).toContinuousLinearMap

/-- These explicit matrix-fold bounds are the same in the physical and
regular representations. They are independent of the sector and parameter. -/
def commonTwistBound {s : Set UpperHalfPlane} (hs : IsCompact s) (q : ℕ+) : ℝ :=
  rowBound hN (.twist q.val q.property) hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3)

def commonResidualFilter (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (qs : Finset ℕ+) (d : ℕ) :=
  (1-(finiteRowBound qs (commonTwistBound A hN P hs))⁻¹ •
    (∑ q∈qs,(residualRow A hN P e q.val q.property hs).adjoint.comp
      (residualRow A hN P e q.val q.property hs)))^d

theorem residualRow_common_bound (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (q : ℕ+) :
    ‖residualRow A hN P e q.val q.property hs‖ ≤ commonTwistBound A hN P hs q := by
  have hu := LinearIsometry.norm_toContinuousLinearMap_le (physicalIsometry A hN P e)
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans
  rw [mul_one]
  have hb := AsymptoticTwistObservation.residual_norm_le N q.val hN q.property hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q.val)
  simpa only [commonTwistBound, rowBound, multiplier_norm, one_mul] using hb

theorem commonResidualFilter_order (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    0≤commonResidualFilter A hN P e hs qs d ∧
      commonResidualFilter A hN P e hs qs d≤1 ∧
      ‖commonResidualFilter A hN P e hs qs d‖≤1 := by
  let B := fun q : ℕ+ => residualRow A hN P e q.val q.property hs
  have hg := QuantitativePositiveGramFilter.gram_sum_bounds qs B
  have hb : (1+∑ q∈qs,‖B q‖^2) ≤ finiteRowBound qs (commonTwistBound A hN P hs) := by
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro q _
    exact pow_le_pow_left₀ (norm_nonneg (B q))
      (show ‖B q‖ ≤ commonTwistBound A hN P hs q from
        residualRow_common_bound A hN P e hs q) 2
  exact QuantitativePositiveGramFilter.filter_order _ (finiteRowBound_pos _ _) hg.1
    (hg.2.trans (smul_le_smul_of_nonneg_right hb zero_le_one)) d

/-- Every original Euler solution has one normalized full datum
fixed by all finite residual filters simultaneously. -/
theorem original_all_filters (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      ∀ (s : Set ℍ) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ),
        commonResidualFilter A hN P e hs qs d g=g := by
  obtain ⟨e,g,hg,hFE⟩ := original_normalized_range A hN P r σ hb
  refine ⟨e,g,hg,?_⟩
  intro s hs qs d
  apply QuantitativeMaass.gram_filter_fixes qs
    (fun q : ℕ+ => residualRow A hN P e q.val q.property hs) g _ _ d
  intro q _
  have hgAE := principalEulerWeightedLp_coeFn hN A (AsymptoticReconstructedCount.parameters A P) r σ hb
  rw [←hg] at hgAE
  apply AsymptoticTwistObservation.residual_eq_zero N q.val hN q.property hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q.val)
    (principalEulerPhysical b r σ) (principalEulerPhysical_periodic b r σ) _ _ hgAE
  intro z hz
  simpa only [mul_zero,pow_zero,div_one] using hFE q.val q.property z hz

#print axioms commonResidualFilter_order
#print axioms original_all_filters

end QuantitativeMaass.EulerHilbert.FullTerminal
