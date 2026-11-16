module

public import QuantitativeMaassNonzeroReconstructionV1
public import QuantitativeMaassEulerResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass.EulerHilbert.Nonzero

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Original twist residual on the normalized nonzero-mode terminal space. -/
def residualRow (e : Sector N) (q : ℕ) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s) :=
  (AsymptoticTwistObservation.residual N q hN hq hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q)).comp
      (physicalIsometry A hN P e).toContinuousLinearMap

/-- The actual finite positive residual filter on the corrected terminal space. -/
def residualFilter (e : Sector N) {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :=
  let B := fun q : ℕ+ => residualRow A hN P e q.val q.property hs
  (1-(1+∑ q∈qs,‖B q‖^2)⁻¹ • (∑ q∈qs,(B q).adjoint.comp (B q)))^d

theorem residualFilter_order (e : Sector N) {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    0≤residualFilter A hN P e hs qs d ∧ residualFilter A hN P e hs qs d≤1 ∧
      ‖residualFilter A hN P e hs qs d‖≤1 := by
  let B := fun q : ℕ+ => residualRow A hN P e q.val q.property hs
  obtain ⟨h0,h1⟩ := QuantitativePositiveGramFilter.gram_sum_bounds qs B
  exact QuantitativePositiveGramFilter.filter_order _ (by positivity) h0 h1 d

/-- Every original Euler solution has one normalized nonzero-mode datum
fixed by all finite residual filters simultaneously. -/
theorem original_all_filters (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε),
      physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      ∀ (s : Set ℍ) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ),
        residualFilter A hN P e hs qs d g=g := by
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

#print axioms residualFilter_order
#print axioms original_all_filters

end QuantitativeMaass.EulerHilbert.Nonzero
