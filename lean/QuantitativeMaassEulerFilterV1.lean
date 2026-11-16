module

public import QuantitativeMaassEulerResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass.EulerHilbert

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- A positive contraction built from the actual finite family of original
weight-zero residual rows; it has no spectral parameter. -/
def residualFilter (e : Sector N) {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :=
  let B := fun q : ℕ+ => residualRow A hN P e q.val q.property hs
  (1-(1+∑ q∈qs,‖B q‖^2)⁻¹ • (∑ q∈qs,(B q).adjoint.comp (B q)))^d

theorem residualFilter_order (e : Sector N) {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    0≤residualFilter A hN P e hs qs d ∧ residualFilter A hN P e hs qs d≤1 ∧
      ‖residualFilter A hN P e hs qs d‖≤1 := by
  let B := fun q : ℕ+ => residualRow A hN P e q.val q.property hs
  obtain ⟨h0,h1⟩ := QuantitativePositiveGramFilter.gram_sum_bounds qs B
  exact QuantitativePositiveGramFilter.filter_order _ (by positivity) h0 h1 d

/-- Every finite residual filter fixes the actual normalized original datum,
simultaneously at all real spectral parameters, all compact cutoffs and all
polynomial depths. The datum and its finite sector are constructed. -/
theorem original_all_filters (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      (AsymptoticCylinderLift.lift (normalized A hN P e g) =ᵐ[volume]
        AsymptoticWeightedBranches.stripSection (AsymptoticReconstructedCount.parameters A P).ε
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (principalEulerPhysical b r σ)) ∧
      ∀ (s : Set ℍ) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ),
        residualFilter A hN P e hs qs d g=g := by
  obtain ⟨e,g,hg,hres⟩ := original_normalized_residuals A hN P r σ hb
  refine ⟨e,g,hg,?_⟩
  intro s hs qs d
  exact QuantitativeMaass.gram_filter_fixes qs
    (fun q : ℕ+ => residualRow A hN P e q.val q.property hs) g
    (fun q _ => hres q.val q.property s hs) _ d

#print axioms residualFilter_order
#print axioms original_all_filters

end QuantitativeMaass.EulerHilbert
