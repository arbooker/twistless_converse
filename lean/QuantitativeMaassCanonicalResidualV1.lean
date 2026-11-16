module

public import QuantitativeMaassCompletedTerminalEmbeddingV1
public import QuantitativeMaassNonzeroFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticSectorSigns QuantitativeNewGap
open scoped Topology

namespace QuantitativeMaass

/-- Every compact twist residual annihilates the actual weighted image
of the completed canonical sector; continuity supplies the nonsmooth vectors. -/
theorem completedNewSign_weighted_residual (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (q : ℕ) (hq : 0<q)
    {s : Set ℍ} (hs : IsCompact s) (x : AutomorphicSpace N)
    (hx : x∈completedNewSignSpace N hN χ) :
    AsymptoticTwistObservation.residual N q hN hq hs hε v 0 (multiplier e q)
      (AsymptoticCylinderLift.lift (translationToProductCylinder
        (weightedQuotientEmbedding N hε hv x)))=0 := by
  let J := AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
    (translationToProductCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (weightedQuotientEmbedding N hε hv))
  let L := (AsymptoticTwistObservation.residual N q hN hq hs hε v 0 (multiplier e q)).comp J
  change L x=0
  obtain ⟨f,hf,hm,ht⟩ := completedNewSignSpace_continuous_approximation N hN χ x hx
  have hz (n : ℕ) : L (AutomorphicL2.denseEmbedding _ _ (f n))=0 := by
    obtain ⟨hw,hS⟩ := completedNewSign_continuous_sector N hN χ e hχW hχS (f n) (hf n) (hm n)
    change AsymptoticTwistObservation.residual N q hN hq hs hε v 0 (multiplier e q)
      (AsymptoticCylinderLift.lift (translationToProductCylinder
        (weightedQuotientEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ (f n)))))=0
    rw [weightedQuotientEmbedding_representative]
    apply AsymptoticTwistObservation.residual_eq_zero N q hN hq hs hε v 0 (multiplier e q)
      (upperZeroExtension (f n).val) (upperZeroExtension_periodic N (f n))
    · intro z _
      simpa only [mul_zero,pow_zero,div_one] using
        newSpace_all_analytic_laws N hN (f n) (hf n) (hm n).2.1 e hw hS q hq z
    · exact weightedQuotientRepresentative_strip N hε hv (f n)
  have hl := L.continuous.tendsto x |>.comp ht
  have hr : Tendsto (fun n => L (AutomorphicL2.denseEmbedding _ _ (f n))) atTop (𝓝 0) := by
    simp only [hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hl hr

theorem completedNewSignTerminalEmbedding_residual {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (q : ℕ) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    (x : completedNewSignSpace N hN χ) :
    EulerHilbert.Nonzero.residualRow A hN P e q hq hs
      (completedNewSignTerminalEmbedding A hN P χ e x)=0 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  change AsymptoticTwistObservation.residual N q hN hq hs P'.epsilon_pos (P'.s+3) 0 (multiplier e q)
    (AsymptoticCylinderLift.lift (EulerHilbert.Nonzero.normalized A hN P e
      (completedNewSignTerminalEmbedding A hN P χ e x)))=0
  rw [completedNewSignTerminalEmbedding_normalized A hN P χ e hχW hχS]
  exact completedNewSign_weighted_residual N hN χ e hχW hχS P'.epsilon_pos
    (show 1≤P'.s+3 by omega) q hq hs x.val x.property

/-- Every finite positive residual filter fixes the canonical target exactly. -/
theorem completedNewSignTerminalEmbedding_filter {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (x : completedNewSignSpace N hN χ) :
    EulerHilbert.Nonzero.residualFilter A hN P e hs qs d
      (completedNewSignTerminalEmbedding A hN P χ e x)=
        completedNewSignTerminalEmbedding A hN P χ e x := by
  apply gram_filter_fixes qs
    (fun q : ℕ+ => EulerHilbert.Nonzero.residualRow A hN P e q.val q.property hs)
  intro q _
  exact completedNewSignTerminalEmbedding_residual A hN P χ e hχW hχS q.val q.property hs x

#print axioms completedNewSign_weighted_residual
#print axioms completedNewSignTerminalEmbedding_residual
#print axioms completedNewSignTerminalEmbedding_filter

end QuantitativeMaass
