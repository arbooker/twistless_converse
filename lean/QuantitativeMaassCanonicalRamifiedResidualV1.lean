module

public import QuantitativeMaassCompletedTerminalEmbeddingV1
public import QuantitativeMaassNonzeroFilterV1
public import QuantitativeMaassRamifiedResidualZeroV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticOrbitDecode
open scoped Topology

namespace QuantitativeMaass

/-- Every compact ramified residual annihilates the actual weighted image
of the completed canonical sector; continuity supplies the nonsmooth vectors. -/
theorem completedNewSign_weighted_ramified_residual (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (p : ℕ) (hp : p.Prime) (hpN : p∣N)
    {s : Set ℍ} (hs : IsCompact s) (x : AutomorphicSpace N)
    (hx : x∈completedNewSignSpace N hN χ) :
    AsymptoticRamifiedObservation.residual p hp.pos hs hε v 0 (AsymptoticCylinderRamified.eigenvalue e p)
      (AsymptoticCylinderLift.lift (translationToProductCylinder
        (weightedQuotientEmbedding N hε hv x)))=0 := by
  let J := AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
    (translationToProductCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (weightedQuotientEmbedding N hε hv))
  let L := (AsymptoticRamifiedObservation.residual p hp.pos hs hε v 0 (AsymptoticCylinderRamified.eigenvalue e p)).comp J
  change L x=0
  obtain ⟨f,hf,hm,ht⟩ := completedNewSignSpace_continuous_approximation N hN χ x hx
  have hz (n : ℕ) : L (AutomorphicL2.denseEmbedding _ _ (f n))=0 := by
    obtain ⟨_hw,hS⟩ := completedNewSign_continuous_sector N hN χ e hχW hχS (f n) (hf n) (hm n)
    change AsymptoticRamifiedObservation.residual p hp.pos hs hε v 0 (AsymptoticCylinderRamified.eigenvalue e p)
      (AsymptoticCylinderLift.lift (translationToProductCylinder
        (weightedQuotientEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ (f n)))))=0
    rw [weightedQuotientEmbedding_representative]
    apply ramified_residual_weightZero_eq_zero p hp.pos hs hε v
      (AsymptoticCylinderRamified.eigenvalue e p)
      (upperZeroExtension (f n).val) (upperZeroExtension_periodic N (f n))
    · intro z _hz
      have hU : ∀ z : ℍ, ∑ a : Fin p,(f n).val (ramifiedLabel p hp.pos a • z)=
          AsymptoticCylinderRamified.eigenvalue e p*(f n).val z := by
        intro y
        classical
        by_cases hsimple : p∈simplePrimes N
        · have hp2 := (mem_simplePrimes.mp hsimple).2.2
          simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hp2,neg_neg] using
            newSpace_simple_ramified N hN (f n) (hf n) (hm n).2.1 p hp hpN hp2
              (-delta e p) (hS ⟨p,hsimple⟩) y
        · have hp2 : p^2∣N := by
            by_contra hh
            exact hsimple (mem_simplePrimes.mpr ⟨hp,hpN,hh⟩)
          simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hp2,zero_mul] using
            newSpace_repeated_ramified_zero N p hN hp hp2 (f n) (hf n) (hm n).2.1 y
      have hh := upperZeroExtension_ramified p hp.pos (f n).val
        (AsymptoticCylinderRamified.eigenvalue e p) hU z
      unfold ramifiedAverage at hh
      rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => upperZeroExtension (f n).val ((z+(a:ℂ))/(p:ℂ))) p] at hh
      exact hh
    · exact weightedQuotientRepresentative_strip N hε hv (f n)
  have hl := L.continuous.tendsto x |>.comp ht
  have hr : Tendsto (fun n => L (AutomorphicL2.denseEmbedding _ _ (f n))) atTop (𝓝 0) := by
    simp only [hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hl hr


#print axioms completedNewSign_weighted_ramified_residual
end QuantitativeMaass
