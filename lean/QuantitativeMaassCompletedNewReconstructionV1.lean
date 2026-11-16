module

public import QuantitativeMaassCompletedSectorSignsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNinaMaass QuantitativeNewGap
open scoped Topology

namespace QuantitativeMaass

/-- The fixed Euler reconstruction is the identity on the weighted image
of every completed new/sign vector with matching sector signs. -/
theorem completedNewSign_reconstruction {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : AutomorphicSpace N) (hx : x∈completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let g := translationToProductCylinder
      (weightedQuotientEmbedding N P'.epsilon_pos (show 1≤P'.s+3 by omega) x)
    EulerHilbert.reconstruction A hN P e
      (AsymptoticRegionL2.restrict AsymptoticCylinder.measure
        (AsymptoticCylinderTerminal.region P'.ε) (AsymptoticCylinderTerminal.region_measurable P'.ε) g)=g := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let J := translationToProductCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (weightedQuotientEmbedding N P'.epsilon_pos (show 1≤P'.s+3 by omega))
  let T := AsymptoticRegionL2.restrict AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region P'.ε) (AsymptoticCylinderTerminal.region_measurable P'.ε)
  let L := (EulerHilbert.reconstruction A hN P e).comp (T.comp J)
  change L x=J x
  obtain ⟨f,hf,hm,ht⟩ := completedNewSignSpace_continuous_approximation N hN χ x hx
  have he (n : ℕ) : L (AutomorphicL2.denseEmbedding _ _ (f n))=
      J (AutomorphicL2.denseEmbedding _ _ (f n)) := by
    obtain ⟨hw,hs⟩ := completedNewSign_continuous_sector N hN χ e hχW hχS (f n) (hf n) (hm n)
    have hh := continuous_newSpace_reconstruction A hN P (f n) (hf n) (hm n).2.1 e hw hs
    change EulerHilbert.reconstruction A hN P e
      (T (translationToProductCylinder
        (weightedQuotientEmbedding N P'.epsilon_pos (show 1≤P'.s+3 by omega)
          (AutomorphicL2.denseEmbedding _ _ (f n)))))=
      translationToProductCylinder
        (weightedQuotientEmbedding N P'.epsilon_pos (show 1≤P'.s+3 by omega)
          (AutomorphicL2.denseEmbedding _ _ (f n)))
    rw [weightedQuotientEmbedding_representative]
    exact hh
  have hl := L.continuous.tendsto x |>.comp ht
  have hr := J.continuous.tendsto x |>.comp ht
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n => (he n).symm)))

/-- The same identity uses the actual nonzero-mode terminal data map;
the zero-mode condition is supplied by cuspidality. -/
theorem completedNewSign_nonzero_reconstruction {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    EulerHilbert.Nonzero.reconstruction A hN P e
      (cuspidalTerminalData N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) ⟨x.val,x.property.1⟩)=
      translationToProductCylinder
        (completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x) := by
  exact completedNewSign_reconstruction A hN P χ e hχW hχS x.val x.property

#print axioms completedNewSign_reconstruction
#print axioms completedNewSign_nonzero_reconstruction

end QuantitativeMaass
