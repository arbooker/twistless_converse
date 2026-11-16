module

public import QuantitativeMaassNewSpaceAllLawsV1
public import QuantitativeMaassCuspidalTerminalDataV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNinaMaass QuantitativeNewGap

namespace QuantitativeMaass

theorem weightedQuotientRepresentative_strip (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AsymptoticCylinderLift.lift
        (translationToProductCylinder (weightedQuotientRepresentative N hε hv f))=ᵐ[volume]
      AsymptoticWeightedBranches.stripSection ε v 0 (upperZeroExtension f.val) := by
  rw [←productCylinderToTranslation_lift,translationToProductCylinder_inverse]
  have hh := cylinderZeroExtension_coeFn_of_ae (weightedQuotientRepresentative N hε hv f)
    (fun z => (AsymptoticCompactBranch.cap ε v z:ℂ)*f.val z)
    (weightedRepresentative_memLp N hε hv f).coeFn_toLp
  apply hh.trans
  apply Eventually.of_forall
  intro z
  unfold AsymptoticWeightedBranches.stripSection
  apply congrFun
  apply Set.indicator_congr
  intro y _
  simp only [AsymptoticWeightedBranches.weighted,AsymptoticCompactBranch.cap,pow_zero,mul_one,
    upperZeroExtension_apply]

/-- The actual continuous new/sign function is reconstructed from its
terminal strip restriction using the same fixed certificate as the Euler count. -/
theorem continuous_newSpace_reconstruction {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hx : AutomorphicL2.denseEmbedding _ _ f∈newSpace N hN)
    (e : Sector N)
    (hW : ∀ z,sign e.1*f.val (frickeLabel N hN • z)=f.val z)
    (hS : ∀ p : SimplePrime N,∀ z,
      f.val (localAtkinLabel N hN p • z)= -delta e p.val*f.val z) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let g := translationToProductCylinder
      (weightedQuotientRepresentative N P'.epsilon_pos (show 1≤P'.s+3 by omega) f)
    EulerHilbert.reconstruction A hN P e
      (AsymptoticRegionL2.restrict AsymptoticCylinder.measure
        (AsymptoticCylinderTerminal.region P'.ε) (AsymptoticCylinderTerminal.region_measurable P'.ε) g)=g := by
  dsimp only
  apply AsymptoticCylinderReconstruction.extension_of_FE A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) 0
    (upperZeroExtension f.val) (upperZeroExtension_periodic N f)
  · intro q hq z _
    simpa only [mul_zero,pow_zero,div_one] using
      newSpace_all_analytic_laws N hN f hf hx e hW hS q (Nat.pos_of_dvd_of_pos hq hQ) z
  · exact weightedQuotientRepresentative_strip N _ _ f
  · exact lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P
      (multiplier e) (fun q _ => multiplier_norm e q) 0) (by norm_num)

#print axioms weightedQuotientRepresentative_strip
#print axioms continuous_newSpace_reconstruction

end QuantitativeMaass
