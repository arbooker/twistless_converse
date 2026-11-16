module

public import QuantitativeMaassOrbitReconstructionEquationV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticSectorSigns QuantitativeNewGap AsymptoticWeightedBranches
open FinitenessCertificate FinitenessGlobalHeight
open scoped lp
namespace QuantitativeMaass.CountingMetric

/-- The constructed cap lift is exactly the orbit section of its pointwise
modular representative, not merely an equality of L2 classes. -/
theorem countingCapLift_section (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (z : ℍ) (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (a : AsymptoticRationalGroup.Group) :
    countingCapLift N hδ hν z f a=
      stripSection δ ν 0 (upperZeroExtension (orbitRepresentative N z hz f).val) (a • z) := by
  classical
  rw [countingCapLift_apply]
  unfold stripSection
  by_cases ha : a • z∈AsymptoticMassTransport.strip
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem ha]
    simp only [weighted,pow_zero,mul_one,upperZeroExtension_apply,orbitRepresentative_apply,
      AsymptoticCompactBranch.cap]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem ha]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A)

/-- The original all-modulus equations put the actual canonical cap lift
in the range of the literal certificate reconstruction. -/
theorem countingCapLift_extension (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (hK : ‖AsymptoticRegularCertificate.low A hN P (multiplier e) (P.s+3) z‖<1) :
    AsymptoticRegularReconstruction.extension A hN P (multiplier e) z
      (AsymptoticOrbitRegion.restrict (AsymptoticCertificateOperators.highStrip P.ε) z
        (countingCapLift N P.epsilon_pos (by omega : 1≤P.s+3) z f))=
      countingCapLift N P.epsilon_pos (by omega : 1≤P.s+3) z f := by
  apply regular_extension_of_FE A hN P (multiplier e) z
    (upperZeroExtension (orbitRepresentative N z hz f).val)
  · exact upperZeroExtension_periodic N (orbitRepresentative N z hz f)
  · intro q hq w _
    exact countingSector_orbit_all_laws N hN e f hf z hz q (Nat.pos_of_dvd_of_pos hq hQ) w
  · exact countingCapLift_section N P.epsilon_pos (by omega) z hz f
  · exact hK

/-- Common contraction parameters discharge the remaining analytic bound
in the cap-lift reconstruction identity. -/
theorem countingCapLift_common_extension (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e) :
    let P' := AsymptoticReconstructedCount.parameters A P
    AsymptoticRegularReconstruction.extension A hN P' (multiplier e) z
      (AsymptoticOrbitRegion.restrict (AsymptoticCertificateOperators.highStrip P'.ε) z
        (countingCapLift N P'.epsilon_pos (by omega : 1≤P'.s+3) z f))=
      countingCapLift N P'.epsilon_pos (by omega : 1≤P'.s+3) z f := by
  apply countingCapLift_extension A hN _ e z hz f hf
  exact (AsymptoticRegularReconstruction.parameters_contraction A hN P
    (multiplier e) (fun q _ => multiplier_norm e q) z).trans (by norm_num)

#print axioms countingCapLift_section
#print axioms countingCapLift_extension
#print axioms countingCapLift_common_extension
end QuantitativeMaass.CountingMetric
