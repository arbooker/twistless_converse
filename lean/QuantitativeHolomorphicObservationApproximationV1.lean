module

public import QuantitativeHolomorphicObservationFilterV1
public import QuantitativeHolomorphicCutNormalizationV1
public import QuantitativeHolomorphicNewtonContractionV1
public import QuantitativeHolomorphicFilterStabilityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- Common scalar error for the actual compact finite Newton reconstruction. -/
def normalizedCutError (P : Parameters A) (Y : ℝ) (d J n : ℕ) : ℝ :=
  cutCountReconstructionError A P Y d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
    (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P)

/-- The ambient cylinder filter associated to any terminal reconstruction.
Its observations and their norm bounds are the literal compact twist/ramified rows. -/
def observationCylinderFilter (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i))
    (V : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε
      →L[ℂ] AsymptoticCylinder.Space) (d : ℕ) :=
  let L := fun i => rowOperator hN (r i) e (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) (h+1)
  let b := fun i => rowBound hN (r i) (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  V.comp ((finiteRowFilter qs L b V d).comp V.adjoint)

theorem observationCylinderFilter_exact (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    observationCylinderFilter A hN P h e qs r s hs
      (normalizedCountReconstruction A hN P h e) d =
    (normalizedCountReconstruction A hN P h e).comp
      ((normalizedObservationFilter A hN P h e qs r s hs d).comp
        (normalizedCountReconstruction A hN P h e).adjoint) := rfl

/-- Quantitative replacement of the actual positive global filter by its
finite Newton reconstruction.  The degree loss is linear, with no dependence
on the number or norms of observation rows.  All cutoff and reconstruction
bounds on the right are proved for the actual counting operators. -/
theorem observationCylinderFilter_cut_error (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y : ℝ) (hY : 0 ≤ Y)
    (j J n d : ℕ) (hJ : 0 < J) :
    ‖observationCylinderFilter A hN P h e qs r s hs
        (polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n) d -
      observationCylinderFilter A hN P h e qs r s hs
        (normalizedCountReconstruction A hN P h e) d‖ ≤
      (2 * d + 2 : ℝ) * normalizedCutError A P Y j J n := by
  let U := normalizedCountReconstruction A hN P h e
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  have hU : ‖U‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedCountReconstruction_norm, one_mul]
  have hV : ‖V‖ ≤ 1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hd := cut_normalizedCountReconstruction_closed_error A hN P h n e Y hY j J hJ
  exact (finiteRowFilter_sandwich_difference qs _ _
    (fun i => rowOperator_norm_le hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) (h+1)) U V hU hV d).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))

#print axioms observationCylinderFilter_cut_error

end QuantitativeHolomorphic
