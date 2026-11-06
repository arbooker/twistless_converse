module

public import AsymptoticCylinderCutPositiveV1
public import AsymptoticRegularObservationNormalBoundV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight AsymptoticReconstructedCount
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def normalBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)
  BR^2+(observationsBound A hN P r s hs*BR)^2


end AsymptoticCylinderObservation

namespace AsymptoticSharedApproximation

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A single scale for the finite inverse polynomials in both
realizations, independent of weight, sector, root and cutoff height. -/
noncomputable def normalBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  max (AsymptoticCylinderObservation.normalBound A hN P r s hs)
    (AsymptoticRegularObservation.wholeNormalBound A hN P r s hs)

theorem cylinder_bound_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    AsymptoticCylinderObservation.normalBound A hN P r s hs≤normalBound A hN P r s hs := le_max_left _ _

theorem regular_bound_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    AsymptoticRegularObservation.wholeNormalBound A hN P r s hs≤normalBound A hN P r s hs := le_max_right _ _

#print axioms cylinder_bound_le
#print axioms regular_bound_le

end AsymptoticSharedApproximation
