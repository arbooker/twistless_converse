module

public import AsymptoticRegularObservationNormalBoundV1
public import AsymptoticRegularInverseV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The inverse of the actual completed normal family, expressed by a
common-scale Neumann series on the fixed counting Hilbert space. -/
noncomputable def wholeInverse (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticCoerciveNeumann.inverse (wholeNormalBound A hN P r s hs) (wholeNormal A hN P r s hs e z)

theorem wholeInverse_mul (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    (wholeInverse A hN P r s hs e z).comp (wholeNormal A hN P r s hs e z)=1 :=
  AsymptoticCoerciveNeumann.inverse_mul _ _ (wholeNormal_norm_le A hN P r s hs e z)
    (wholeNormal_coercive A hN P r s hs e z)

theorem wholeNormal_mul_inverse (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    (wholeNormal A hN P r s hs e z).comp (wholeInverse A hN P r s hs e z)=1 :=
  AsymptoticCoerciveNeumann.mul_inverse _ _ (wholeNormal_norm_le A hN P r s hs e z)
    (wholeNormal_coercive A hN P r s hs e z)

theorem wholeInverse_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    ‖wholeInverse A hN P r s hs e z‖≤1 :=
  AsymptoticCoerciveNeumann.inverse_norm_le _ _ (wholeNormal_norm_le A hN P r s hs e z)
    (wholeNormal_coercive A hN P r s hs e z)

theorem wholeInverse_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Covariant (wholeInverse A hN P r s hs e) :=
  inverse_covariant _ _ (wholeNormal_covariant A hN P r s hs e)
    (wholeNormal_norm_le A hN P r s hs e) (wholeNormal_coercive A hN P r s hs e)

theorem wholeInverse_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (wholeInverse A hN P r s hs e z) a b) :=
  inverse_matrix_measurable _ _ (wholeNormal_matrix_measurable A hN P r s hs e)
    (wholeNormal_norm_le A hN P r s hs e) (wholeNormal_coercive A hN P r s hs e) a b

#print axioms wholeInverse_mul
#print axioms wholeNormal_mul_inverse
#print axioms wholeInverse_norm_le
#print axioms wholeInverse_covariant
#print axioms wholeInverse_matrix_measurable

end AsymptoticRegularObservation
