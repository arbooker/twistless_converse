module

public import AsymptoticFiniteHolomorphicNormalV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCylinderLift
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The concrete branch polynomial is precisely the lift of the actual
finite cylinder reconstruction polynomial. -/
theorem holomorphicSum_finiteAmbientExpression (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (h : ℕ) (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) :
    holomorphicSum (finiteAmbientExpression A hN P r s hs e Y n d I) (h+1)=
      lift.toContinuousLinearMap.comp
        (((AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I).comp
          ((AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I).comp
            (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I).adjoint)).comp
              lift.toContinuousLinearMap.adjoint) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let S := AsymptoticCylinderTerminal.ambientLift P'.ε
  let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
  let O := holomorphicRows hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  have hS : S.adjoint.comp S=1 := AsymptoticCylinderTerminal.ambientLift_adjoint_self P'.ε
  have hP : S.comp S.adjoint=AsymptoticCertificateOperators.highProjection A P' :=
    AsymptoticCylinderTerminal.ambientLift_self_adjoint P'.ε
  have hO := holomorphicRows_comp_lift hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  have ht := AsymptoticObservation.completed_polynomial_sandwich S hS
    lift.toContinuousLinearMap lift.adjoint_comp_self R O
    (AsymptoticSharedApproximation.normalBound A hN P r s hs) n
  rw [hP,hO] at ht
  rw [finiteAmbientExpression,holomorphicSum_compose,holomorphicSum_compose,
    holomorphicSum_inversePolynomial,holomorphicSum_adjoint,holomorphicSum_finiteNormalExpression,
    holomorphicSum_cutFull_eq_cylinder]
  exact ht

#print axioms holomorphicSum_finiteAmbientExpression

end AsymptoticFiniteBranch
