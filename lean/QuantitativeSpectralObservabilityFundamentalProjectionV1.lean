module

public import QuantitativeSpectralObservabilityFundamentalFiberV1
public import AsymptoticOrbitDiagonalV1
public import AsymptoticOrbitRegionV1
public import AsymptoticOrbitBranchAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- On the invariant conull set, the quotient embedding has exactly the
fundamental-domain coordinate corner as its range projection. -/
theorem fundamentalInduction_cogram (N : ℕ) (x : ℍ) (hx : fundamentalGood N x) :
    (fundamentalInduction N x hx).toContinuousLinearMap.comp
      (fundamentalInduction N x hx).toContinuousLinearMap.adjoint =
        corner (fundamentalSet N) x := by
  apply eq_of_matrix_eq
  intro g h
  have he := AsymptoticFiberIsometry.projection_apply_delta (classOf N)
    (fun a => fundamentalAmplitude N (a • x)) (fundamental_amplitude_hasSum N x hx) g h
  change matrix ((fundamentalInduction N x hx).toContinuousLinearMap.comp
      (fundamentalInduction N x hx).toContinuousLinearMap.adjoint) g h = _ at he
  rw [he]
  change _ = (corner (fundamentalSet N) x (delta h)) g
  rw [corner_apply]
  by_cases hg : g • x∈fundamentalSet N
  · rw [ite_eq_left hg]
    by_cases hh : h • x∈fundamentalSet N
    · by_cases hc : classOf N g=classOf N h
      · have hgh := fundamental_class_unique N x hx g h hc hg hh
        subst h
        simp [fundamentalAmplitude,hg,delta]
      · have hgh : g≠h := fun e => hc (congrArg (classOf N) e)
        simp [hc,delta,hgh]
    · have hgh : g≠h := fun e => hh (e ▸ hg)
      simp [fundamentalAmplitude,hh,delta,hgh]
  · simp [fundamentalAmplitude,hg]

/-- Extracting the unique quotient coordinate preserves norm for vectors
supported on the actual fundamental set. -/
theorem fundamentalInduction_adjoint_norm (N : ℕ) (x : ℍ)
    (hx : fundamentalGood N x) (v : ℓ²(OrbitGroup,ℂ))
    (hv : corner (fundamentalSet N) x v=v) :
    ‖(fundamentalInduction N x hx).toContinuousLinearMap.adjoint v‖=‖v‖ := by
  have he := congrArg (fun B : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) => B v)
    (fundamentalInduction_cogram N x hx)
  change fundamentalInduction N x hx
    ((fundamentalInduction N x hx).toContinuousLinearMap.adjoint v)=_ at he
  rw [hv] at he
  calc
    _ = ‖fundamentalInduction N x hx
      ((fundamentalInduction N x hx).toContinuousLinearMap.adjoint v)‖ :=
        ((fundamentalInduction N x hx).norm_map _).symm
    _ = ‖v‖ := congrArg norm he

#print axioms fundamentalInduction_cogram
#print axioms fundamentalInduction_adjoint_norm

end QuantitativeSpectralObservability
