module

public import QuantitativeSpectralObservabilityFundamentalTransferV1
public import QuantitativeSpectralObservabilityFundamentalProjectionV1
public import AsymptoticRegularHeightCutoffV1
public import AsymptoticIsometryRangeV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp

attribute [local instance] Classical.propDecidable

theorem fundamentalTransfer_gram (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x) :
    (fundamentalTransfer N hε ht x).adjoint.comp (fundamentalTransfer N hε ht x)=
      corner (fundamentalSet N) x := by
  have hi := AsymptoticFiberIsometry.adjoint_comp (classOf N)
    (fun g => amplitude N ε t (g • x)) (fibre_amplitude_hasSum N hε ht x)
  change (induction N hε ht x).toContinuousLinearMap.adjoint.comp
    (induction N hε ht x).toContinuousLinearMap=1 at hi
  simp only [fundamentalTransfer,dite_eq_left hx,adjoint_comp,adjoint_adjoint]
  calc
    _ = (fundamentalInduction N x hx).toContinuousLinearMap.comp
      (((induction N hε ht x).toContinuousLinearMap.adjoint.comp
        (induction N hε ht x).toContinuousLinearMap).comp
        (fundamentalInduction N x hx).toContinuousLinearMap.adjoint) := by
          simp only [comp_assoc]
    _ = corner (fundamentalSet N) x := by
      rw [hi]
      exact fundamentalInduction_cogram N x hx

theorem fundamentalTransfer_cogram (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x) :
    (fundamentalTransfer N hε ht x).comp (fundamentalTransfer N hε ht x).adjoint=
      projection N hε ht x := by
  have hi := AsymptoticFiberIsometry.adjoint_comp (classOf N)
    (fun g => fundamentalAmplitude N (g • x)) (fundamental_amplitude_hasSum N x hx)
  change (fundamentalInduction N x hx).toContinuousLinearMap.adjoint.comp
    (fundamentalInduction N x hx).toContinuousLinearMap=1 at hi
  simp only [fundamentalTransfer,dite_eq_left hx,adjoint_comp,adjoint_adjoint]
  calc
    _ = (induction N hε ht x).toContinuousLinearMap.comp
      (((fundamentalInduction N x hx).toContinuousLinearMap.adjoint.comp
        (fundamentalInduction N x hx).toContinuousLinearMap).comp
        (induction N hε ht x).toContinuousLinearMap.adjoint) := by
          simp only [comp_assoc]
    _ = projection N hε ht x := by
      rw [hi]
      exact AsymptoticIsometryRange.cogram (induction N hε ht x)

/-- Transport an actual geometric subset of the fundamental set into the
normalized quotient model. -/
def fundamentalTransport (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (s : Set ℍ) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalTransfer N hε ht x).comp (corner s x)

theorem fundamentalTransport_regular (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : MeasurableSet s) :
    (∀ g h, Measurable (fun x => matrix (fundamentalTransport N hε ht s x) g h)) ∧
      Covariant (fundamentalTransport N hε ht s) :=
  ⟨matrix_comp_measurable _ _ (fundamentalTransfer_measurable N hN hε ht)
      (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable) hs),
    covariant_comp _ _ (fundamentalTransfer_covariant N hε ht) (corner_covariant s)⟩

theorem fundamentalTransport_gram (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    {s : Set ℍ} (hs : s⊆fundamentalSet N) (x : ℍ) (hx : fundamentalGood N x) :
    (fundamentalTransport N hε ht s x).adjoint.comp (fundamentalTransport N hε ht s x)=
      corner s x := by
  simp only [fundamentalTransport,adjoint_comp,corner_adjoint]
  calc
    _ = ((corner s x).comp ((fundamentalTransfer N hε ht x).adjoint.comp
        (fundamentalTransfer N hε ht x))).comp (corner s x) := by
          simp only [comp_assoc]
    _ = corner s x := by
      rw [fundamentalTransfer_gram N hε ht x hx,corner_comp_of_subset hs,corner_idempotent]

theorem fundamentalTransport_zero (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (s : Set ℍ) (x : ℍ) (hx : ¬fundamentalGood N x) :
    fundamentalTransport N hε ht s x=0 := by
  simp only [fundamentalTransport,fundamentalTransfer,dite_eq_right hx,zero_comp]

#print axioms fundamentalTransfer_gram
#print axioms fundamentalTransfer_cogram
#print axioms fundamentalTransport_regular
#print axioms fundamentalTransport_gram

end QuantitativeSpectralObservability
