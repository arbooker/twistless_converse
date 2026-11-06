module

public import QuantitativeSpectralObservabilityFundamentalTransferV1
public import QuantitativeSpectralObservabilityFundamentalProjectionV1
public import QuantitativeSpectralObservabilityFundamentalCompactV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilitySampling
open QuantitativeSpectralCoverUnweight
open scoped lp

attribute [local instance] Classical.propDecidable

/-- The literal compact fundamental-domain samples, placed in the existing
normalized congruence quotient Hilbert space. -/
def fundamentalSampling (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalTransfer N hε ht x).comp (fundamentalRawSampling N hN H hε t x)

theorem fundamentalSampling_range (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    fundamentalSampling N hN H hε ht x v∈quotientSpace N hε ht x :=
  fundamentalTransfer_range N hε ht x _

theorem fundamentalSampling_norm (N : ℕ) (hN : 0<N) (H : ℝ) (hH : 0≤H)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖fundamentalSampling N hN H hε ht x‖≤
      samplingBound N hN H ε t*(8*coverBound N hN*(H+3)+5) := by
  apply (opNorm_comp_le _ _).trans
  exact ((mul_le_mul_of_nonneg_right (fundamentalTransfer_norm N hε ht x)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      fundamentalRawSampling_norm N hN H hH hε t x))

theorem fundamentalSampling_regular (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    (∀ g h, Measurable (fun x => matrix (fundamentalSampling N hN H hε ht x) g h)) ∧
      Covariant (fundamentalSampling N hN H hε ht) := by
  have hs := fundamentalRawSampling_regular N hN H hε t
  exact ⟨matrix_comp_measurable _ _ (fundamentalTransfer_measurable N hN hε ht) hs.1,
    covariant_comp _ _ (fundamentalTransfer_covariant N hε ht) hs.2⟩

theorem fundamentalSampling_norm_eq_raw (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) :
    ‖fundamentalSampling N hN H hε ht x v‖=‖fundamentalRawSampling N hN H hε t x v‖ := by
  have hv := congrArg (fun B : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) => B v)
    (fundamentalRawSampling_supported N hN H hε t x)
  change corner (fundamentalSet N) x (fundamentalRawSampling N hN H hε t x v)=_ at hv
  simp only [fundamentalSampling,comp_apply,fundamentalTransfer,dite_eq_left hx]
  change ‖induction N hε ht x
    ((fundamentalInduction N x hx).toContinuousLinearMap.adjoint
      (fundamentalRawSampling N hN H hε t x v))‖=_
  rw [(induction N hε ht x).norm_map]
  exact fundamentalInduction_adjoint_norm N x hx _ hv

/-- Recovering the unweighted quotient coordinate gives the original
fundamental-domain samples exactly, including their cutoff. -/
theorem fundamentalSampling_recover (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) :
    fundamentalInduction N x hx ((induction N hε ht x).toContinuousLinearMap.adjoint
      (fundamentalSampling N hN H hε ht x v))=fundamentalRawSampling N hN H hε t x v := by
  have hi := AsymptoticFiberIsometry.adjoint_comp (classOf N)
    (fun g => amplitude N ε t (g • x)) (fibre_amplitude_hasSum N hε ht x)
  change (induction N hε ht x).toContinuousLinearMap.adjoint.comp
    (induction N hε ht x).toContinuousLinearMap=1 at hi
  simp only [fundamentalSampling,comp_apply,fundamentalTransfer,dite_eq_left hx]
  change fundamentalInduction N x hx
    (((induction N hε ht x).toContinuousLinearMap.adjoint.comp
      (induction N hε ht x).toContinuousLinearMap)
        ((fundamentalInduction N x hx).toContinuousLinearMap.adjoint
          (fundamentalRawSampling N hN H hε t x v)))=_
  rw [hi]
  change ((fundamentalInduction N x hx).toContinuousLinearMap.comp
    (fundamentalInduction N x hx).toContinuousLinearMap.adjoint)
      (fundamentalRawSampling N hN H hε t x v)=_
  rw [fundamentalInduction_cogram]
  exact congrArg (fun B : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) => B v)
    (fundamentalRawSampling_supported N hN H hε t x)

#print axioms fundamentalSampling_range
#print axioms fundamentalSampling_norm
#print axioms fundamentalSampling_regular
#print axioms fundamentalSampling_norm_eq_raw
#print axioms fundamentalSampling_recover

end QuantitativeSpectralObservability
