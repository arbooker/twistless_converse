module

public import QuantitativeSpectralObservabilityFundamentalFiberV1
public import AsymptoticCongruenceProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceWeight
open AsymptoticRegularTrace
open scoped lp ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Transfer the single fundamental-set coordinate in each fibre into
the existing normalized quotient realization. Boundary roots are set to
zero on a proved invariant null set. -/
def fundamentalTransfer (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  if hx : fundamentalGood N x then
    (induction N hε ht x).toContinuousLinearMap.comp
      (fundamentalInduction N x hx).toContinuousLinearMap.adjoint
  else 0

theorem fundamentalTransfer_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ‖fundamentalTransfer N hε ht x‖≤1 := by
  unfold fundamentalTransfer
  split_ifs
  · apply (opNorm_comp_le _ _).trans
    rw [adjoint.norm_map]
    have h₁ := (induction N hε ht x).norm_toContinuousLinearMap_le
    have h₂ := (fundamentalInduction N x ‹fundamentalGood N x›).norm_toContinuousLinearMap_le
    simpa only [one_mul] using mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one
  · simp

theorem fundamentalTransfer_range (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    fundamentalTransfer N hε ht x v∈quotientSpace N hε ht x := by
  unfold fundamentalTransfer
  split_ifs with hx
  · exact ⟨(fundamentalInduction N x hx).toContinuousLinearMap.adjoint v,rfl⟩
  · exact (quotientSpace N hε ht x).zero_mem

theorem fundamentalTransfer_matrix (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (g h : OrbitGroup) :
    matrix (fundamentalTransfer N hε ht x) g h =
      if fundamentalGood N x then
        if classOf N g=classOf N h then
          amplitude N ε t (g • x)*conj (fundamentalAmplitude N (h • x)) else 0
      else 0 := by
  classical
  by_cases hx : fundamentalGood N x
  · rw [fundamentalTransfer,dite_eq_left hx,ite_eq_left hx,AsymptoticRegularTrace.matrix,comp_apply]
    have hd := AsymptoticFiberIsometry.adjoint_delta (classOf N)
      (fun a => fundamentalAmplitude N (a • x)) (fundamental_amplitude_hasSum N x hx) h
    change (fundamentalInduction N x hx).toContinuousLinearMap.adjoint (delta h)=
      conj (fundamentalAmplitude N (h • x)) • delta (classOf N h) at hd
    rw [hd]
    change amplitude N ε t (g • x)*
      (conj (fundamentalAmplitude N (h • x))*delta (classOf N h) (classOf N g))=_
    by_cases he : classOf N g=classOf N h
    · simp [delta,he]
    · simp [delta,he]
  · simp only [fundamentalTransfer,dite_eq_right hx,ite_eq_right hx]
    rfl

theorem fundamentalAmplitude_measurable (N : ℕ) (hN : 0<N) :
    Measurable (fundamentalAmplitude N) :=
  measurable_const.indicator (fundamentalSet_measurable N hN)

theorem fundamentalTransfer_measurable (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (g h : OrbitGroup) :
    Measurable (fun x => matrix (fundamentalTransfer N hε ht x) g h) := by
  simp only [fundamentalTransfer_matrix]
  apply Measurable.ite (fundamentalGood_measurable N hN) _ measurable_const
  split_ifs
  · exact ((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((fundamentalAmplitude_measurable N hN).comp
        (AsymptoticRationalGroup.measurePreserving h).measurable))
  · exact measurable_const

theorem fundamentalTransfer_covariant (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) : Covariant (fundamentalTransfer N hε ht) := by
  intro x b g h
  simp only [fundamentalTransfer_matrix,classOf_right_iff,mul_smul,fundamentalGood_smul_iff]

#print axioms fundamentalTransfer_norm
#print axioms fundamentalTransfer_range
#print axioms fundamentalTransfer_matrix
#print axioms fundamentalTransfer_covariant

end QuantitativeSpectralObservability
