module

public import QuantitativeNewGapSignedWeightedV1
public import QuantitativeSpectralObservabilityNewSamplerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticQuotientOperators AsymptoticPermutationInvariant
open QuantitativeNewGap QuantitativeSpectralObservability
open scoped lp

theorem countingRow_equivariant (N : ℕ) (hN : 0<N) (s : ℝ) :
    Equivariant (countingRow N hN s) := by
  classical
  intro a q r
  induction q using Quotient.inductionOn with
  | h g =>
    induction r using Quotient.inductionOn with
    | h k =>
      change matrix (countingRow N hN s) (classOf N (g*a)) (classOf N (k*a))=
        matrix (countingRow N hN s) (classOf N g) (classOf N k)
      simp only [countingRow_matrix]
      have he (g' k' : OrbitGroup) : classOf N (g'*a)=classOf N (k'*a) ↔
          classOf N g'=classOf N k' := by
        change AsymptoticNestedQuotients.classOf (gamma N) (g'*a)=
          AsymptoticNestedQuotients.classOf (gamma N) (k'*a) ↔
          AsymptoticNestedQuotients.classOf (gamma N) g'=
          AsymptoticNestedQuotients.classOf (gamma N) k'
        simp only [AsymptoticNestedQuotients.classOf_eq_iff,mul_inv_rev,mul_assoc,mul_inv_cancel_left]
      rw [← mul_assoc (AsymptoticFreshMatrices.frickeLabel N hN) g a]
      exact congrArg₂ (fun z w : ℂ => z-(s:ℂ)*w)
        (if_congr (he (AsymptoticFreshMatrices.frickeLabel N hN*g) k) rfl rfl)
        (if_congr (he g k) rfl rfl)

theorem signedNew_equivariant (N : ℕ) (hN : 0<N) (s : ℝ) :
    Equivariant (signedNewSpace N hN s).starProjection := by
  intro a
  apply invariant_inter
  · exact totalNew_equivariant N hN a
  · exact invariant_kernel _ (countingRow N hN s) (countingRow_equivariant N hN s a)

theorem signedNew_projection_regular (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (signedNewStripSpace N hN s hε ht x).starProjection g k)) ∧
      Covariant (fun x => (signedNewStripSpace N hN s hε ht x).starProjection) := by
  simp only [signedNewStripSpace_projection,compression_matrix]
  constructor
  · intro g k
    exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
        (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · intro x a g k
    simp only [compression_matrix,mul_smul]
    have he := signedNew_equivariant N hN s a
      (AsymptoticNestedQuotients.classOf (gamma N) g)
      (AsymptoticNestedQuotients.classOf (gamma N) k)
    simp only [AsymptoticNestedQuotients.rightMulEquiv_classOf] at he
    exact congrArg (fun z : ℂ =>
      (amplitude N ε t (g • a • x)*star (amplitude N ε t (k • a • x)))*z) he.symm

def signedSampling (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (signedNewStripSpace N hN s hε ht x).starProjection.comp
    (fundamentalSampling N hN Y hε ht x)

theorem signedSampling_mem (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    signedSampling N hN s Y hε ht x v∈signedNewStripSpace N hN s hε ht x :=
  Submodule.starProjection_apply_mem _ _

theorem signedSampling_norm (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖signedSampling N hN s Y hε ht x‖≤‖fundamentalSampling N hN Y hε ht x‖ := by
  calc
    _ ≤ ‖(signedNewStripSpace N hN s hε ht x).starProjection‖*
        ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
      mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
    _ = _ := one_mul _

theorem signedSampling_regular (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (signedSampling N hN s Y hε ht x) g k)) ∧
      Covariant (signedSampling N hN s Y hε ht) := by
  have hp := signedNew_projection_regular N hN s hε ht
  have hs := fundamentalSampling_regular N hN Y hε ht
  exact ⟨matrix_comp_measurable _ _ hp.1 hs.1,covariant_comp _ _ hp.2 hs.2⟩

#print axioms countingRow_equivariant
#print axioms signedNew_projection_regular
#print axioms signedSampling_regular

end QuantitativeSpectralExceptionalFricke
