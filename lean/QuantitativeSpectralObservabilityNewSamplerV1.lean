module

public import QuantitativeNewGapIndexedV1
public import QuantitativeSpectralObservabilityOldTailRowsV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticPolarIsometry AsymptoticQuotientOperators
open QuantitativeNewGap
open scoped lp

theorem totalNew_equivariant (N : ℕ) (hN : 0<N) :
    Equivariant (AsymptoticTotalNewCorner.space N hN).starProjection := by
  rw [starProjection_congr _ _ (totalNewSpace_eq_jointList N hN)]
  intro a
  exact invariant_jointListSpace _ _
    (fun p => AsymptoticTotalNewCorner.localSpace_equivariant N hN p a) _

theorem totalNew_projection_regular (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix
      (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection g k)) ∧
    Covariant (fun x => (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection) := by
  simp only [AsymptoticTotalNewCorner.stripSpace_projection,compression_matrix]
  constructor
  · intro g k
    exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
        (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · intro x a g k
    simp only [compression_matrix,mul_smul]
    have he := totalNew_equivariant N hN a
      (AsymptoticNestedQuotients.classOf (gamma N) g)
      (AsymptoticNestedQuotients.classOf (gamma N) k)
    simp only [AsymptoticNestedQuotients.rightMulEquiv_classOf] at he
    exact congrArg (fun z : ℂ =>
      (amplitude N ε t (g • a • x)*star (amplitude N ε t (k • a • x)))*z) he.symm

/-- The actual fundamental sampler followed by the literal all-prime new projection. -/
def newSampling (N : ℕ) (hN : 0<N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection.comp
    (fundamentalSampling N hN Y hε ht x)

theorem newSampling_mem (N : ℕ) (hN : 0<N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    newSampling N hN Y hε ht x v∈AsymptoticTotalNewCorner.stripSpace N hN hε ht x :=
  Submodule.starProjection_apply_mem _ _

theorem newSampling_norm (N : ℕ) (hN : 0<N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖newSampling N hN Y hε ht x‖≤‖fundamentalSampling N hN Y hε ht x‖ := by
  calc
    _ ≤ ‖(AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection‖*
        ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
      mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
    _ = _ := one_mul _

theorem newSampling_regular (N : ℕ) (hN : 0<N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (newSampling N hN Y hε ht x) g k)) ∧
      Covariant (newSampling N hN Y hε ht) := by
  have hp := totalNew_projection_regular N hN hε ht
  have hs := fundamentalSampling_regular N hN Y hε ht
  exact ⟨matrix_comp_measurable _ _ hp.1 hs.1,covariant_comp _ _ hp.2 hs.2⟩

/-- Pythagoras replaces an observed sample by its projection when the discarded
part is controlled by the same detector. -/
theorem observability_projected {ι : Type*} (V : Submodule ℂ ℓ²(ι,ℂ))
    [CompleteSpace V] (f a : ℓ²(ι,ℂ)) (d K A : ℝ) (hK : 0≤K) (hA : 0≤A)
    (hobs : ‖f‖^2≤K*(d^2+‖a‖^2))
    (hgap : ‖a-V.starProjection a‖^2≤A*d^2) :
    ‖f‖^2≤K*(1+A)*(d^2+‖V.starProjection a‖^2) := by
  have he := Submodule.norm_sq_eq_add_norm_sq_starProjection a V
  rw [Submodule.starProjection_orthogonal_val] at he
  have hp : 0≤A*‖V.starProjection a‖^2 := mul_nonneg hA (sq_nonneg _)
  apply hobs.trans
  calc
    _ ≤ K*((1+A)*(d^2+‖V.starProjection a‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ hK
      nlinarith only [he,hgap,hp]
    _ = _ := by ring

#print axioms totalNew_equivariant
#print axioms totalNew_projection_regular
#print axioms newSampling_regular
#print axioms observability_projected

end QuantitativeSpectralObservability
