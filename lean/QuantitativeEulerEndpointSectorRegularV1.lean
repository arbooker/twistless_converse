module

public import QuantitativeEulerEndpointSectorSignCoordinatesV1
public import QuantitativeSpectralObservabilityNewSamplerV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticQuotientOperators AsymptoticPermutationInvariant
open QuantitativeNewGap QuantitativeSpectralObservability
open scoped lp Classical

theorem sectorSignRow_apply (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N)
    (f : ℓ²(Classes N,ℂ)) (g : OrbitGroup) :
    sectorSignRow N hN sector i f (classOf N g)=
      f (classOf N (sectorLabel N hN i*g))-(sectorNormalizerSign sector i:ℂ)*f (classOf N g) := by
  cases i <;> rfl

theorem sectorSignRow_matrix (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N)
    (g k : OrbitGroup) :
    matrix (sectorSignRow N hN sector i) (classOf N g) (classOf N k)=
      (if classOf N (sectorLabel N hN i*g)=classOf N k then 1 else 0)-
      (sectorNormalizerSign sector i:ℂ)*(if classOf N g=classOf N k then 1 else 0) := by
  rw [matrix,sectorSignRow_apply]
  simp [AsymptoticRegularTrace.delta,lp.single_apply,Pi.single_apply,eq_comm]

theorem weightedSectorSignRow_norm (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (i : SectorSignIndex N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖weightedSectorSignRow N hN sector i hε ht x‖≤‖sectorSignRow N hN sector i‖ := by
  let J := (induction N hε ht x).toContinuousLinearMap
  have hJ : ‖J‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    change ‖induction N hε ht x f‖≤1*‖f‖
    rw [(induction N hε ht x).norm_map,one_mul]
  have ha : ‖J.adjoint‖≤1 := by simpa only [adjoint.norm_map] using hJ
  change ‖(J.comp (sectorSignRow N hN sector i)).comp J.adjoint‖≤_
  calc
    _ ≤ (‖J‖*‖sectorSignRow N hN sector i‖)*‖J.adjoint‖ :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*‖sectorSignRow N hN sector i‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)) ha (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weightedSectorSignRow_regular (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (i : SectorSignIndex N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (weightedSectorSignRow N hN sector i hε ht x) g k)) ∧
      Covariant (weightedSectorSignRow N hN sector i hε ht) := by
  constructor
  · intro g k
    simp only [weightedSectorSignRow,compression_matrix]
    exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
        (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · intro x a g k
    simp only [weightedSectorSignRow,compression_matrix,mul_smul,sectorSignRow_matrix]
    have he (g' k' : OrbitGroup) : classOf N (g'*a)=classOf N (k'*a) ↔
        classOf N g'=classOf N k' := by
      change AsymptoticNestedQuotients.classOf (gamma N) (g'*a)=
        AsymptoticNestedQuotients.classOf (gamma N) (k'*a) ↔
        AsymptoticNestedQuotients.classOf (gamma N) g'=
        AsymptoticNestedQuotients.classOf (gamma N) k'
      simp only [AsymptoticNestedQuotients.classOf_eq_iff,mul_inv_rev,mul_assoc,mul_inv_cancel_left]
    rw [← mul_assoc (sectorLabel N hN i) g a]
    simp only [he]
theorem sectorSignRow_equivariant (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) :
    Equivariant (sectorSignRow N hN sector i) := by
  classical
  intro a q r
  induction q using Quotient.inductionOn with
  | h g =>
    induction r using Quotient.inductionOn with
    | h k =>
      change matrix (sectorSignRow N hN sector i) (classOf N (g*a)) (classOf N (k*a))=
        matrix (sectorSignRow N hN sector i) (classOf N g) (classOf N k)
      simp only [sectorSignRow_matrix]
      have he (g' k' : OrbitGroup) : classOf N (g'*a)=classOf N (k'*a) ↔
          classOf N g'=classOf N k' := by
        change AsymptoticNestedQuotients.classOf (gamma N) (g'*a)=
          AsymptoticNestedQuotients.classOf (gamma N) (k'*a) ↔
          AsymptoticNestedQuotients.classOf (gamma N) g'=
          AsymptoticNestedQuotients.classOf (gamma N) k'
        simp only [AsymptoticNestedQuotients.classOf_eq_iff,mul_inv_rev,mul_assoc,mul_inv_cancel_left]
      rw [← mul_assoc (sectorLabel N hN i) g a]
      exact congrArg₂ (fun z w : ℂ => z-(sectorNormalizerSign sector i:ℂ)*w)
        (if_congr (he (sectorLabel N hN i*g) k) rfl rfl)
        (if_congr (he g k) rfl rfl)

theorem countingSector_equivariant (N : ℕ) (hN : 0<N) (sector : Sector N) :
    Equivariant (countingSectorSpace N hN sector).starProjection := by
  intro a
  apply invariant_inter
  · exact totalNew_equivariant N hN a
  · apply invariant_jointListSpace
    intro i
    exact invariant_kernel _ (sectorSignRow N hN sector i) (sectorSignRow_equivariant N hN sector i a)

theorem incidence_projection_regular (N : ℕ) (hN : 0<N) (sector : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix
      (AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection g k)) ∧
      Covariant (fun x => (AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection) := by
  simp only [incidence_projection_compression,compression_matrix]
  constructor
  · intro g k
    exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
        (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · intro x a g k
    simp only [compression_matrix,mul_smul]
    have he := countingSector_equivariant N hN sector a
      (AsymptoticNestedQuotients.classOf (gamma N) g)
      (AsymptoticNestedQuotients.classOf (gamma N) k)
    simp only [AsymptoticNestedQuotients.rightMulEquiv_classOf] at he
    exact congrArg (fun z : ℂ =>
      (amplitude N ε t (g • a • x)*star (amplitude N ε t (k • a • x)))*z) he.symm

#print axioms weightedSectorSignRow_regular
#print axioms incidence_projection_regular
end QuantitativeEulerEndpointPrepared
