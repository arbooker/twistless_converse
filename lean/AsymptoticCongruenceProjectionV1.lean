module

public import AsymptoticCongruenceQuotientV1
public import AsymptoticFiberProjectionV1
public import AsymptoticProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceWeight AsymptoticRegularTrace
open scoped lp ComplexConjugate Classical ENNReal

noncomputable def quotientSpace (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (induction N hε ht z).toLinearMap.range

noncomputable instance quotientSpace_complete (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (z : ℍ) : CompleteSpace (quotientSpace N hε ht z) :=
  AsymptoticFiberIsometry.range_complete (classOf N) (fun g => amplitude N ε t (g • z))
    (fibre_amplitude_hasSum N hε ht z)

/-- The orthogonal projection onto the induced quotient Hilbert space. -/
noncomputable def projection (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (quotientSpace N hε ht z).starProjection

theorem projection_matrix (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (g h : AsymptoticRationalGroup.Group) :
    matrix (projection N hε ht z) g h=
      if classOf N g=classOf N h then amplitude N ε t (g • z)*conj (amplitude N ε t (h • z))
      else 0 := by
  have he := (congrArg (fun T : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ) => T (delta h) g)
      (AsymptoticFiberIsometry.operator_cogram (classOf N)
        (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z))).symm.trans
    (AsymptoticFiberIsometry.projection_apply_delta (classOf N)
      (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z) g h)
  have hr : (AsymptoticFiberIsometry.operator (classOf N)
      (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z)).range=
      quotientSpace N hε ht z := by
    ext v
    rfl
  have congr_projection (U V : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ))
      [CompleteSpace U] [CompleteSpace V] (hUV : U=V) : U.starProjection=V.starProjection := by
    subst V
    rfl
  rw [congr_projection _ _ hr] at he
  by_cases hh : classOf N g=classOf N h
  · simpa only [ite_eq_left hh,matrix,projection] using he
  · simpa only [ite_eq_right hh,matrix,projection] using he

theorem projection_diagonal (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (g : AsymptoticRationalGroup.Group) :
    (matrix (projection N hε ht z) g g).re=
      AsymptoticMassTransport.strip.indicator (fun w => AsymptoticCompactBranch.cap ε t w^2)
        (g • z)/weight N ε t (g • z) := by
  rw [projection_matrix,ite_eq_left rfl,Complex.mul_conj,Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  simpa only [OneMemClass.coe_one,one_smul] using amplitude_norm_sq N hε ht 1 (g • z)

theorem projection_matrix_measurable (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (projection N hε ht z) g h) := by
  simp only [projection_matrix]
  split_ifs
  · exact ((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
        (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
          (AsymptoticRationalGroup.measurePreserving h).measurable))
  · exact measurable_const

theorem classOf_right_iff (N : ℕ) (g h a : AsymptoticRationalGroup.Group) :
    classOf N (g*a)=classOf N (h*a) ↔ classOf N g=classOf N h := by
  simp only [classOf,Quotient.eq_iff_equiv,QuotientGroup.rightRel_apply,
    mul_inv_rev,mul_assoc,mul_inv_cancel_left]

theorem projection_covariant (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    Covariant (projection N hε ht) := by
  intro x a g h
  simp only [projection_matrix,classOf_right_iff,mul_smul]

/-- The rooted diagonal has the manuscript's exact weight ratio.
Evaluating this integral as a congruence covolume is a separate step. -/
theorem projection_trace (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    trace volume (projection N hε ht)=
      ∫⁻ z : ℍ,ENNReal.ofReal
        (AsymptoticMassTransport.strip.indicator
          (fun w => AsymptoticCompactBranch.cap ε t w^2) z/weight N ε t z) := by
  simp only [trace,projection_diagonal,one_smul]

#print axioms projection_matrix
#print axioms projection_diagonal
#print axioms projection_matrix_measurable
#print axioms classOf_right_iff
#print axioms projection_covariant
#print axioms projection_trace

end AsymptoticCongruenceQuotient
