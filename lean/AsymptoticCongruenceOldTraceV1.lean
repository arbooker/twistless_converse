module

public import AsymptoticCongruenceOldSpaceV1
public import AsymptoticCongruenceTraceFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticCongruenceQuotient
open AsymptoticRegularTrace
open scoped lp ComplexConjugate Classical ENNReal

variable (N : ℕ) (J : Subgroup AsymptoticRationalGroup.Group) (hJ : gamma N≤J)
variable [Finite (J ⧸ (gamma N).subgroupOf J)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

theorem projection_diagonal (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    (matrix (space N J hJ hε ht z).starProjection g g).re=
      (matrix (AsymptoticCongruenceQuotient.projection N hε ht z) g g).re*
        (((gamma N).subgroupOf J).index:ℝ)⁻¹ := by
  rw [projection_matrix,AsymptoticCongruenceQuotient.projection_matrix]
  simp [Complex.mul_conj,Complex.mul_re]

theorem projection_matrix_measurable (g k : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (space N J hJ hε ht z).starProjection g k) := by
  simp only [projection_matrix]
  split_ifs
  · exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
        (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
          (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · exact measurable_const

theorem projection_covariant : Covariant (fun z => (space N J hJ hε ht z).starProjection) := by
  intro z a g k
  simp only [projection_matrix,mul_smul]
  have he : AsymptoticNestedQuotients.classOf J (g*a)=AsymptoticNestedQuotients.classOf J (k*a) ↔
      AsymptoticNestedQuotients.classOf J g=AsymptoticNestedQuotients.classOf J k := by
    simp only [AsymptoticNestedQuotients.classOf,Quotient.eq_iff_equiv,QuotientGroup.rightRel_apply,
      mul_inv_rev,mul_assoc,mul_inv_cancel_left]
  by_cases hk : AsymptoticNestedQuotients.classOf J g=AsymptoticNestedQuotients.classOf J k
  · simp only [ite_eq_left hk,ite_eq_left (he.mpr hk)]
  · simp only [ite_eq_right hk,ite_eq_right (not_congr he |>.mpr hk)]

/-- The local averaging projection has the reciprocal-index fraction of
the actual congruence quotient trace. This identity is proved in the
strip model and does not assume a quotient trace formula. -/
theorem projection_trace : trace volume (fun z => (space N J hJ hε ht z).starProjection)=
    ENNReal.ofReal ((((gamma N).subgroupOf J).index:ℝ)⁻¹)*
      trace volume (AsymptoticCongruenceQuotient.projection N hε ht) := by
  simp only [trace,projection_diagonal]
  simp_rw [mul_comm _ ((((gamma N).subgroupOf J).index:ℝ)⁻¹),
    ENNReal.ofReal_mul (by positivity : 0≤(((gamma N).subgroupOf J).index:ℝ)⁻¹)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem projection_trace_toReal :
    (trace volume (fun z => (space N J hJ hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal/
        (((gamma N).subgroupOf J).index:ℝ) := by
  rw [projection_trace,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  exact mul_comm _ _

theorem projection_trace_finite (hN : 0<N) :
    trace volume (fun z => (space N J hJ hε ht z).starProjection)<∞ :=
  projection_trace_finite_of_le volume (space N J hJ hε ht) (quotientSpace N hε ht)
    (space_le_quotient N J hJ hε ht) (AsymptoticCongruenceQuotient.projection_trace_finite N hN hε ht)

#print axioms projection_diagonal
#print axioms projection_matrix_measurable
#print axioms projection_covariant
#print axioms projection_trace
#print axioms projection_trace_toReal
#print axioms projection_trace_finite

end AsymptoticCongruenceOldSpace
