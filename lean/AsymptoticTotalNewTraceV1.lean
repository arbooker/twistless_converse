module

public import AsymptoticTotalNewCornerV1
public import AsymptoticIncidenceSumTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticTotalNewCorner

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticPolarIsometry AsymptoticSectorSigns ContinuousLinearMap
open scoped lp ENNReal

variable (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

noncomputable def stripInduction (x : ℍ) : space N hN →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (AsymptoticCongruenceQuotient.induction N hε ht x).comp (space N hN).subtypeₗᵢ

noncomputable def stripSpace (x : ℍ) : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (stripInduction N hN hε ht x).toLinearMap.range

noncomputable instance stripSpace_complete (x : ℍ) : CompleteSpace (stripSpace N hN hε ht x) :=
  AsymptoticIsometryRange.range_complete (stripInduction N hN hε ht x)

theorem stripSpace_le_quotient (x : ℍ) :
    stripSpace N hN hε ht x≤AsymptoticCongruenceQuotient.quotientSpace N hε ht x := by
  rintro v ⟨f,rfl⟩
  exact ⟨f.val,rfl⟩

theorem incidence_le_stripSpace (e : Sector N) (x : ℍ) :
    AsymptoticQuotientIncidence.space N hN hε ht e x≤stripSpace N hN hε ht x := by
  intro v hv
  have hq := ((AsymptoticQuotientIncidence.space_mem N hN hε ht e x v).mp hv).1
  obtain ⟨f,rfl⟩ := hq
  exact ⟨⟨f,incidence_induction_mem N hN hε ht e x f hv⟩,rfl⟩

theorem stripSpace_projection (x : ℍ) :
    (stripSpace N hN hε ht x).starProjection=
      AsymptoticCongruenceQuotient.compression N hε ht (space N hN).starProjection x := by
  have hh := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht x) (space N hN).subtypeₗᵢ
  have hr : (space N hN).subtypeₗᵢ.toLinearMap.range=space N hN := Submodule.range_subtype _
  rw [starProjection_congr _ _ hr] at hh
  exact hh

theorem stripSpace_trace_finite :
    trace volume (fun x => (stripSpace N hN hε ht x).starProjection)<∞ :=
  projection_trace_finite_of_le volume (stripSpace N hN hε ht)
    (AsymptoticCongruenceQuotient.quotientSpace N hε ht) (stripSpace_le_quotient N hN hε ht)
    (AsymptoticCongruenceQuotient.projection_trace_finite N hN hε ht)

theorem totalTrace_le_stripSpace :
    AsymptoticQuotientIncidence.totalTrace N hN hε ht≤
      (trace volume (fun x => (stripSpace N hN hε ht x).starProjection)).toReal :=
  AsymptoticQuotientIncidence.totalTrace_le_common N hN hε ht (stripSpace N hN hε ht)
    (incidence_le_stripSpace N hN hε ht) (stripSpace_trace_finite N hN hε ht)

/-- The coefficient obtained from the actual local new projections.
Its local factors have separately proved numerical formulas. It depends
only on the level, not on the strip weights or sector. -/
noncomputable def coefficient : ℝ :=
  ((gamma N).relIndex (gamma 1):ℝ)/12*
    ((N.primeFactors.toList).map (fun p =>
      (matrix (localSpace N hN p).starProjection (AsymptoticNestedQuotients.classOf (gamma N) 1)
        (AsymptoticNestedQuotients.classOf (gamma N) 1)).re)).prod

/-- The summed incidence trace is bounded by the total local new
coefficient. All sector orthogonality, prime-product separation and
quotient-covolume hypotheses have been discharged. -/
theorem totalTrace_le_coefficient :
    AsymptoticQuotientIncidence.totalTrace N hN hε ht≤4*Real.pi*coefficient N hN := by
  apply (totalTrace_le_stripSpace N hN hε ht).trans
  have hr : 0≤(matrix (space N hN).starProjection
      (AsymptoticCongruenceQuotient.classOf N 1) (AsymptoticCongruenceQuotient.classOf N 1)).re := by
    rw [AsymptoticQuotientOperators.projection_diagonal,Complex.ofReal_re]
    positivity
  simp_rw [stripSpace_projection N hN hε ht]
  rw [AsymptoticCongruenceQuotient.compression_trace N hε ht _ hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,AsymptoticCongruenceQuotient.projection_trace_covolume_toReal N hN hε ht]
  have hh := mul_le_mul_of_nonneg_right (diagonal_le_product N hN)
    (show 0≤((gamma N).relIndex (gamma 1):ℝ)*(Real.pi/3) by positivity)
  convert hh using 1
  · rfl
  · unfold coefficient
    ring

#print axioms stripSpace_le_quotient
#print axioms incidence_le_stripSpace
#print axioms stripSpace_projection
#print axioms stripSpace_trace_finite
#print axioms totalTrace_le_stripSpace
#print axioms totalTrace_le_coefficient

end AsymptoticTotalNewCorner
