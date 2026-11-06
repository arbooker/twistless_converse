module

public import QuantitativeEulerEndpointActualFiniteSectorComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalTrace
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointTerminalAlgebra
open scoped ENNReal

/-- A contractive covariant left factor cannot increase the finite trace
of a positive Gram. Both signed traces are actual finite positive traces. -/
theorem contraction_gram_trace (U V : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (hU : ∀ g h,Measurable (fun x => matrix (U x) g h))
    (hV : ∀ g h,Measurable (fun x => matrix (V x) g h))
    (hcU : Covariant U) (hcV : Covariant V) (hn : ∀ x,‖U x‖≤1)
    (hf : AsymptoticRegularTrace.trace volume (fun x => (V x).adjoint.comp (V x))<∞) :
    signedTrace volume (fun x => ((U x).comp (V x)).comp ((U x).comp (V x)).adjoint)≤
      signedTrace volume (fun x => (V x).adjoint.comp (V x)) := by
  let B := fun x => (U x).comp (V x)
  have hm := matrix_comp_measurable U V hU hV
  have hc := covariant_comp U V hcU hcV
  have hb := trace_gram_comp_le volume U V hn
  have he := trace_adjoint_mul AsymptoticRationalGroup.measurePreserving B hm hc
  have hl : AsymptoticRegularTrace.trace volume (fun x => (B x).comp (B x).adjoint)≤
      AsymptoticRegularTrace.trace volume (fun x => (V x).adjoint.comp (V x)) := by
    rw [←he]
    exact hb
  rw [signedTrace_eq_toReal volume _
    (matrix_comp_measurable B (fun x => (B x).adjoint) hm (matrix_adjoint_measurable B hm) 1 1)
    (fun x => by simpa only [adjoint_adjoint] using isPositive_adjoint_comp_self (B x).adjoint),
    signedTrace_eq_toReal volume _
      (matrix_comp_measurable (fun x => (V x).adjoint) V (matrix_adjoint_measurable V hV) hV 1 1)
      (fun x => isPositive_adjoint_comp_self (V x))]
  exact ENNReal.toReal_mono hf.ne hl

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem rep_trace_finite (a : Algebra A P) : AsymptoticRegularTrace.trace measure (rep A P a)<∞ :=
  AsymptoticHyperbolicArea.closed_terminal_trace_finite (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    (rep A P a) (representation_norm_le _ _ _ _ _ a) (representation_supported _ _ _ _ _ a)

/-- Exact positive terminal elements remain trace-dominated after arbitrary
contractive finite reconstruction. No pointwise order of products is used. -/
theorem positive_sandwich_le_trace (a : Algebra A P) (ha : 0≤a) (U : Expression)
    (hU : ∀ x,‖regularSum U x‖≤1) :
    signedTrace volume (fun x => (regularSum U x).comp ((rep A P a x).comp (regularSum U x).adjoint))≤tr A P a := by
  let b := CFC.sqrt a
  have hb : star b*b=a := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,CFC.sqrt_mul_sqrt_self a ha]
  have hb' : b*star b=a := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,CFC.sqrt_mul_sqrt_self a ha]
  have hgram (x) : (rep A P b x).adjoint.comp (rep A P b x)=rep A P a x := by
    change rep A P (star b*b) x=rep A P a x
    rw [hb]
  have hrange (x) : (rep A P b x).comp (rep A P b x).adjoint=rep A P a x := by
    change rep A P (b*star b) x=rep A P a x
    rw [hb']
  have hf : AsymptoticRegularTrace.trace measure (fun x => (rep A P b x).adjoint.comp (rep A P b x))<∞ := by
    simp only [hgram]
    exact rep_trace_finite A P a
  have hh := contraction_gram_trace (regularSum U) (rep A P b)
    (QuantitativeHolomorphic.regularSum_matrix_measurable U)
    (representation_matrix_measurable _ _ _ _ _ b)
    (QuantitativeHolomorphic.regularSum_covariant U) (representation_covariant _ _ _ _ _ b) hU hf
  simp only [adjoint_comp,←comp_assoc] at hh
  have he (x) : ((regularSum U x).comp (rep A P b x)).comp
      ((rep A P b x).adjoint.comp (regularSum U x).adjoint)=
      (regularSum U x).comp ((rep A P a x).comp (regularSum U x).adjoint) := by
    simp only [comp_assoc,←hrange x]
  change signedTrace volume (fun x => ((regularSum U x).comp (rep A P b x)).comp
      ((rep A P b x).adjoint.comp (regularSum U x).adjoint))≤_ at hh
  change signedTrace (volume : Measure UpperHalfPlane) _ ≤ signedTrace measure (rep A P a)
  simpa only [he,hgram,QuantitativeEulerEndpointRegularBase.measure] using hh

#print axioms contraction_gram_trace
#print axioms rep_trace_finite
#print axioms positive_sandwich_le_trace
end QuantitativeEulerEndpointTerminalTrace
