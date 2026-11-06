module

public import QuantitativeEulerEndpointTerminalSandwichTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalTrace
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeHolomorphic
open scoped ENNReal
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- Cyclicity moves a uniform filter error onto the fixed terminal strip.
The resulting cost is its area, independently of output cutoffs. -/
theorem sandwich_trace_error (a : Algebra A P) (ha : 0≤a ∧ a≤1)
    (U T : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hT : ∀ x,‖regularSum T x‖≤1)
    (hs : ∀ x,(regularSum U x).comp (AsymptoticOrbitDiagonal.corner (terminalRegion A P) x)=regularSum U x)
    (hf : AsymptoticRegularTrace.trace volume
      (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞)
    (δ : ℝ) (he : ∀ x,‖rep A P a x-regularSum T x‖≤δ) :
    ‖signedTrace volume (fun x => (regularSum U x).comp ((regularSum T x).comp (regularSum U x).adjoint))-
      signedTrace volume (fun x => (regularSum U x).comp ((rep A P a x).comp (regularSum U x).adjoint))‖≤
        δ*(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  let V := regularSum U
  let F := regularSum T
  let R := rep A P a
  let G := fun x => (V x).adjoint.comp (V x)
  have hmV := regularSum_matrix_measurable U
  have hmF := regularSum_matrix_measurable T
  have hmR := representation_matrix_measurable _ _ _ _ _ a
  have hmG := matrix_comp_measurable (fun x => (V x).adjoint) V (matrix_adjoint_measurable V hmV) hmV
  have hnR (x) : ‖R x‖≤1 :=
    (representation_norm_le _ _ _ _ _ a x).trans ((CStarAlgebra.norm_le_one_iff_of_nonneg a ha.1).mpr ha.2)
  have hnG (x) : ‖G x‖≤1 := contraction_gram_norm_le (V x) (hU x)
  have hn (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) (hB : ∀ x,‖B x‖≤1) (x) :
      ‖(B x).comp (G x)‖≤1 :=
    (opNorm_comp_le _ _).trans ((mul_le_mul (hB x) (hnG x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hp (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) (x) :
      ((B x).comp (G x)).comp (AsymptoticOrbitDiagonal.corner (terminalRegion A P) x)=(B x).comp (G x) := by
    dsimp only [G,V]
    simp only [comp_assoc,hs x]
  have hd (x) : ‖(F x).comp (G x)-(R x).comp (G x)‖≤δ := by
    rw [←sub_comp]
    apply (opNorm_comp_le _ _).trans
    have hh : ‖F x-R x‖≤δ := by simpa only [norm_sub_rev] using he x
    exact (mul_le_mul_of_nonneg_left (hnG x) (norm_nonneg _)).trans (by simpa using hh)
  have hh := norm_signedTrace_sub_le_corner measure (terminal_measurable A P) (terminal_finite A P)
    (fun x => (F x).comp (G x)) (fun x => (R x).comp (G x))
    (matrix_comp_measurable F G hmF hmG 1 1) (matrix_comp_measurable R G hmR hmG 1 1)
    (hn F hT) (hn R hnR) (hp F) (hp R) hd
  rw [terminal_area,ENNReal.toReal_ofReal (inv_nonneg.mpr
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le)] at hh
  rw [signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving V F hmV hmF
    (regularSum_covariant U) (regularSum_covariant T) hf hT,
    signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving V R hmV hmR
    (regularSum_covariant U) (representation_covariant _ _ _ _ _ a) hf hnR]
  exact hh

/-- A positive finite filter close to an exact terminal contraction has
retained reconstructed trace bounded by the exact trace plus terminal-area error. -/
theorem retained_sandwich_le_trace (a : Algebra A P) (ha : 0≤a ∧ a≤1)
    (U T : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hT : ∀ x,0≤regularSum T x ∧ regularSum T x≤1)
    (hs : ∀ x,(regularSum U x).comp (AsymptoticOrbitDiagonal.corner (terminalRegion A P) x)=regularSum U x)
    (hf : AsymptoticRegularTrace.trace volume
      (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞)
    (δ : ℝ) (he : ∀ x,‖rep A P a x-regularSum T x‖≤δ) (Y H : ℝ) :
    signedTrace volume (regularRetained Y H
      (fun x => (regularSum U x).comp ((regularSum T x).comp (regularSum U x).adjoint)))≤
      tr A P a+δ*(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  let V := regularSum U
  let F := regularSum T
  have hn (x) : ‖F x‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hT x).1).mpr (hT x).2
  have hmV := regularSum_matrix_measurable U
  have hmF := regularSum_matrix_measurable T
  have hm := matrix_comp_measurable V _ hmV
    (matrix_comp_measurable F _ hmF (matrix_adjoint_measurable V hmV))
  have hp (x) : ((V x).comp ((F x).comp (V x).adjoint)).IsPositive := by
    simpa only [adjoint_adjoint] using (nonneg_iff_isPositive.mp (hT x).1).adjoint_conj (V x).adjoint
  have hfin : AsymptoticRegularTrace.trace volume (fun x => (V x).comp ((F x).comp (V x).adjoint))<∞ := by
    apply (trace_sandwich_le_range_gram volume V F hn).trans_lt
    rw [←trace_adjoint_mul AsymptoticRationalGroup.measurePreserving V hmV (regularSum_covariant U)]
    exact hf
  have hcut := regularRetained_trace_le_full Y H _ hm hp hfin
  have herr := sandwich_trace_error A P a ha U T hU hn hs hf δ he
  have hbound := positive_sandwich_le_trace A P a ha.1 U hU
  have herr' := (le_abs_self _).trans (show |(_ : ℝ)|≤_ from herr)
  linarith

#print axioms sandwich_trace_error
#print axioms retained_sandwich_le_trace
end QuantitativeEulerEndpointTerminalTrace
