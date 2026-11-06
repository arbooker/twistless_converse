module

public import QuantitativeArithmeticRetainedNestedGeometricTraceV1
public import QuantitativeArithmeticRetainedGeometricTraceV1
public import QuantitativeEulerEndpointSandwichPerturbationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedTerminalSandwich
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeHolomorphic
open scoped ENNReal
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A)

theorem rep_trace_finite (a : Algebra A P) : AsymptoticRegularTrace.trace measure (rep A P a)<∞ :=
  AsymptoticHyperbolicArea.closed_terminal_trace_finite P.epsilon_pos
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
  have hh := QuantitativeEulerEndpointTerminalTrace.contraction_gram_trace (regularSum U) (rep A P b)
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
        δ*P.ε⁻¹ := by
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
    P.epsilon_pos.le)] at hh
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
      tr A P a+δ*P.ε⁻¹ := by
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


attribute [local irreducible] QuantitativeArithmeticRetainedFiniteTransport.normalizedExpression
  regularSum QuantitativeArithmeticRetainedNestedGeometricTrace.sandwichExpression

set_option backward.isDefEq.respectTransparency true in
/-- The concrete finite mixed normalizer pays filter replacement only on the
fixed terminal strip, not on its growing output truncation. -/
theorem normalized_sandwich_le_trace (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)
    (a : Algebra A P) (ha : 0≤a ∧ a≤1) (τ : ℝ) (e : AsymptoticSectorSigns.Sector N)
    (T : Expression) (hT : ∀x,0≤regularSum T x ∧ regularSum T x≤1)
    (δ : ℝ) (he : ∀x,‖rep A P a x-regularSum T x‖≤δ) (Y H : ℝ) :
    signedTrace volume (regularSum (retainedExpression Y H
      (QuantitativeArithmeticRetainedNestedGeometricTrace.sandwichExpression A hR₀ hN P τ e T)))≤
      tr A P a+δ*P.ε⁻¹ := by
  have ht := retained_sandwich_le_trace A P a ha
    (QuantitativeArithmeticRetainedFiniteTransport.normalizedExpression A P hR₀ hN τ e) T
    (QuantitativeArithmeticRetainedGeometricTrace.finiteAmbient_norm A P hR₀ hN τ e) hT
    (QuantitativeArithmeticRetainedGeometricTrace.finiteAmbient_terminal A P hR₀ hN τ e)
    (QuantitativeArithmeticRetainedGeometricTrace.finiteAmbient_trace_finite A P hR₀ hN τ e) δ he Y H
  have heq : regularSum (retainedExpression Y H
      (QuantitativeArithmeticRetainedNestedGeometricTrace.sandwichExpression A hR₀ hN P τ e T))=
      regularRetained Y H (fun x =>
        (regularSum (QuantitativeArithmeticRetainedFiniteTransport.normalizedExpression A P hR₀ hN τ e) x).comp
          ((regularSum T x).comp
            (regularSum (QuantitativeArithmeticRetainedFiniteTransport.normalizedExpression A P hR₀ hN τ e) x).adjoint)) := by
    funext x
    simp only [QuantitativeArithmeticRetainedNestedGeometricTrace.sandwichExpression,
      regularSum_retainedExpression,regularSum_compose,regularSum_adjoint,regularRetained]
  rw [heq]
  exact ht

#print axioms rep_trace_finite
#print axioms positive_sandwich_le_trace
#print axioms sandwich_trace_error
#print axioms retained_sandwich_le_trace
#print axioms normalized_sandwich_le_trace
end QuantitativeArithmeticRetainedTerminalSandwich
