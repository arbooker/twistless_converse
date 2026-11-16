module

public import QuantitativeMaassPowerSandwichCoefficientV1
public import QuantitativeMaassConjugatedFilterExcessV1
public import QuantitativeMaassRawCommonRegularTraceV1
public import AsymptoticRegularBoundedSandwichV1

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeHolomorphic
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (U : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hsource : ∀ x,regularSum U x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum U x)

def terminalExpressionGram : Algebra A P :=
  QuantitativeSpectralSourceGram.gramElement action_measurable (terminalRegion A P)
    (terminal_measurable A P) (regularSum U) (regularSum_matrix_measurable U)
    (regularSum_covariant U) 1 hU hsource

theorem terminalExpressionGram_order :
    0≤terminalExpressionGram A P U hU hsource ∧ terminalExpressionGram A P U hU hsource≤1 := by
  have hp := QuantitativeSpectralSourceGram.gramElement_nonneg action_measurable (terminalRegion A P)
    (terminal_measurable A P) (regularSum U) (regularSum_matrix_measurable U)
    (regularSum_covariant U) 1 hU hsource
  have hn := QuantitativeSpectralSourceGram.gramElement_norm_le action_measurable (terminalRegion A P)
    (terminal_measurable A P) (regularSum U) (regularSum_matrix_measurable U)
    (regularSum_covariant U) 1 hU hsource
  exact ⟨hp,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mp (by simpa using hn)⟩

/-- The actual regular trace of the ambient polynomial is a finite terminal
trace. Only the reconstruction Gram needs finite trace. -/
theorem regular_power_trace_terminal
    (hf : trace volume (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞)
    (F : Algebra A P) (m : ℕ) :
    signedTrace volume (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)=
      tr A P (1-(1-F*terminalExpressionGram A P U hU hsource)^m) := by
  let G := terminalExpressionGram A P U hU hsource
  let K := powerSandwichCoefficient F G m
  have hrep (x : UpperHalfPlane) :
      regularSum U x*rep A P K x*(regularSum U x).adjoint=
        1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m := by
    let r : Algebra A P→ₙ+*(RegularSpace→L[ℂ]RegularSpace) :=
      { toFun := fun a => rep A P a x
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl }
    exact powerSandwichCoefficient_rep r F G (regularSum U x) (regularSum U x).adjoint rfl m
  have he : (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)=
      (fun x => (regularSum U x).comp ((rep A P K x).comp (regularSum U x).adjoint)) := by
    funext x
    rw [←hrep]
    rfl
  rw [he, signedTrace_bounded_sandwich volume AsymptoticRationalGroup.measurePreserving
    (regularSum U) (rep A P K) (regularSum_matrix_measurable U)
    (representation_matrix_measurable _ _ _ _ _ K) (regularSum_covariant U)
    (representation_covariant _ _ _ _ _ K) hf (representation_norm_le _ _ _ _ _ K)]
  change tr A P (K*G)=_
  rw [powerSandwichCoefficient_mul]

include hU hsource in
/-- A concrete terminal Gram gives the same coefficient-one canonical
trace estimate, before any finite-expression approximation is introduced. -/
theorem regular_power_trace_excess
    (hf : trace volume (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞)
    (F E : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1)
    (hE : IsStarProjection E) (hEF : E≤F) (m : ℕ) :
    signedTrace volume (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)-tr A P E≤
      (m:ℝ)*tr A P (F-E) := by
  let G := terminalExpressionGram A P U hU hsource
  let S := CFC.sqrt G
  have hG := terminalExpressionGram_order A P U hU hsource
  have hS : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)
  have hSS : S*S=G := CFC.sqrt_mul_sqrt_self G hG.1
  have hnG : ‖G‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg G hG.1).mpr hG.2
  have hnS : ‖S‖≤1 := by
    have hh : ‖star S*S‖=‖S‖*‖S‖ := CStarRing.norm_star_mul_self
    rw [hS.star_eq,hSS] at hh
    nlinarith [norm_nonneg S]
  have hsτ : ∀ a : Algebra A P,tr A P (star a)=tr A P a :=
    QuantitativeSpectralFiniteCornerTrace.rootedTrace_star _ _ _ _ _
  have he := cyclic_power_filter (tr A P) (tr_cyclic A P) (F*S) S m
  have he1 : F*S*S=F*G := by rw [mul_assoc,hSS]
  have he2 : S*(F*S)=S*F*star S := by rw [hS.star_eq,mul_assoc]
  rw [he1,he2] at he
  rw [regular_power_trace_terminal A P U hU hsource hf,he]
  have hh := conjugated_power_filter_excess (tr A P) (tr_mono A P) (tr_cyclic A P) hsτ
    S F E hnS hF0 hF1 hE hEF m
  apply hh.trans
  have ht : 0≤tr A P (F-E) := by simpa only [map_zero] using tr_mono A P (sub_nonneg.mpr hEF)
  have hs2 : ‖S‖^2≤1 := by nlinarith [norm_nonneg S]
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg m
  nlinarith [mul_le_mul_of_nonneg_left hs2 hm]

#print axioms terminalExpressionGram_order
#print axioms regular_power_trace_terminal
#print axioms regular_power_trace_excess
end QuantitativeMaass
