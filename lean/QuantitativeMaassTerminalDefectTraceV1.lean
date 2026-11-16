module

public import QuantitativeMaassTerminalPowerTraceV1
public import QuantitativeMaassTerminalHalfDefectV1
public import QuantitativeMaassConjugatedDefectTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointTerminalAlgebra
open scoped ENNReal

/-- The genuine regular polynomial trace is controlled directly by the
terminal filter trace and its already available idempotency defect.
No canonical-kernel identification or projection-preservation premise occurs. -/
theorem regular_power_trace_defect {N Q : ℕ} {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (U : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hsource : ∀ x,regularSum U x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum U x)
    (hf : trace volume (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞)
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) (m : ℕ) :
    signedTrace volume (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)≤
      tr A P F+4*((m:ℝ)+1)*tr A P (F-F^2) := by
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
  have hD : 0≤F-F^2 := sub_nonneg.mpr (by
    simpa only [pow_one] using CStarAlgebra.pow_antitone hF1 hF0 (by decide : 1≤2))
  have hd : 0≤(4:ℝ) • (F-F^2) := smul_nonneg (by norm_num) hD
  have hb := terminal_half_defect_bounds A P F hF0 hF1
  have hh := conjugated_filter_trace_of_projection_approx (tr A P) (tr_mono A P)
    (tr_cyclic A P) hsτ S F (halfProjection A P F (IsSelfAdjoint.of_nonneg hF0))
    ((4:ℝ) • (F-F^2)) hnS hF0 hF1 (half_projection A P F _) hd hb.1 hb.2 m
  rw [map_smul,smul_eq_mul] at hh
  nlinarith

#print axioms regular_power_trace_defect
end QuantitativeMaass
