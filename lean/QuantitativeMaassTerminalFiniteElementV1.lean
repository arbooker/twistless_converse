module

public import QuantitativeMaassTerminalPowerTraceV1
public import QuantitativeEulerEndpointTerminalUnitExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticFiniteBranch QuantitativeHolomorphic ContinuousLinearMap
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularEmbedding
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (T : Expression) (hT : ∀ x,0≤regularSum T x ∧ regularSum T x≤1)
    (hleft : ∀ x,AsymptoticOrbitDiagonal.corner (terminalRegion A P) x*regularSum T x=regularSum T x)
    (hright : ∀ x,regularSum T x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum T x)

def terminalFiniteElement : Algebra A P :=
  ofFamily action_measurable (terminalRegion A P) (terminal_measurable A P)
    (regularSum T) 1
    (fun x => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hT x).1).mpr (hT x).2)
    (regularSum_matrix_measurable T) (regularSum_covariant T) hleft hright

theorem terminalFiniteElement_order :
    0≤terminalFiniteElement A P T hT hleft hright ∧ terminalFiniteElement A P T hT hleft hright≤1 := by
  have h0 : 0≤terminalFiniteElement A P T hT hleft hright := by
    apply (QuantitativeSpectralRegularOrder.pointwise_le_iff action_measurable
      (terminalRegion A P) (terminal_measurable A P) 0 _).mp
    exact fun x => (hT x).1
  have hn : ‖terminalFiniteElement A P T hT hleft hright‖≤1 := by
    apply norm_ofFamily_le
    norm_num
  exact ⟨h0,(CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp hn⟩

theorem terminalFiniteElement_close (F : Algebra A P) {δ : ℝ} (hδ : 0≤δ)
    (he : ∀ x,‖regularSum T x-rep A P F x‖≤δ) :
    ‖terminalFiniteElement A P T hT hleft hright-F‖≤δ := by
  apply (BoundedContinuousFunction.norm_le hδ).mpr
  exact he

#print axioms terminalFiniteElement_order
#print axioms terminalFiniteElement_close
end QuantitativeMaass
