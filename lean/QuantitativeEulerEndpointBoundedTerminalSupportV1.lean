module

public import QuantitativeEulerEndpointBoundedTerminalSoftV1
public import QuantitativeEulerEndpointSupportOperationsV1
public import QuantitativeEulerEndpointPacketSupportV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedTerminal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointPrepared
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointUnitSubcorner
open QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup QuantitativeHolomorphic Polynomial

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ)
  (hC : ∀ i x,‖normalizedCombinedRows A P e hs l i x‖≤C i)
variable (r : EligiblePrime N) (hrQ : ¬r.val∣Q)
  (hrfixed : ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q) (hr : r∉l)
local notation "t" => terminalRegion A P
local notation "ht" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable t ht

include hrQ hrfixed hr in
theorem combined_rows_supported (i : ℕ) (x : UpperHalfPlane) :
    Supported (integralGroup r.val) (normalizedCombinedRows A P e hs l i x) := by
  have hU := normalized_reconstruction_supported A r.val (NeZero.pos N) r.property.2 hrQ P e x
  cases i with
  | zero =>
    exact supported_comp _ _ _
      (newBaselineDetector_supported N e r.val r.property.2 hrfixed hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) x) hU
  | succ i =>
    exact supported_comp _ _ _
      (packetSequence_supported N (NeZero.pos N) (sign e.1) hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) l r hr i x) hU

include hrQ hrfixed hr in
theorem combined_gram_supported (x : Base) :
    Supported (integralGroup r.val) (rep A P (gram A P e hs l C hC) x) := by
  rw [rep_gram]
  apply Finset.sum_induction
  · intro a b ha hb
    exact supported_add _ _ _ ha hb
  · intro g h _
    rfl
  intro i _
  have hh : Supported (integralGroup r.val) (scaledRows A P e hs l C i x) :=
    supported_smul _ _ (combined_rows_supported A P e hs l r hrQ hrfixed hr i x) _
  exact supported_comp _ _ _ (supported_adjoint _ _ hh) hh

include hrQ hrfixed hr in
/-- Every future eligible prime avoiding the fixed denominators and the current
block remains a support prime after the complete polynomial update. -/
theorem next_supported (F : Algebra A P)
    (hF : ∀ x,Supported (integralGroup r.val) (rep A P F x)) (L : ℕ) (z : ℝ[X]) (x : Base) :
    Supported (integralGroup r.val) (rep A P (next A P e hs l C hC F L z) x) := by
  have hP (y : Base) : Supported (integralGroup r.val) (rep A P 1 y) := by
    rw [rep_one]
    exact reconstructed_terminal_supported A P r.val y
  have hG (y : Base) : Supported (integralGroup r.val)
      (QuantitativeEulerEndpointSubcorner.representation action_measurable t ht 1 hp (unitGram A P e hs l C hC) y) := by
    change Supported (integralGroup r.val) (rep A P (value action_measurable t ht (unitGram A P e hs l C hC)) y)
    rw [value_unitGram]
    exact combined_gram_supported A P e hs l C hC r hrQ hrfixed hr y
  have hh := QuantitativeEulerEndpointSupportAlgebra.update_polynomial_supported
    action_measurable t ht 1 hp (integralGroup r.val) hP
    (lift action_measurable t ht F) (unitGram A P e hs l C hC) hF hG L z x
  change Supported (integralGroup r.val)
    (rep A P (value action_measurable t ht (unitNext A P e hs l C hC F L z)) x) at hh
  rwa [value_unitNext] at hh

#print axioms combined_rows_supported
#print axioms combined_gram_supported
#print axioms next_supported
end QuantitativeEulerEndpointBoundedTerminal
