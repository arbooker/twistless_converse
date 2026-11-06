module

public import QuantitativeEulerEndpointBlockGramV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockRestriction
open ContinuousLinearMap QuantitativeSpectralDeflationChain QuantitativeSpectralCornerCutRow
open QuantitativeEulerEndpointBlockGram AsymptoticRegularTrace MeasureTheory
open scoped lp

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

theorem step_eq_of_restriction (U : ClosedSubmodule ℂ H) (B C : H →L[ℂ] H) (c : ℝ)
    (h : B*U.toSubmodule.starProjection=C*U.toSubmodule.starProjection) : step U B c=step U C c := by
  apply SetLike.ext
  intro v
  change v∈nextSpace U.toSubmodule B c ↔ v∈nextSpace U.toSubmodule C c
  simp only [nextSpace,restricted,h]

/-- Right restricting every row to the initial source leaves every
actual deflation subspace unchanged, including its quantitative thresholds. -/
theorem chain_restrict_initial (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H)
    (c : ℝ) (n : ℕ) :
    chain U (fun i => B i*U.toSubmodule.starProjection) c n=chain U B c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chain,chain,ih]
    apply step_eq_of_restriction
    have hle : chain U B c n≤U := chain_antitone U B c (Nat.zero_le n)
    have hp : U.toSubmodule.starProjection*(chain U B c n).toSubmodule.starProjection=
        (chain U B c n).toSubmodule.starProjection := by
      exact ContinuousLinearMap.ext (fun v => U.toSubmodule.starProjection_eq_self_iff.mpr
        (hle ((chain U B c n).toSubmodule.starProjection_apply_mem v)))
    rw [mul_assoc,hp]
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (q : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs)
  (V : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hV : ∀ x, (V x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))

include hV in
/-- The hard packet in the soft update is the original-row packet exactly.
This permits using the previously proved fresh-prime chain contraction. -/
theorem restricted_projectionFamily (c : ℝ) (n : ℕ) :
    QuantitativeSpectralRegularPacket.projectionFamily V (rows hact s hs B q) c n=
      QuantitativeSpectralRegularPacket.projectionFamily V B c n := by
  funext x
  change (chain (V x) (fun i => rows hact s hs B q i x) c n).toSubmodule.starProjection=
    (chain (V x) (fun i => B i x) c n).toSubmodule.starProjection
  simp only [rows,← hV,chain_restrict_initial]

#print axioms step_eq_of_restriction
#print axioms chain_restrict_initial
#print axioms restricted_projectionFamily
end QuantitativeEulerEndpointBlockRestriction
