module

public import QuantitativeSpectralRegularCornerStepV1
public import QuantitativeSpectralDeflationChainV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularPacket

open AsymptoticRegularTrace AsymptoticSubgroupSupport
open QuantitativeSpectralDeflationChain QuantitativeSpectralRegularCornerStep
open QuantitativeSpectralCornerCutRow QuantitativeSpectralCutRow
open MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

variable (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (c : ℝ)

def projectionFamily (n : ℕ) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  projection (U x) (fun i => B i x) c n

def rowFamily (n : ℕ) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  packetRow (U x) (fun i => B i x) c n

variable
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h))
    (hcU : Covariant (fun x => (U x).toSubmodule.starProjection))
    (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
    (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
    (hc : 0 < c)

include hmU hcU hmB hcB hC hc in
/-- Regularity of every projection in the actual recursively constructed
packet follows by induction; no regularity of the cuts is postulated. -/
theorem projection_regular (n : ℕ) :
    (∀ g h, Measurable (fun x => matrix (projectionFamily U B c n x) g h)) ∧
      Covariant (projectionFamily U B c n) := by
  induction n with
  | zero => exact ⟨hmU,hcU⟩
  | succ n ih =>
    exact (step_regular (fun x => (chain (U x) (fun i => B i x) c n).toSubmodule)
      (B n) ih.1 ih.2 (hmB n) (hcB n) (C n) (hC n) c hc).1

include hmU hcU hmB hcB hC hc in
theorem row_regular (n : ℕ) :
    (∀ g h, Measurable (fun x => matrix (rowFamily U B c n x) g h)) ∧
      Covariant (rowFamily U B c n) := by
  have hp := projection_regular U B c hmU hcU hmB hcB C hC hc n
  exact (step_regular (fun x => (chain (U x) (fun i => B i x) c n).toSubmodule)
    (B n) hp.1 hp.2 (hmB n) (hcB n) (C n) (hC n) c hc).2

omit [Group G] [Countable G] [MeasurableSpace α] [MulAction G α] in
include hC hc in
/-- Normalizing and deflating never enlarges the original residual bound. -/
theorem row_norm_le (n : ℕ) (x : α) : ‖rowFamily U B c n x‖ ≤ C n := by
  have hh := norm_mul_le_of_le
    (cutNormalizer_contracts (restricted (chain (U x) (fun i => B i x) c n).toSubmodule (B n x)) hc)
    (hC n x)
  simpa only [rowFamily, packetRow, row, one_mul] using hh

omit [Countable G] [MeasurableSpace α] [MulAction G α] in
/-- Only already-used residuals need subgroup support. In particular a
future prime may be fresh even when its own residual is not integral there. -/
theorem projection_supported (S : Subgroup G) (x : α) (n : ℕ)
    (hU : Supported S (U x).toSubmodule.starProjection)
    (hB : ∀ i < n, Supported S (B i x)) (hc : 0 < c) :
    Supported S (projectionFamily U B c n x) := by
  induction n with
  | zero => exact hU
  | succ n ih =>
    have hp := ih (fun i hi => hB i (lt_trans hi (Nat.lt_succ_self n)))
    exact (step_supported S (chain (U x) (fun i => B i x) c n).toSubmodule
      (B n x) hp (hB n (Nat.lt_succ_self n)) c hc).1

omit [Countable G] [MeasurableSpace α] [MulAction G α] in
theorem row_supported (S : Subgroup G) (x : α) (n : ℕ)
    (hU : Supported S (U x).toSubmodule.starProjection)
    (hB : ∀ i ≤ n, Supported S (B i x)) (hc : 0 < c) :
    Supported S (rowFamily U B c n x) := by
  have hp := projection_supported U B c S x n hU (fun i hi => hB i hi.le) hc
  exact (step_supported S (chain (U x) (fun i => B i x) c n).toSubmodule
    (B n x) hp (hB n le_rfl) c hc).2

#print axioms projection_regular
#print axioms row_regular
#print axioms row_norm_le
#print axioms projection_supported
#print axioms row_supported

end QuantitativeSpectralRegularPacket
