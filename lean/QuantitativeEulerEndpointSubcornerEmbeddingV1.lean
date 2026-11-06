module

public import QuantitativeSpectralRegularPacketV1
public import QuantitativeSpectralPacketSupportV1
public import QuantitativeEulerEndpointSubcornerV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerEmbedding

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeEulerEndpointSubcorner
open QuantitativeSpectralRegularPacket QuantitativeSpectralPacketSupport
open QuantitativeSpectralDeflationChain
open MeasureTheory
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c)

include hU in
theorem initial_matrix_measurable :
    ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h) := by
  simp only [hU]
  exact QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs p

include hU in
theorem initial_covariant : Covariant (fun x => (U x).toSubmodule.starProjection) := by
  simp only [hU]
  exact QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs p

/-- Actual surviving projections as elements of the concrete terminal
finite-corner C*-algebra. -/
def projectionElement (n : ℕ) : Subcorner hact s hs p hp := by
  have hreg := projection_regular U B c (initial_matrix_measurable hact s hs p U hU)
    (initial_covariant hact s hs p U hU) hmB hcB C hC hc n
  refine ofFamily hact s hs p hp (projectionFamily U B c n) 1 ?_ hreg.1 hreg.2 ?_ ?_
  · intro x
    exact (chain (U x) (fun i => B i x) c n).toSubmodule.starProjection_norm_le
  · intro x
    have he := projection_left_initial (U x) (fun i => B i x) c n
    change (U x).toSubmodule.starProjection * projectionFamily U B c n x = _ at he
    simpa only [hU, projectionFamily, rowFamily, ContinuousLinearMap.mul_def] using he
  · intro x
    have he := projection_right_initial (U x) (fun i => B i x) c n
    change projectionFamily U B c n x * (U x).toSubmodule.starProjection = _ at he
    simpa only [hU, projectionFamily, rowFamily, ContinuousLinearMap.mul_def] using he

@[simp] theorem representation_projectionElement (n : ℕ) :
    representation hact s hs p hp (projectionElement hact s hs p hp U hU B hmB hcB C hC c hc n) =
      projectionFamily U B c n := rfl

variable (hsource : ∀ i x, B i x * QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x = B i x)

include hsource in
/-- Actual normalized rows as finite-corner elements. Uniform norm,
measurability, covariance, and both support identities are discharged. -/
def rowElement (n : ℕ) : Subcorner hact s hs p hp := by
  have hreg := row_regular U B c (initial_matrix_measurable hact s hs p U hU)
    (initial_covariant hact s hs p U hU) hmB hcB C hC hc n
  apply ofFamily hact s hs p hp (rowFamily U B c n) (C n)
    (row_norm_le U B c C hC hc n) hreg.1 hreg.2
  · intro x
    have he := row_left_initial (U x) (fun i => B i x) c hc n
    change (U x).toSubmodule.starProjection * rowFamily U B c n x = _ at he
    simpa only [hU, projectionFamily, rowFamily, ContinuousLinearMap.mul_def] using he
  · intro x
    have hh : B n x * projection (U x) (fun i => B i x) c 0 = B n x := by
      change B n x * (U x).toSubmodule.starProjection = _
      rw [hU]
      exact hsource n x
    have he := row_right_initial (U x) (fun i => B i x) c n hh
    change rowFamily U B c n x * (U x).toSubmodule.starProjection = _ at he
    simpa only [hU, projectionFamily, rowFamily, ContinuousLinearMap.mul_def] using he

@[simp] theorem representation_rowElement (n : ℕ) :
    representation hact s hs p hp (rowElement hact s hs p hp U hU B hmB hcB C hC c hc hsource n) =
      rowFamily U B c n := rfl

#print axioms projectionElement
#print axioms representation_projectionElement
#print axioms rowElement
#print axioms representation_rowElement

end QuantitativeEulerEndpointSubcornerEmbedding
