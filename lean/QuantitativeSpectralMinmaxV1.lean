module

public import QuantitativeSpectralCutRegularityV1
public import AsymptoticRegularEmbeddingTraceV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralMinmax

open MeasureTheory ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut
open QuantitativeSpectralCutRegularity AsymptoticRegularTrace
open scoped lp ENNReal InnerProduct

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Tracial min--max for the actual regular orbit trace. A regular closed
subspace with quadratic lower bound `b>a` has trace at most the high cut at
`a`. The proof constructs an injective regular map and uses the already
formalized polar-decomposition dimension inequality. Infinite traces are
allowed; no discrete spectrum or finite-dimensional approximation is used. -/
theorem trace_le_high_cut (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmA : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hcA : Covariant A)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (U x)]
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    {a b : ℝ} (hab : a < b)
    (hcoercive : ∀ x v, v ∈ U x → b * ‖v‖^2 ≤ (⟪A x v, v⟫_ℂ).re) :
    trace μ (fun x => (U x).starProjection) ≤
      trace μ (fun x => (highAt (A x) a).starProjection) := by
  have hr := highAt_regular A hmA hcA hsa M hM a
  exact trace_le_of_injective_map μ hmp U (fun x => highAt (A x) a) hmU hcU
    (fun x => (highAt (A x) a).starProjection) hr.1 hr.2 1
    (fun x => (highAt (A x) a).starProjection_norm_le)
    (fun x v hv hz => high_projection_injective_on (A x) (hsa x) (U x) hab
      (hcoercive x) hv hz)
    (fun x v _ => (highAt (A x) a).starProjection_apply_mem v)

#print axioms trace_le_high_cut

end QuantitativeSpectralMinmax
