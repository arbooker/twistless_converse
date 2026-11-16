module

public import QuantitativeMaassRegularTraceLinearityV1
public import AsymptoticRegularInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem diagonal_integrable_add (μ : Measure α) (A B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (ha : Integrable (fun x => rootDiagonal (A x)) μ)
    (hb : Integrable (fun x => rootDiagonal (B x)) μ) :
    Integrable (fun x => rootDiagonal (A x+B x)) μ := by
  apply (ha.add hb).congr
  exact Filter.Eventually.of_forall (fun x => (map_add rootDiagonal (A x) (B x)).symm)

#print axioms diagonal_integrable_add
end AsymptoticRegularTrace
