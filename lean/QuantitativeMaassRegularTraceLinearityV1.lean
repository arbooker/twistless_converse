module

public import QuantitativeMaassRegularPositiveTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [MeasurableSpace α]

/-- Real rooted diagonal as a continuous real-linear map. -/
def rootDiagonal : (ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))→L[ℝ]ℝ :=
  Complex.reCLM.comp ((matrixCLM (1:G) 1).restrictScalars ℝ)

theorem rootDiagonal_apply (B : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ)) :
    rootDiagonal B=(matrix B 1 1).re := rfl

theorem signedTrace_add_of_integrable (μ : Measure α)
    (A B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (ha : Integrable (fun x => rootDiagonal (A x)) μ)
    (hb : Integrable (fun x => rootDiagonal (B x)) μ) :
    signedTrace μ (fun x => A x+B x)=signedTrace μ A+signedTrace μ B := by
  change (∫ x,rootDiagonal (A x+B x) ∂μ)=_
  simp only [map_add]
  exact integral_add ha hb

theorem signedTrace_sub_of_integrable (μ : Measure α)
    (A B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (ha : Integrable (fun x => rootDiagonal (A x)) μ)
    (hb : Integrable (fun x => rootDiagonal (B x)) μ) :
    signedTrace μ (fun x => A x-B x)=signedTrace μ A-signedTrace μ B := by
  change (∫ x,rootDiagonal (A x-B x) ∂μ)=_
  simp only [map_sub]
  exact integral_sub ha hb

variable [Countable G] [MulAction G α] [TopologicalSpace α] [DiscreteTopology α]

theorem positive_diagonal_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hcF : Covariant F) (hp : ∀ x,0≤F x)
    {K : ℝ} (hn : ∀ x,‖F x‖≤K) (hf : trace μ F<∞) :
    Integrable (fun x => rootDiagonal (F x)) μ := by
  have hh := positive_weight_diagonal_integrable μ hmp F (fun _ => 1) hF
    (fun _ _ => measurable_const) hcF covariant_one hp hn
    (fun _ => le_rfl : ∀ _ : α,‖(1 : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))‖≤‖(1 : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))‖) hf
  exact hh

#print axioms rootDiagonal_apply
#print axioms signedTrace_add_of_integrable
#print axioms signedTrace_sub_of_integrable
#print axioms positive_diagonal_integrable
end AsymptoticRegularTrace
