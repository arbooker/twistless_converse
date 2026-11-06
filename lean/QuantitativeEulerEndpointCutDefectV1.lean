module

public import QuantitativeEulerEndpointCutMassV1
public import QuantitativeEulerEndpointWindowDefectV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerCut
open AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointSpectralWindow MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

theorem half_cut_defect_bounds (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) :
    A-(4:ℝ) • (A-A^2)≤cutElement hact s hs p hp U hU A
      (IsSelfAdjoint.of_nonneg hA0) (1/2) (by norm_num) ∧
    cutElement hact s hs p hp U hU A (IsSelfAdjoint.of_nonneg hA0) (1/2) (by norm_num)≤
      A+(4:ℝ) • (A-A^2) := by
  have hA := IsSelfAdjoint.of_nonneg hA0
  have hd := window_defect_bounds A hA0 hA1
  have hlo := intrinsic_window_sandwich hact s hs p hp U hU A hA
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<3/4)
  have hhi := intrinsic_window_sandwich hact s hs p hp U hU A hA
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1/2)
  exact ⟨hd.1.trans hlo.2,hhi.1.trans hd.2⟩

include U hU in
/-- Replacing an actual positive contraction by its actual half-threshold
projection changes the trace by at most four times its idempotency defect. -/
theorem half_cut_trace_error (μ : Measure α) (hf : μ s<∞)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) :
    |(trace μ (fun x => (highAt (ρ A x) (1/2)).starProjection)).toReal-
      rootedTrace hact s hs p hp μ hf A|≤
        4*rootedTrace hact s hs p hp μ hf (A-A^2) := by
  have hb := half_cut_defect_bounds hact s hs p hp U hU A hA0 hA1
  have hlo := rootedTrace_mono hact s hs p hp μ hf hb.1
  have hhi := rootedTrace_mono hact s hs p hp μ hf hb.2
  rw [map_sub,map_smul,smul_eq_mul,
    cut_trace_eq hact s hs p hp U hU μ hf A (IsSelfAdjoint.of_nonneg hA0)] at hlo
  rw [map_add,map_smul,smul_eq_mul,
    cut_trace_eq hact s hs p hp U hU μ hf A (IsSelfAdjoint.of_nonneg hA0)] at hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms half_cut_defect_bounds
#print axioms half_cut_trace_error
end QuantitativeEulerEndpointCornerCut
