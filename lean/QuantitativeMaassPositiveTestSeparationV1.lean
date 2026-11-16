module

public import QuantitativeMaassPositiveTestSpaceV1
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem continuous_positiveTest_integrable (u : ℝ → H) (hu : Continuous u) (φ : PositiveSmoothTest) :
    Integrable (fun t => φ t • u t) :=
  (φ.continuous.smul hu).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right

theorem positiveTest_integral_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace H] [CompleteSpace G] (L : H →L[ℝ] G) (u : ℝ → H) (hu : Continuous u) (φ : PositiveSmoothTest) :
    L (∫ t,φ t • u t)=∫ t,φ t • L (u t) := by
  rw [← L.integral_comp_comm (continuous_positiveTest_integrable u hu φ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => L.map_smul (φ t) (u t))

/-- Positive smooth tests separate continuous vector-valued functions on
the closed positive half-line. The value at zero follows by continuity,
not from testing at a point or from an assumed endpoint trace. -/
theorem continuous_eq_zero_of_positiveTests [CompleteSpace H]
    (u : ℝ → H) (hu : Continuous u)
    (hz : ∀ φ : PositiveSmoothTest,(∫ t,φ t • u t)=0) :
    ∀ t,0≤t → u t=0 := by
  have hae : ∀ᵐ t ∂volume,t∈Ioi (0:ℝ) → u t=0 :=
    isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hu.continuousOn.locallyIntegrableOn measurableSet_Ioi)
      (fun g hg hc hs => hz ⟨g,hg,hc,hs⟩)
  have hr : u =ᵐ[volume.restrict (Ioi (0:ℝ))] (fun _ => 0) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr hae
  have he : EqOn u (fun _ => 0) (Ioi (0:ℝ)) :=
    Measure.eqOn_open_of_ae_eq hr isOpen_Ioi hu.continuousOn continuous_const.continuousOn
  have hcl := he.closure hu continuous_const
  rw [closure_Ioi] at hcl
  exact hcl

#print axioms positiveTest_integral_map
#print axioms continuous_eq_zero_of_positiveTests

end QuantitativeMaass
