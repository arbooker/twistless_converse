module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace QuantitativeMaass.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def timePrimitive (f : ℝ → E) (t : ℝ) : E := ∫ u in (0:ℝ)..t, f u

theorem timePrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (timePrimitive f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem timePrimitive_continuous {f : ℝ → E} (hf : Continuous f) :
    Continuous (timePrimitive f) :=
  continuous_iff_continuousAt.mpr (fun t => (timePrimitive_hasDerivAt hf t).continuousAt)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem timePrimitive_continuousMap_apply (G : ℝ → C(K,ℝ)) (hG : Continuous G)
    (t : ℝ) (s : K) : timePrimitive G t s=timePrimitive (fun u => G u s) t := by
  exact ((ContinuousMap.evalCLM (R := ℝ) s).intervalIntegral_comp_comm (μ := volume)
    (hG.intervalIntegrable 0 t)).symm

/-- Reconstruct a continuous-map-valued curve from its pointwise acceleration.
Joint control of the velocity is not needed: norm continuity of the acceleration
and the scalar fundamental theorem of calculus give the strong reconstruction. -/
theorem continuousMap_doublePrimitive (F G : ℝ → C(K,ℝ)) (v : ℝ → K → ℝ)
    (hG : Continuous G)
    (hF : ∀ s t, HasDerivAt (fun u => F u s) (v t s) t)
    (hv : ∀ s t, HasDerivAt (fun u => v u s) (G t s) t)
    (hv0 : ∀ s, v 0 s=0) (t : ℝ) :
    F t=F 0+timePrimitive (timePrimitive G) t := by
  have hGc := timePrimitive_continuous hG
  have hfirst : ∀ u s, timePrimitive G u s=v u s := by
    intro u s
    rw [timePrimitive_continuousMap_apply G hG]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x (_ : x∈uIcc (0:ℝ) u) => hv s x)
      (((ContinuousMap.evalCLM (R := ℝ) s).continuous.comp hG).intervalIntegrable 0 u)
    simpa only [timePrimitive,hv0 s,sub_zero] using h
  ext s
  change F t s=F 0 s+timePrimitive (timePrimitive G) t s
  rw [timePrimitive_continuousMap_apply (timePrimitive G) hGc]
  have hvcont : Continuous (fun u => v u s) :=
    continuous_iff_continuousAt.mpr (fun u => (hv s u).continuousAt)
  have hsecond := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u∈uIcc (0:ℝ) t) => hF s u) (hvcont.intervalIntegrable 0 t)
  simp_rw [hfirst]
  change F t s=F 0 s+∫ u in (0:ℝ)..t, v u s
  rw [hsecond]
  ring

#print axioms continuousMap_doublePrimitive

end QuantitativeMaass.Wave
