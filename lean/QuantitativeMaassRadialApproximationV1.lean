module

public import QuantitativeMaassRadialKernelLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The geometric initial-value limit for normalized shrinking radial
kernels. All mass, support, and absolute-mass hypotheses are explicit kernel
conditions; the actual quotient output is the conclusion. -/
theorem radialKernel_output_tendsto {ι : Type*} (l : Filter ι) (N : ℕ)
    (g : ι → ℝ → ℂ) (hg : ∀ i,ContDiff ℝ ∞ (g i))
    (R : ι → ℝ) (hR : ∀ i,0≤R i)
    (hs : ∀ i,Function.support (g i)⊆Iic (Real.cosh (R i)))
    (hlim : Tendsto R l (𝓝 0))
    (hmass : ∀ i,(2*Real.pi:ℂ)*(∫ q in Ioi (1:ℝ),g i q)=1)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ i,2*Real.pi*(∫ q in Ioi (1:ℝ),‖g i q‖)≤C)
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (x : ℍ) (hfx : ContinuousAt f x) :
    Tendsto (fun i => (radialKernelData N (g i) (hg i) (R i) (hR i) (hs i)).output f x)
      l (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hCp : 0<C+1 := by linarith
  have he : 0<ε/(C+1) := div_pos hε hCp
  obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp hfx (ε/(C+1)) he
  have hRδ : ∀ᶠ i in l,R i<δ := (tendsto_order.mp hlim).2 δ hδ
  filter_upwards [hRδ] with i hi
  have hnear (y : ℍ) (hy : y∈Metric.closedBall x (R i)) : ‖f y-f x‖≤ε/(C+1) := by
    have hd : dist y x<δ := lt_of_le_of_lt hy hi
    simpa only [dist_eq_norm] using (hfδ hd).le
  have hh := radialKernel_output_local_error N (g i) (hg i) (R i) (hR i) (hs i)
    f hf hinv hL x (ε/(C+1)) hnear
  rw [hmass i,one_mul] at hh
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (hh.trans (mul_le_mul_of_nonneg_right (hbound i) he.le))
  have hid : (C+1)*(ε/(C+1))=ε := mul_div_cancel₀ ε (ne_of_gt hCp)
  nlinarith

#print axioms radialKernel_output_tendsto

end QuantitativeMaass
