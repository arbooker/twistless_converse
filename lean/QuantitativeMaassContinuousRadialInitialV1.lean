module

public import QuantitativeMaassContinuousRadialUnfoldV1
public import QuantitativeMaassAbelNormalizedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass.ContinuousRadial

/-- A local oscillation estimate for the literal quotient convolution. The
normalization and error constant are the exact hyperbolic radial masses. -/
theorem radialKernel_output_local_error (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Continuous f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (x : ℍ) (ε : ℝ)
    (hnear : ∀ y ∈ Metric.closedBall x R,‖f y-f x‖≤ε) :
    ‖(radialKernelData N g hg R hR hs).output f x-
      ((2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q)*f x‖≤
        (2*Real.pi*(∫ q in Ioi (1:ℝ),‖g q‖))*ε := by
  let φ : ℍ → ℂ := fun y => g (Real.cosh (dist y x))
  have hφ : Integrable φ := hyperbolic_radial_integrable g hg.continuous x R hR hs
  have hu := continuous_radial_output_unfold N g hg R hR hs f hf hinv x
  have hi : Integrable (fun y => φ y*(f y-f x)) := by
    have hh := hu.1.sub (hφ.mul_const (f x))
    change Integrable (fun y => φ y*f y-φ y*f x) at hh
    simpa only [mul_sub] using hh
  have he : (radialKernelData N g hg R hR hs).output f x-
      ((2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q)*f x=∫ y,φ y*(f y-f x) := by
    simp_rw [mul_sub]
    rw [integral_sub hu.1 (hφ.mul_const (f x)),integral_mul_const,hu.2.2]
    rw [integral_hyperbolic_radial]
  rw [he]
  calc
    _ ≤ ∫ y,‖φ y*(f y-f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,‖φ y‖*ε := by
      apply integral_mono hi.norm (hφ.norm.mul_const ε)
      intro y
      dsimp only
      rw [norm_mul]
      by_cases hy : φ y=0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_left (hnear y ?_) (norm_nonneg _)
        have hb := Real.cosh_le_cosh.mp (hs hy)
        rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hb
        exact hb
    _ = _ := by
      rw [integral_mul_const]
      change (∫ y : ℍ,‖g (Real.cosh (dist y x))‖)*ε=_
      rw [integral_hyperbolic_radial_norm]

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
    (f : ℍ → ℂ) (hf : Continuous f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (x : ℍ) :
    Tendsto (fun i => (radialKernelData N (g i) (hg i) (R i) (hR i) (hs i)).output f x)
      l (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hCp : 0<C+1 := by linarith
  have he : 0<ε/(C+1) := div_pos hε hCp
  obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε/(C+1)) he
  have hRδ : ∀ᶠ i in l,R i<δ := (tendsto_order.mp hlim).2 δ hδ
  filter_upwards [hRδ] with i hi
  have hnear (y : ℍ) (hy : y∈Metric.closedBall x (R i)) : ‖f y-f x‖≤ε/(C+1) := by
    have hd : dist y x<δ := lt_of_le_of_lt hy hi
    simpa only [dist_eq_norm] using (hfδ hd).le
  have hh := radialKernel_output_local_error N (g i) (hg i) (R i) (hR i) (hs i)
    f hf hinv x (ε/(C+1)) hnear
  rw [hmass i,one_mul] at hh
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (hh.trans (mul_le_mul_of_nonneg_right (hbound i) he.le))
  have hid : (C+1)*(ε/(C+1))=ε := mul_div_cancel₀ ε (ne_of_gt hCp)
  nlinarith

/-- The constructed, normalized Abel family recovers every continuous
invariant function, without a global L2 hypothesis at each point as its radius shrinks. -/
theorem abelNormalizedProfile_output_tendsto {ι : Type*} (l : Filter ι) (N : ℕ)
    (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (f : ℍ → ℂ) (hf : Continuous f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (x : ℍ) :
    Tendsto (fun i => (radialKernelData N (abelNormalizedProfile (R i))
      (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
      (abelNormalizedProfile_support _ (hR i))).output f x) l (𝓝 (f x)) :=
  radialKernel_output_tendsto l N (fun i => abelNormalizedProfile (R i))
    (fun i => abelNormalizedProfile_smooth _ (hR i)) R (fun i => (hR i).le)
    (fun i => abelNormalizedProfile_support _ (hR i)) hlim
    (fun i => abelNormalizedProfile_mass _ (hR i)) 1 (by norm_num)
    (fun i => (abelNormalizedProfile_norm_mass _ (hR i)).le) f hf hinv x


#print axioms radialKernel_output_local_error
#print axioms radialKernel_output_tendsto
#print axioms abelNormalizedProfile_output_tendsto

end QuantitativeMaass.ContinuousRadial
