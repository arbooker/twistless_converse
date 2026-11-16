module

public import QuantitativeMaassAbelContinuityV1
public import Mathlib.MeasureTheory.Measure.Support

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- Continuity of the literal kernel rows in squared L2 distance, using one
locally uniform kernel bound and the finite quotient measure. -/
theorem oneSidedAbelKernel_row_L2_continuous (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    Tendsto (fun u => ∫ y,‖radialPoincareKernel N (abelProfile F) u y-
      radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N) (𝓝 x) (𝓝 0) := by
  let K := radialPoincareKernel N (abelProfile F)
  have hc : Continuous (fun p : ℍ×ℍ => K p.1 p.2) :=
    oneSidedAbelKernel_joint_continuous N F hF R hR hs
  have hm (u : ℍ) : AEStronglyMeasurable (K u) (quotientMeasure N) :=
    (Continuous.uncurry_left (f:=K) u hc).aestronglyMeasurable
  obtain ⟨D,_,hD⟩ := oneSidedAbelKernel_local_bound N F hF R hR hs x 1
  have hb : ∀ᶠ u in 𝓝 x,∀ᵐ y ∂quotientMeasure N,‖‖K u y-K x y‖^2‖≤(2*D)^2 := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with u hu
    change dist u x<1 at hu
    filter_upwards with y
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hh := (norm_sub_le (K u y) (K x y)).trans
      (add_le_add (hD u hu.le y) (hD x (by simp) y))
    linarith
  have hl : ∀ᵐ y ∂quotientMeasure N,Tendsto (fun u => ‖K u y-K x y‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    filter_upwards with y
    have hh : Continuous (fun u => K u y) := Continuous.uncurry_right (f:=K) y hc
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      ((hh.continuousAt (x:=x)).tendsto.sub_const (K x y)).norm.pow 2
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ => (2*D)^2)
    (Eventually.of_forall (fun u => ((hm u).sub (hm x)).norm.pow 2)) hb (integrable_const _) hl
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero,K] using ht

/-- The actual quotient Hilbert columns have the literal squared-kernel distance. -/
theorem oneSidedAbelColumn_sub_energy (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x u : ℍ) :
    ‖oneSidedAbelColumn N F hF R hR hs u-oneSidedAbelColumn N F hF R hR hs x‖^2=
      ∫ y,‖radialPoincareKernel N (abelProfile F) u y-
        radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N := by
  change ‖(oneSidedAbelColumn N F hF R hR hs u).val-
    (oneSidedAbelColumn N F hF R hR hs x).val‖^2=_
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (oneSidedAbelColumn N F hF R hR hs u).val
    (oneSidedAbelColumn N F hF R hR hs x).val,
    oneSidedAbelColumn_coeFn N F hF R hR hs u,
    oneSidedAbelColumn_coeFn N F hF R hR hs x] with y hy hu hx
  rw [hy,Pi.sub_apply,hu,hx]

/-- Strong Hilbert-space continuity of the original Abel kernel columns. -/
theorem oneSidedAbelColumn_continuous (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    Continuous (oneSidedAbelColumn N F hF R hR hs) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  have ht := oneSidedAbelKernel_row_L2_continuous N F hF R hR hs x
  simp_rw [← oneSidedAbelColumn_sub_energy N F hF R hR hs x] at ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

/-- A continuous representative of each original real Abel packet output. -/
theorem oneSidedAbelKernel_output_continuous (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (v : AutomorphicSpace N) :
    Continuous (fun x => ∫ y,radialPoincareKernel N (abelProfile F) x y*v.val y
      ∂quotientMeasure N) := by
  simp_rw [← oneSidedAbelColumn_inner N F hF hr R hR hs]
  exact (oneSidedAbelColumn_continuous N F hF R hR hs).inner continuous_const

/-- Continuous representatives agreeing almost everywhere agree on the
measure support. This is the pointwise passage needed before taking diagonals. -/
theorem continuous_eq_on_measure_support {A E : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [TopologicalSpace E] [T2Space E] (μ : Measure A) (f g : A → E)
    (hf : Continuous f) (hg : Continuous g) (he : f=ᵐ[μ]g) :
    EqOn f g μ.support :=
  μ.support_subset_of_isClosed (isClosed_eq hf hg) he

#print axioms oneSidedAbelKernel_row_L2_continuous
#print axioms oneSidedAbelColumn_sub_energy
#print axioms oneSidedAbelColumn_continuous
#print axioms oneSidedAbelKernel_output_continuous
#print axioms continuous_eq_on_measure_support

end QuantitativeMaass
