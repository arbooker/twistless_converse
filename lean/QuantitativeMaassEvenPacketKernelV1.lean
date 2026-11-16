module

public import QuantitativeMaassRadialAbelLocalEnergyV1
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual kernel outputs converge for every integrable input and every
centre. Compact overlap supplies the bound in the integration variable. -/
theorem radialShiftAbelKernel_output_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0))
    (v : ℍ → ℂ) (hv : Integrable v (quotientMeasure N)) (x : ℍ) :
    Tendsto (fun i => ∫ y,radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y*v y
      ∂quotientMeasure N) l
      (𝓝 (∫ y,radialPoincareKernel N (abelProfile F) x y*v y ∂quotientMeasure N)) := by
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  obtain ⟨D,_,hD⟩ := radialShiftAbelKernel_local_bound N F hF R hR hs x 0
  have hm (i : ι) : AEStronglyMeasurable (fun y =>
      radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y*v y)
      (quotientMeasure N) := by
    have h := radialPoincareKernel_joint_measurable N _ (abelProfile_smooth _
      (radialShiftApprox_smooth F hF _ (ha i)) (radialShiftApprox_compact F _ hz _ (ha i))).continuous
    exact (h.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul hv.aestronglyMeasurable
  have hb : ∀ᶠ i in l,∀ᵐ y ∂quotientMeasure N,
      ‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y*v y‖≤D*‖v y‖ := by
    filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with i hi
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hD _ (ha i) hi.le x (by simp) y) (norm_nonneg _)
  have hl : ∀ᵐ y ∂quotientMeasure N,Tendsto (fun i =>
      radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y*v y) l
      (𝓝 (radialPoincareKernel N (abelProfile F) x y*v y)) := by
    filter_upwards with y
    exact (radialShiftAbelKernel_tendsto l N F hF R hR hs a ha ha0 x y).mul_const (v y)
  exact tendsto_integral_filter_of_dominated_convergence (fun y => D*‖v y‖)
    (Eventually.of_forall hm) hb (hv.norm.const_mul D) hl

/-- A pointwise limit of chosen representatives identifies an L2 limit.
The almost-everywhere subsequence is extracted from proved convergence in measure. -/
theorem L2_limit_eq_pointwise_representatives {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (u : ℕ → Lp ℂ 2 μ) (w : Lp ℂ 2 μ)
    (hu : Tendsto u atTop (𝓝 w)) (g : ℕ → A → ℂ) (h : A → ℂ)
    (hg : ∀ n,u n=ᵐ[μ]g n) (hh : ∀ x,Tendsto (fun n => g n x) atTop (𝓝 (h x))) :
    w=ᵐ[μ]h := by
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  filter_upwards [hlim,ae_all_iff.mpr hg] with x hx he
  have heq : (fun n => (u (ns n)) x)=(fun n => g (ns n) x) := funext (fun n => he (ns n))
  rw [heq] at hx
  exact tendsto_nhds_unique hx ((hh x).comp hns.tendsto_atTop)

/-- The original even real smooth compact time packet has the literal
Abel-inverted periodized kernel, for every vector in the actual quotient
Hilbert space. No global smooth extension of the radial lift is assumed. -/
theorem evenWavePacket_kernel_coeFn (N : ℕ) [NeZero N]
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (v : AutomorphicSpace N) :
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) v).val=ᵐ[quotientMeasure N]
      (fun x => ∫ y,radialPoincareKernel N (abelProfile (evenCoshLift f)) x y*v.val y
        ∂quotientMeasure N) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f hf he hc
  have hz : ∀ q,Real.cosh R<q → F q=0 := evenCoshLift_zero_above f R hR hs
  have hsF : Function.support F⊆Iic (Real.cosh R) := by
    intro q hq
    by_contra hn
    exact hq (hz q (lt_of_not_ge hn))
  let P (n : ℕ) := abelKernelOperator N (radialShiftApprox F (a n))
    (radialShiftApprox_smooth F hF _ (ha n)) (radialShiftApprox_compact F _ hz _ (ha n))
    R hR (radialShiftApprox_upper_support F _ hz _ (ha n))
  have hP : Tendsto P atTop
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))) :=
    radialShiftAbelOperator_tendsto atTop N f hf he hc hr R hR hs a ha ha0
  have hv : Tendsto (fun n => (P n v).val) atTop
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) v).val) :=
    (AutomorphicSpace N).subtypeL.continuous.tendsto _ |>.comp
      ((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) v).continuous.tendsto _ |>.comp hP)
  apply L2_limit_eq_pointwise_representatives (quotientMeasure N) _ _ hv
    (fun n x => ∫ y,radialPoincareKernel N (abelProfile (radialShiftApprox F (a n))) x y*v.val y
      ∂quotientMeasure N)
  · intro n
    exact radialKernelOperator_coeFn N _ _ R hR _ v
  · intro x
    exact radialShiftAbelKernel_output_tendsto atTop N F hF R hR hsF a ha ha0 v.val
      ((Lp.memLp v.val).integrable (by norm_num)) x

#print axioms radialShiftAbelKernel_output_tendsto
#print axioms L2_limit_eq_pointwise_representatives
#print axioms evenWavePacket_kernel_coeFn

end QuantitativeMaass
