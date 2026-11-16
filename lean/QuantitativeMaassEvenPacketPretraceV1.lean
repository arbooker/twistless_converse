module

public import QuantitativeMaassEvenPacketKernelV1
public import QuantitativeMaassRadialPretraceV1
public import QuantitativeMaassWindowTimeRealizationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

theorem oneSidedAbelKernel_joint_measurable (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    Measurable (fun p : ℍ×ℍ => radialPoincareKernel N (abelProfile F) p.1 p.2) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  apply measurable_of_tendsto_metrizable
    (fun n => radialPoincareKernel_joint_measurable N _ (abelProfile_smooth _
      (radialShiftApprox_smooth F hF _ (ha n)) (radialShiftApprox_compact F _ hz _ (ha n))).continuous)
  exact tendsto_pi_nhds.mpr (fun p => radialShiftAbelKernel_tendsto atTop N F hF R hR hs a ha ha0 p.1 p.2)

/-- The literal limiting kernel has a common bound on every compact set of centres. -/
theorem oneSidedAbelKernel_local_bound (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (o : ℍ) (L : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ x : ℍ,dist x o≤L → ∀ y : ℍ,
      ‖radialPoincareKernel N (abelProfile F) x y‖≤D := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨D,hD,hbound⟩ := radialShiftAbelKernel_local_bound N F hF R hR hs o L
  refine ⟨D,hD,?_⟩
  intro x hx y
  apply le_of_tendsto (radialShiftAbelKernel_tendsto atTop N F hF R hR hs a ha ha0 x y).norm
  filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with n hn
  exact hbound _ (ha n) hn.le x hx y

/-- Kernel rows are genuine invariant quotient L2 functions, even when the
radial test is only smooth on the physical half-line. -/
theorem oneSidedAbelKernel_representative (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    radialPoincareKernel N (abelProfile F) x∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
  have hm : Measurable (radialPoincareKernel N (abelProfile F) x) :=
    Measurable.of_uncurry_left (f:=radialPoincareKernel N (abelProfile F))
      (oneSidedAbelKernel_joint_measurable N F hF R hR hs)
  obtain ⟨D,_,hb⟩ := oneSidedAbelKernel_local_bound N F hF R hR hs x 0
  refine ⟨hm,?_,MemLp.of_bound hm.aestronglyMeasurable D (Eventually.of_forall (hb x (by simp)))⟩
  intro γ y
  exact radialPoincareKernel_invariant N (abelProfile F) x y γ

def oneSidedAbelColumn (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) : AutomorphicSpace N :=
  AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)
    ⟨_,oneSidedAbelKernel_representative N F hF R hR hs x⟩

theorem oneSidedAbelColumn_coeFn (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    (oneSidedAbelColumn N F hF R hR hs x).val=ᵐ[quotientMeasure N]
      radialPoincareKernel N (abelProfile F) x :=
  (oneSidedAbelKernel_representative N F hF R hR hs x).2.2.coeFn_toLp

theorem oneSidedAbelColumn_inner (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (x : ℍ) (v : AutomorphicSpace N) :
    inner ℂ (oneSidedAbelColumn N F hF R hR hs x) v=
      ∫ y,radialPoincareKernel N (abelProfile F) x y*v.val y ∂quotientMeasure N := by
  change inner ℂ (oneSidedAbelColumn N F hF R hR hs x).val v.val=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneSidedAbelColumn_coeFn N F hF R hR hs x] with y hy
  rw [hy,RCLike.inner_apply]
  change v.val y*star (radialPoincareKernel N (abelProfile F) x y)=_
  rw [radialPoincareKernel_star N _ (abelProfile_real F hr),mul_comm]

theorem oneSidedAbelColumn_energy (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    ‖oneSidedAbelColumn N F hF R hR hs x‖^2=
      ∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N := by
  change ‖(oneSidedAbelColumn N F hF R hR hs x).val‖^2=_
  rw [← inner_self_eq_norm_sq (𝕜:=ℝ),L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [oneSidedAbelColumn_coeFn N F hF R hR hs x] with y hy
  rw [hy]

/-- Parseval for the literal one-sided Abel kernel. -/
theorem oneSidedAbelKernel_parseval {ι : Type*} (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    HasSum (fun i => ‖∫ y,radialPoincareKernel N (abelProfile F) x y*(b i).val y
      ∂quotientMeasure N‖^2) (∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N) := by
  have h := hasSum_inner_norm_sq b (oneSidedAbelColumn N F hF R hR hs x)
  simp_rw [oneSidedAbelColumn_inner N F hF hr R hR hs x] at h
  rw [oneSidedAbelColumn_energy] at h
  exact h

/-- Pretrace for the ORIGINAL even compact time packet, including time zero.
The identity is obtained from the actual kernel rows and Hilbert Parseval. -/
theorem evenWavePacket_pretrace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x‖^2)
        (∫ y,‖radialPoincareKernel N (abelProfile (evenCoshLift f)) x y‖^2 ∂quotientMeasure N) := by
  have hrep : ∀ᵐ x ∂quotientMeasure N,∀ i,
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x=
        ∫ y,radialPoincareKernel N (abelProfile (evenCoshLift f)) x y*(b i).val y ∂quotientMeasure N :=
    ae_all_iff.mpr (fun i => evenWavePacket_kernel_coeFn N f hf he hc hr R hR hs (b i))
  have hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R) := by
    intro q hq
    by_contra hn
    exact hq (evenCoshLift_zero_above f R hR hs q (lt_of_not_ge hn))
  filter_upwards [hrep] with x hx
  simp_rw [hx]
  exact oneSidedAbelKernel_parseval N b _ (evenCoshLift_smoothOn f hf he hc)
    (evenCoshLift_real f hr) R hR hsF x


theorem oneSidedAbelColumn_lintegral (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    ENNReal.ofReal (∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N)=
      ∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N (abelProfile F) x y‖^2) ∂quotientMeasure N := by
  rw [← oneSidedAbelColumn_energy N F hF R hR hs x,automorphic_norm_square_lintegral]
  apply lintegral_congr_ae
  filter_upwards [oneSidedAbelColumn_coeFn N F hF R hR hs x] with y hy
  rw [hy]

/-- The localized energy trace identity for the original packet, with no
smooth-extension or trace-formula hypothesis. The region may be arbitrary. -/
theorem evenWavePacket_restricted_energy_trace {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (s : Set ℍ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∑' i,∫⁻ x in s,ENNReal.ofReal
      (‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x‖^2)
      ∂quotientMeasure N)=
      ∫⁻ x in s,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N (abelProfile (evenCoshLift f)) x y‖^2)
        ∂quotientMeasure N ∂quotientMeasure N := by
  have hm (i : ι) : AEMeasurable
      (fun x => ENNReal.ofReal
        (‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x‖^2))
      ((quotientMeasure N).restrict s) :=
    ((Lp.stronglyMeasurable (Wave.shiftedQuotientWavePacket N f
      (compactSmoothWaveWeight f hf hc) (b i)).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R) := by
    intro q hq
    by_contra hn
    exact hq (evenCoshLift_zero_above f R hR hs q (lt_of_not_ge hn))
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (evenWavePacket_pretrace N b f hf he hc hr R hR hs)] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]
  exact oneSidedAbelColumn_lintegral N _ (evenCoshLift_smoothOn f hf he hc) R hR hsF x

/-- Actual local geometric energy is finite. This supplies finiteness and
not a quantitative bound as the support radius grows. -/
theorem oneSidedAbelKernel_local_energy_finite (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (o : ℍ) (L : ℝ) :
    (∫⁻ x in Metric.closedBall o L,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N (abelProfile F) x y‖^2)
      ∂quotientMeasure N ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  obtain ⟨D,hD,hbound⟩ := oneSidedAbelKernel_local_bound N F hF R hR hs o L
  have hb : (∫⁻ x in Metric.closedBall o L,∫⁻ y,ENNReal.ofReal
      (‖radialPoincareKernel N (abelProfile F) x y‖^2) ∂quotientMeasure N ∂quotientMeasure N)≤
      (∫⁻ _x in Metric.closedBall o L,∫⁻ _y,ENNReal.ofReal (D^2)
        ∂quotientMeasure N ∂quotientMeasure N) := by
    apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
    intro x hx
    apply lintegral_mono
    intro y
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hbound x hx y) 2)
  apply hb.trans_lt
  simp only [lintegral_const,Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
    (measure_lt_top _ _)

theorem evenWavePacket_local_energy_finite {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (o : ℍ) (L : ℝ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∑' i,∫⁻ x in Metric.closedBall o L,ENNReal.ofReal
      (‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x‖^2)
      ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  rw [evenWavePacket_restricted_energy_trace N b _ f hf he hc hr R hR hs]
  apply oneSidedAbelKernel_local_energy_finite N _ (evenCoshLift_smoothOn f hf he hc) R hR
  intro q hq
  by_contra hn
  exact hq (evenCoshLift_zero_above f R hR hs q (lt_of_not_ge hn))

theorem evenWavePacket_local_energy_summable {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (o : ℍ) (L : ℝ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Summable (fun i => ∫ x in Metric.closedBall o L,
      ‖(Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) (b i)).val x‖^2
      ∂quotientMeasure N) := by
  have h := ENNReal.summable_toReal (evenWavePacket_local_energy_finite N b o L f hf he hc hr R hR hs).ne
  apply h.congr
  intro i
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Eventually.of_forall (fun _ => sq_nonneg _)
  · exact ((Lp.stronglyMeasurable (Wave.shiftedQuotientWavePacket N f
      (compactSmoothWaveWeight f hf hc) (b i)).val).norm.pow 2).aestronglyMeasurable


/-- Concrete geometric realization of the constructed moving window packet:
the literal kernel, exact restricted energy identity, and finite local energy
are all conclusions. No radial lift or kernel identity is supplied by the caller. -/
theorem windowWavePacket_geometric_realization {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (basis : HilbertBasis ι ℂ (AutomorphicSpace N))
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) :
    let g := abelProfile (evenCoshLift (symmetricWindowTimeTest K R a b))
    (∀ v : AutomorphicSpace N,(windowWavePacket N K hc R hR a b v).val=ᵐ[quotientMeasure N]
      (fun x => ∫ y,radialPoincareKernel N g x y*v.val y ∂quotientMeasure N)) ∧
    (∀ s : Set ℍ,(∑' i,∫⁻ x in s,ENNReal.ofReal
      (‖(windowWavePacket N K hc R hR a b (basis i)).val x‖^2) ∂quotientMeasure N)=
      ∫⁻ x in s,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2)
        ∂quotientMeasure N ∂quotientMeasure N) ∧
    (∀ (o : ℍ) (L : ℝ),Summable (fun i => ∫ x in Metric.closedBall o L,
      ‖(windowWavePacket N K hc R hR a b (basis i)).val x‖^2 ∂quotientMeasure N)) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  have hBR : 0≤B*R := (mul_pos hB hR).le
  refine ⟨?_,?_,?_⟩
  · intro v
    exact evenWavePacket_kernel_coeFn N _ (symmetricWindowTimeTest_smooth K R a b)
      (symmetricWindowTimeTest_even K he R a b) (symmetricWindowTimeTest_compact K hc R a b hR)
      (symmetricWindowTimeTest_real K he R a b) (B*R) hBR (hs R hR a b) v
  · intro s
    exact evenWavePacket_restricted_energy_trace N basis s _ (symmetricWindowTimeTest_smooth K R a b)
      (symmetricWindowTimeTest_even K he R a b) (symmetricWindowTimeTest_compact K hc R a b hR)
      (symmetricWindowTimeTest_real K he R a b) (B*R) hBR (hs R hR a b)
  · intro o L
    exact evenWavePacket_local_energy_summable N basis o L _ (symmetricWindowTimeTest_smooth K R a b)
      (symmetricWindowTimeTest_even K he R a b) (symmetricWindowTimeTest_compact K hc R a b hR)
      (symmetricWindowTimeTest_real K he R a b) (B*R) hBR (hs R hR a b)

#print axioms windowWavePacket_geometric_realization

#print axioms oneSidedAbelColumn_lintegral
#print axioms evenWavePacket_restricted_energy_trace
#print axioms oneSidedAbelKernel_local_energy_finite
#print axioms evenWavePacket_local_energy_finite
#print axioms evenWavePacket_local_energy_summable

#print axioms oneSidedAbelKernel_joint_measurable
#print axioms oneSidedAbelKernel_local_bound
#print axioms oneSidedAbelKernel_representative
#print axioms oneSidedAbelColumn_coeFn
#print axioms oneSidedAbelColumn_inner
#print axioms oneSidedAbelColumn_energy
#print axioms oneSidedAbelKernel_parseval
#print axioms evenWavePacket_pretrace

end QuantitativeMaass
