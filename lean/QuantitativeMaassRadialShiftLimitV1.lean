module

public import QuantitativeMaassRadialShiftApproxV1
public import QuantitativeMaassAbelSpectralIdentificationV1
public import QuantitativeMaassSmoothPacketTraceV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def radialShiftTime (f : ℝ → ℂ) (a t : ℝ) : ℂ :=
  radialShiftApprox (evenCoshLift f) a (Real.cosh t)

theorem radialShiftTime_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (a : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (radialShiftTime f a) :=
  (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) a ha).comp Real.contDiff_cosh

theorem radialShiftTime_support (f : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (a : ℝ) (ha : 0<a) :
    Function.support (radialShiftTime f a)⊆Icc (-R) R :=
  coshTimeTest_support _ R hR (radialShiftApprox_upper_support _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) a ha)

theorem radialShiftTime_compact (f : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (a : ℝ) (ha : 0<a) :
    HasCompactSupport (radialShiftTime f a) :=
  (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
    (closure_minimal (radialShiftTime_support f R hR hs a ha) isClosed_Icc)

theorem radialShiftTime_norm_le (f : ℝ → ℂ) (C : ℝ) (hC : ∀ x,‖f x‖≤C)
    (a : ℝ) (ha : 0<a) (t : ℝ) : ‖radialShiftTime f a t‖≤C := by
  unfold radialShiftTime
  rw [radialShiftApprox_eq_shift _ a _ ha (by linarith [Real.one_le_cosh t])]
  exact hC _

/-- Convergence in the weighted time norm that controls the WHOLE quotient
operator, including the exceptional spectrum. -/
theorem radialShiftTime_weighted_limit {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ t,‖radialShiftTime f (a i) t-f t‖*Real.cosh (|t|/2)) l (𝓝 0) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hC0 : 0≤C := (norm_nonneg (f 0)).trans (hC 0)
  let bound : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => 2*C*Real.cosh (R/2))
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hm (i : ι) : AEStronglyMeasurable
      (fun t => ‖radialShiftTime f (a i) t-f t‖*Real.cosh (|t|/2)) volume := by
    have ht := (radialShiftTime_smooth f hf he hc (a i) (ha i)).continuous
    exact (show Continuous _ by fun_prop).aestronglyMeasurable
  have hb (i : ι) : ∀ᵐ t ∂volume,
      ‖‖radialShiftTime f (a i) t-f t‖*Real.cosh (|t|/2)‖≤bound t := by
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.cosh_pos _).le)]
    by_cases ht : t∈Icc (-R) R
    · simp only [bound,indicator_of_mem ht]
      have hnorm := (norm_sub_le (radialShiftTime f (a i) t) (f t)).trans
        (add_le_add (radialShiftTime_norm_le f C hC (a i) (ha i) t) (hC t))
      have hcos : Real.cosh (|t|/2)≤Real.cosh (R/2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (div_nonneg (abs_nonneg t) (by norm_num)),
          abs_of_nonneg (div_nonneg hR (by norm_num))]
        exact div_le_div_of_nonneg_right (abs_le.mpr ht) (by norm_num)
      apply mul_le_mul (by linarith : ‖radialShiftTime f (a i) t-f t‖≤2*C) hcos
        (Real.cosh_pos _).le (mul_nonneg (by norm_num) hC0)
    · have hz : f t=0 := by by_contra hn; exact ht (hs hn)
      have hz' : radialShiftTime f (a i) t=0 := by
        by_contra hn
        exact ht (radialShiftTime_support f R hR hs (a i) (ha i) hn)
      simp only [bound,indicator_of_notMem ht,hz,hz',sub_self,norm_zero,zero_mul,le_refl]
  have hl : ∀ᵐ t ∂volume,Tendsto
      (fun i => ‖radialShiftTime f (a i) t-f t‖*Real.cosh (|t|/2)) l (𝓝 (0:ℝ)) := by
    filter_upwards with t
    have h := ((radialShiftApprox_cosh_tendsto l f hf he hc a ha ha0 t).sub_const (f t)).norm
    simpa only [radialShiftTime,sub_self,norm_zero,zero_mul] using h.mul_const (Real.cosh (|t|/2))
  have h := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hm) (Eventually.of_forall hb) hi hl
  simpa only [integral_zero] using h

/-- Actual bounded spectral operators converge in operator norm. -/
theorem radialShiftTime_packet_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => Wave.shiftedQuotientWavePacket N (radialShiftTime f (a i))
      (compactSmoothWaveWeight _ (radialShiftTime_smooth f hf he hc (a i) (ha i))
        (radialShiftTime_compact f R hR hs (a i) (ha i)))) l
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (f:=fun i => Wave.shiftedQuotientWavePacket N (radialShiftTime f (a i))
      (compactSmoothWaveWeight _ (radialShiftTime_smooth f hf he hc (a i) (ha i))
        (radialShiftTime_compact f R hR hs (a i) (ha i))))
    (b:=Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))).mpr
  apply squeeze_zero' _ _ (radialShiftTime_weighted_limit l f hf he hc R hR hs a ha ha0)
  · exact Eventually.of_forall (fun i => norm_nonneg
      (Wave.shiftedQuotientWavePacket N (radialShiftTime f (a i))
        (compactSmoothWaveWeight _ (radialShiftTime_smooth f hf he hc (a i) (ha i))
          (radialShiftTime_compact f R hR hs (a i) (ha i)))-
       Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)))
  · filter_upwards with i
    exact Wave.shiftedQuotientWavePacket_sub_norm N _ _ _ _
      (compactSmoothWaveWeight _ ((radialShiftTime_smooth f hf he hc (a i) (ha i)).sub hf)
        ((radialShiftTime_compact f R hR hs (a i) (ha i)).sub hc))

/-- Genuine smooth compact Abel kernels approximate the original even
packet in operator norm. This does not yet identify a pointwise limiting kernel. -/
theorem radialShiftAbelOperator_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => abelKernelOperator N (radialShiftApprox (evenCoshLift f) (a i))
      (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha i))
      (radialShiftApprox_compact _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i))
      R hR (radialShiftApprox_upper_support _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i))) l
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))) := by
  apply (radialShiftTime_packet_tendsto l N f hf he hc R hR hs a ha ha0).congr'
  filter_upwards with i
  symm
  exact abelKernelOperator_eq_coshWavePacket N _ _ _
    (radialShiftApprox_real _ (evenCoshLift_real f hr) (a i)) R hR _

/-- Each radial derivative has one bound before the approximation parameter
is chosen. The physical half-line is the only region entering Abel kernels. -/
theorem radialShiftApprox_uniform_derivative_bound (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : ∀ q,B<q → F q=0) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℝ,0<a → a≤1 → ∀ q : ℝ,1≤q →
      ‖iteratedDeriv k (radialShiftApprox F a) q‖≤C := by
  have hcont : ContinuousOn (iteratedDerivWithin k F (Ici 1)) (Icc 1 (B+1)) :=
    (hF.continuousOn_iteratedDerivWithin (m:=k) (by simp) (uniqueDiffOn_Ici (1:ℝ))).mono
      (fun _ hx => hx.1)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0+1,by positivity,?_⟩
  intro a ha ha1 q hq
  by_cases hqB : q≤B
  · rw [radialShiftApprox_iteratedDeriv F hF a ha q hq k]
    have h := hC (q+a) ⟨by linarith,by linarith⟩
    exact h.trans (by linarith [le_max_left C 0])
  · have heq : radialShiftApprox F a=ᶠ[𝓝 q] (fun _ => (0:ℂ)) := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hqB)] with x hx
      have hz := hB (x+a) (lt_trans hx (lt_add_of_pos_right x ha))
      simp only [radialShiftApprox,hz,mul_zero]
    rw [heq.iteratedDeriv_eq]
    simp only [iteratedDeriv_const,ite_self,norm_zero]
    positivity

#print axioms radialShiftApprox_uniform_derivative_bound

#print axioms radialShiftTime_smooth
#print axioms radialShiftTime_support
#print axioms radialShiftTime_compact
#print axioms radialShiftTime_norm_le
#print axioms radialShiftTime_weighted_limit
#print axioms radialShiftTime_packet_tendsto
#print axioms radialShiftAbelOperator_tendsto

end QuantitativeMaass
