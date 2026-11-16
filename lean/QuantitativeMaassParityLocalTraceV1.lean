module

public import QuantitativeMaassParityWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- The literal geometric parity density of the original window square. -/
def windowParityDensity (N : ℕ) (σ : ℝ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) (x : ℍ) : ℝ :=
  ((windowIdentityContribution K hc R hR a d).re+
    (windowGeometricRemainder N K hc R hR a d x).re+
    σ*(windowReflection N K hc R hR a d x).re)/2

/-- Exact positive column realization at every centre, not just almost everywhere. -/
theorem windowParityDensity_eq_column (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d D : ℝ) (hD : 0≤D)
    (hs : Function.support (symmetricWindowTimeTest K R a d)⊆Icc (-D) D) (x : ℍ) :
    windowParityDensity N σ K hc R hR a d x=
      ‖parityProjection N σ (timeAbelColumn N (windowTimeSchwartz K hc R hR a d)
        (symmetricWindowTimeTest_compact K hc R a d hR)
        (symmetricWindowTimeTest_even K he R a d) D hD hs x)‖^2 := by
  have hh := congrArg Complex.re (timeSquare_parity_energy N σ hσ
    (windowTimeSchwartz K hc R hR a d)
    (symmetricWindowTimeTest_compact K hc R a d hR)
    (symmetricWindowTimeTest_even K he R a d)
    (symmetricWindowTimeTest_real K he R a d) D hD hs x)
  rw [windowTimeSquare_kernel_split N K hc R hR a d x] at hh
  simp only [Complex.ofReal_re,Complex.div_ofNat_re,Complex.add_re,Complex.mul_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hh
  exact hh.symm

/-- Continuity and positivity of the actual combined geometric expression. -/
theorem windowParityDensity_continuous_nonneg (N : ℕ) [NeZero N] (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    Continuous (windowParityDensity N σ K hc R hR a d) ∧
      ∀ x,0≤windowParityDensity N σ K hc R hR a d x := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  have hBR : 0≤B*R := mul_nonneg hB.le hR.le
  let f := windowTimeSchwartz K hc R hR a d
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a d hR
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a d
  let c := timeAbelColumn N f hfc hfe (B*R) hBR (hs R hR a d)
  have hcont : Continuous c := oneSidedAbelColumn_continuous N _ _ _ _ _
  have hh : windowParityDensity N σ K hc R hR a d=(fun x => ‖parityProjection N σ (c x)‖^2) := by
    funext x
    exact windowParityDensity_eq_column N σ hσ K he hc R hR a d (B*R) hBR (hs R hR a d) x
  rw [hh]
  exact ⟨((parityProjection N σ).continuous.comp hcont).norm.pow 2,fun _ => sq_nonneg _⟩

/-- The actual local parity trace is finite on every compact region. -/
theorem windowParity_local_trace_finite {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (s : Set ℍ) (hs : IsCompact s) (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    (∑' i,∫⁻ x in s,ENNReal.ofReal
      (‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2)
      ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  rw [windowTimeSquare_parity_restricted_trace N b s σ hσ K he hc R hR a d]
  have hh := windowParityDensity_continuous_nonneg N σ hσ K he hc R hR a d
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hh.2)).mp
    (hh.1.continuousOn.integrableOn_compact hs).2

/-- The local parity trace is an ordinary absolutely convergent real sum,
and equals the integral of the literal geometric parity density. -/
theorem windowParity_local_real_trace {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (s : Set ℍ) (hs : IsCompact s) (σ : ℝ) (hσ : σ^2=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    HasSum (fun i => ∫ x in s,
      ‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2 ∂quotientMeasure N)
      (∫ x in s,windowParityDensity N σ K hc R hR a d x ∂quotientMeasure N) := by
  let F := fun i x => ‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2
  have hint (i : ι) : Integrable (F i) ((quotientMeasure N).restrict s) :=
    ((Lp.memLp (windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0)).restrict
  have hsum : Summable (fun i => ∫ x in s,F i x ∂quotientMeasure N) := by
    have h := ENNReal.summable_toReal (windowParity_local_trace_finite N b s hs σ hσ K he hc R hR a d).ne
    apply h.congr
    intro i
    symm
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _))
      (hint i).aestronglyMeasurable
  have hnorm : Summable (fun i => ∫ x in s,‖F i x‖ ∂quotientMeasure N) := by
    simpa only [F,Real.norm_eq_abs,abs_pow,abs_norm] using hsum
  have hh := hasSum_integral_of_summable_integral_norm hint hnorm
  have heq : (∫ x in s,∑' i,F i x ∂quotientMeasure N)=
      ∫ x in s,windowParityDensity N σ K hc R hR a d x ∂quotientMeasure N := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (windowTimeSquare_parity_pretrace N b σ hσ K he hc R hR a d)]
      with x hx
    exact hx.tsum_eq
  rw [heq] at hh
  exact hh

#print axioms windowParityDensity_eq_column
#print axioms windowParityDensity_continuous_nonneg
#print axioms windowParity_local_trace_finite
#print axioms windowParity_local_real_trace

end QuantitativeMaass
