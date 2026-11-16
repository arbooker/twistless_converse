module

public import QuantitativeMaassParityKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- The original moving-window operator commutes with the actual reflection. -/
theorem windowWavePacket_reflection_commute (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Commute (reflectionIsometry N).toContinuousLinearMap (windowWavePacket N K hc R hR a b) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  exact evenWavePacket_reflection_commute N (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR)
    (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_real K he R a b)
    (B*R) (mul_nonneg hB.le hR.le) (hs R hR a b)

/-- Reflection commutation gives commutation with either parity projection. -/
theorem parityProjection_commute (N : ℕ) (σ : ℝ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : Commute (reflectionIsometry N).toContinuousLinearMap A) :
    Commute (parityProjection N σ) A := by
  apply ContinuousLinearMap.ext
  intro v
  have hh : reflectionIsometry N (A v)=A (reflectionIsometry N v) :=
    DFunLike.congr_fun hA v
  change parityProjection N σ (A v)=A (parityProjection N σ v)
  simp only [parityProjection_apply,map_smul,map_add,hh]

/-- The full geometric diagonal for the original window, at every centre. -/
theorem windowTimeSquare_kernel_split (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) :
    radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution
      (windowTimeSchwartz K hc R hR a b) (windowTimeSchwartz K hc R hR a b)))) x x=
      windowIdentityContribution K hc R hR a b+windowGeometricRemainder N K hc R hR a b x := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R := mul_nonneg hB.le hR.le
  apply radialPoincareKernel_diagonal_split N _ (B*R+B*R) (add_nonneg hBR hBR)
  exact abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (add_nonneg hBR hBR)
    (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))

/-- The original window's actual parity pretrace, including the factor one
half, the literal spherical identity, and both actual geometric errors. -/
theorem windowTimeSquare_parity_pretrace {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2)
        (((windowIdentityContribution K hc R hR a d).re+
          (windowGeometricRemainder N K hc R hR a d x).re+
          σ*(windowReflection N K hc R hR a d x).re)/2) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  have hp := timeSquare_parity_pretrace N b σ hσ (windowTimeSchwartz K hc R hR a d)
    (symmetricWindowTimeTest_compact K hc R a d hR)
    (symmetricWindowTimeTest_even K he R a d)
    (symmetricWindowTimeTest_real K he R a d)
    (B*R) (mul_nonneg hB.le hR.le) (hs R hR a d)
  filter_upwards [hp] with x hx
  rw [windowTimeSquare_kernel_split N K hc R hR a d x,Complex.add_re] at hx
  exact hx

/-- Tonelli transports the actual parity pretrace over any measurable or
nonmeasurable region, using the restricted measure on that region. -/
theorem windowTimeSquare_parity_restricted_trace {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (s : Set ℍ)
    (σ : ℝ) (hσ : σ^2=1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a d : ℝ) :
    (∑' i,∫⁻ x in s,ENNReal.ofReal
      (‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2)
      ∂quotientMeasure N)=
      ∫⁻ x in s,ENNReal.ofReal (((windowIdentityContribution K hc R hR a d).re+
        (windowGeometricRemainder N K hc R hR a d x).re+
        σ*(windowReflection N K hc R hR a d x).re)/2) ∂quotientMeasure N := by
  have hm (i : ι) : AEMeasurable (fun x => ENNReal.ofReal
      (‖(windowWavePacket N K hc R hR a d (parityProjection N σ (b i))).val x‖^2))
      ((quotientMeasure N).restrict s) :=
    ((Lp.stronglyMeasurable (windowWavePacket N K hc R hR a d
      (parityProjection N σ (b i))).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (windowTimeSquare_parity_pretrace N b σ hσ K he hc R hR a d)]
    with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]


#print axioms windowWavePacket_reflection_commute
#print axioms parityProjection_commute
#print axioms windowTimeSquare_kernel_split
#print axioms windowTimeSquare_parity_pretrace
#print axioms windowTimeSquare_parity_restricted_trace

end QuantitativeMaass
