module

public import QuantitativeMaassTranslatedHeckeGrowingV1
public import QuantitativeMaassMixedTraceLinearV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace QuantitativeMaass

/-- Quantitative local trace comparison for every translated Hecke
monomial. The constants precede both the word length and the time shift. -/
theorem upperTranslatedWindowKernel_volume_trace_error
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t → ∀ (S : Set ℍ),IsCompact S → S⊆Metric.closedBall o L → ∀ n : ℕ,
      |(∫ z in S,(upperTranslatedWindowKernel τ N p K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) n HeckeUpper.root z).re ∂volume)-
        volume.real S*
          ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
            (translatedWindowIdentity τ K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re)|≤
        (heckeWordErrorGrowth p)^n*C*(1+|τ|)*Real.sqrt t*ε^2*Real.exp (A*R+30*L+10*|τ|) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := upperTranslatedWindowRemainder_growing_bound K he hc o
  refine ⟨A,C*3^40,hA,by positivity,?_⟩
  intro τ N p _ _ L R ε t hR hL hε hε1 ht S hS hSL n
  let μ : Measure ℍ := volume
  let F := upperTranslatedWindowRemainder τ N p K hc R
    (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) n HeckeUpper.root
  let c := (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
    (translatedWindowIdentity τ K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re
  have hr : 0<HeckeUpper.root.matrix.det := by
    norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det]
  have hf : Continuous F := upperTranslatedWindowRemainder_continuous τ N p K he hc R _ _ _ n _ hr
  have hfi : IntegrableOn F S μ := hf.continuousOn.integrableOn_compact hS
  have hfri : IntegrableOn (fun z => (F z).re) S μ :=
    (Complex.continuous_re.comp hf).continuousOn.integrableOn_compact hS
  have hfv : IntegrableOn F (Metric.closedBall o L) volume := hf.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have heq : (fun z => (upperTranslatedWindowKernel τ N p K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) n HeckeUpper.root z).re)=fun z => c+(F z).re := by
    funext z
    rw [upperTranslatedWindowKernel_split τ N p K hc R _ _ _ n _ hr z,
      HeckeUpper.rawWalks_root_eq_tree]
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,←Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,zero_add,sub_zero]
    rfl
  have hci : IntegrableOn (fun _ : ℍ => c) S μ := continuous_const.continuousOn.integrableOn_compact hS
  rw [heq]
  change |(∫ z in S,c+(F z).re ∂μ)-μ.real S*c|≤_
  rw [integral_add hci hfri,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,
    add_sub_cancel_left]
  calc
    _ ≤ ∫ z in S,‖(F z).re‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ:=μ.restrict S) (fun z => (F z).re)
    _ ≤ ∫ z in S,‖F z‖ ∂μ := integral_mono hfri.norm hfi.norm
      (fun z => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (F z))
    _ ≤ ∫ z in Metric.closedBall o L,‖F z‖ := integral_mono_measure
      (Measure.restrict_mono_set volume hSL)
      (Eventually.of_forall (fun z => norm_nonneg (F z))) hfv.norm
    _ ≤ _ := by
      have hh := hbound τ N p L R ε t hR hL hε hε1 ht n HeckeUpper.root hr
      have hrh : integralMatrixHeight HeckeUpper.root.matrix=3 := by
        norm_num [integralMatrixHeight,HeckeUpper.matrix,HeckeUpper.root]
      rw [hrh] at hh
      convert hh using 1
      ring

#print axioms upperTranslatedWindowKernel_volume_trace_error
end QuantitativeMaass
