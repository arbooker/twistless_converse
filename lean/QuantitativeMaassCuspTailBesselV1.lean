module

public import QuantitativeMaassCuspCenteredTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Continuous invariant representatives identify the actual infinite-tail
restriction of every quotient Hilbert vector. -/
theorem continuous_invariant_tail_restriction (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2≤Y) (v : AutomorphicSpace N) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (he : v.val=ᵐ[quotientMeasure N]f) :
    (cuspTailRestriction N W s Y hY v : ℍ → ℂ)=ᵐ[volume.restrict (cuspTailSet W Y)]
      (fun z => f (cuspAction s z)) := by
  have hm : f∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨hf.measurable,hinv,(memLp_congr_ae he).mp (Lp.memLp v.val)⟩
  let w : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨f,hm⟩
  have hw : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) w=v := by
    apply Subtype.ext
    apply Lp.ext
    exact hm.2.2.coeFn_toLp.trans he.symm
  rw [←hw]
  exact cuspTailRestriction_representative_ae N W s Y hY w

/-- Bessel on the infinite actual cusp tail, allowing removal of a proved
orthogonal column field. No trace-class premise is imposed. -/
theorem continuous_column_tail_centered_bessel {ι : Type*} (N W : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (s : SL(2,ℤ)) (Y : ℝ) (hY : 2≤Y)
    (m : ℍ → AutomorphicSpace N) (hm : ∀ x∈cuspTailSet W Y,∀ i,inner ℂ (m x) (v i)=0) :
    (∑' i,ENNReal.ofReal (‖cuspTailRestriction N W s Y hY (A (v i))‖^2))≤
      ∫⁻ x in cuspTailSet W Y,ENNReal.ofReal (‖c (cuspAction s x)-m x‖^2) := by
  classical
  have he (i : ι) : ENNReal.ofReal (‖cuspTailRestriction N W s Y hY (A (v i))‖^2)=
      ∫⁻ x in cuspTailSet W Y,ENNReal.ofReal (‖inner ℂ (c (cuspAction s x)) (v i)‖^2) := by
    rw [lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [continuous_invariant_tail_restriction N W s Y hY (A (v i)) _
      (hc.inner continuous_const) (fun γ z => by rw [hinv]) (hrep (v i))] with x hx
    rw [hx]
  simp_rw [he]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro S
  have hmeas (i : ι) : Measurable (fun x => ENNReal.ofReal (‖inner ℂ (c (cuspAction s x)) (v i)‖^2)) :=
    (((hc.comp (cuspAction_continuous s)).inner continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [←lintegral_finsetSum (μ:=volume.restrict (cuspTailSet W Y)) S (fun i _ => hmeas i)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (cuspTailSet_measurable W Y)] with x hx
  change (∑ i∈S,ENNReal.ofReal (‖inner ℂ (c (cuspAction s x)) (v i)‖^2))≤
    ENNReal.ofReal (‖c (cuspAction s x)-m x‖^2)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (centered_column_bessel v hv _ _ (hm x hx) S)

/-- The actual window packet satisfies the full cusp-tail Bessel inequality,
with its literal period mean removed internally. -/
theorem windowWavePacket_tail_centered_bessel {ι : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i,v i∈localCuspidalSpace N hN) (s : SL(2,ℤ)) (Y : ℝ) (hY : 2≤Y) :
    (∑' i,ENNReal.ofReal (‖cuspTailRestriction N N s Y hY
      (windowWavePacket N K hc R hR a b (v i))‖^2))≤
      ∫⁻ z in cuspTailSet N Y,ENNReal.ofReal (‖windowAbelColumn N K he hc R hR a b (cuspAction s z)-
        cuspColumnMean N (windowAbelColumn N K he hc R hR a b) s (Real.log z.im)‖^2) := by
  apply continuous_column_tail_centered_bessel N N _ _
    (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowAbelColumn_packet_coeFn N K he hc R hR a b) v hv s Y hY
  intro z _ i
  exact windowAbelColumn_mean_orthogonal N hN K he hc R hR a b s (Real.log z.im) (v i) (hcus i)

#print axioms continuous_invariant_tail_restriction
#print axioms continuous_column_tail_centered_bessel
#print axioms windowWavePacket_tail_centered_bessel

end QuantitativeMaass
