module

public import AsymptoticRankMonotonicityV1
public import AsymptoticBlockLossV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap Filter AsymptoticPolarIsometry AsymptoticCornerKernel
open scoped lp ENNReal Topology

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- In a finite initial corner, divergent proportional losses force
each fixed regular defect to vanish on every subspace retained at all
stages. This avoids matching different residue classes into prime blocks.
The per-stage rank-loss inequalities remain explicit here. -/
theorem ae_annihilates_of_divergent_losses (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (P : ℕ → α → Submodule ℂ ℓ²(G,ℂ)) (U : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ n x,CompleteSpace (P n x)] [∀ x,CompleteSpace (U x)]
    (hUP : ∀ n x,U x≤P n x) (hP0 : ∀ n x,P n x≤P 0 x)
    (hmP : ∀ n g h,Measurable (fun x => matrix (P n x).starProjection g h))
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hcP : ∀ n,Covariant (fun x => (P n x).starProjection))
    (hcU : Covariant (fun x => (U x).starProjection))
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M)
    (hf : trace μ (fun x => (P 0 x).starProjection)<∞)
    (a : ℕ → ℝ) (ha : ∀ n,0≤a n)
    (hdiv : Tendsto (fun n => ∑ i∈Finset.range n,a i) atTop atTop)
    (hstep : ∀ n,
      (trace μ (fun x => ((T x).comp (P n x).starProjection).kerᗮ.starProjection)).toReal*a n≤
        (trace μ (fun x => (P n x).starProjection)).toReal-
          (trace μ (fun x => (P (n+1) x).starProjection)).toReal) :
    ∀ᵐ x ∂μ,∀ v∈U x,T x v=0 := by
  have huf : trace μ (fun x => ((T x).comp (U x).starProjection).kerᗮ.starProjection)<∞ :=
    projection_trace_finite_of_le μ _ (P 0) (fun x =>
      (support_le (U x) _ (restricted_comp_projection (U x) (T x))).trans (hUP 0 x)) hf
  have hnf (n : ℕ) : trace μ (fun x => ((T x).comp (P n x).starProjection).kerᗮ.starProjection)<∞ :=
    projection_trace_finite_of_le μ _ (P 0) (fun x =>
      (support_le (P n x) _ (restricted_comp_projection (P n x) (T x))).trans (hP0 n x)) hf
  have hmono (n : ℕ) := ENNReal.toReal_mono (hnf n).ne
    (restricted_rank_mono μ hmp U (P n) (hUP n) hmU (hmP n) hcU (hcP n) T hm hc M hM)
  have hz := AsymptoticBlockLoss.persistent_rank_zero
    (fun n => (trace μ (fun x => (P n x).starProjection)).toReal) a
    (trace μ (fun x => ((T x).comp (U x).starProjection).kerᗮ.starProjection)).toReal
    (fun _ => ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    (fun n => (mul_le_mul_of_nonneg_right (hmono n) (ha n)).trans (hstep n)) hdiv
  have hzero : trace μ (fun x => ((T x).comp (U x).starProjection).kerᗮ.starProjection)=0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right huf.ne
  have hae := ae_zero_of_support_trace_zero μ hmp (fun x => (T x).comp (U x).starProjection)
    (matrix_comp_measurable _ _ hm hmU) (covariant_comp _ _ hc hcU)
    M (fun x => (restricted_norm_le (U x) (T x)).trans (hM x)) hzero
  filter_upwards [hae] with x hx v hv
  have he := congrArg (fun B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => B v) hx
  simpa only [comp_apply,(U x).starProjection_eq_self_iff.mpr hv,zero_apply] using he

#print axioms ae_annihilates_of_divergent_losses

end AsymptoticRegularTrace
