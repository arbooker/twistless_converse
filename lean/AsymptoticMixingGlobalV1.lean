module

public import AsymptoticMixingCornerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCornerKernel

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

def globalRemaining (P : Submodule ℂ H) (T : ℕ → H →L[ℂ] J) : Submodule ℂ H :=
  ⨅ n,remaining P (T n)

instance globalRemaining_complete (P : Submodule ℂ H) [CompleteSpace P] (T : ℕ → H →L[ℂ] J) :
    CompleteSpace (globalRemaining P T) := by
  have hc : IsClosed (globalRemaining P T : Set H) := by
    change IsClosed ((⨅ n,remaining P (T n) : Submodule ℂ H) : Set H)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun n =>
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (remaining P (T n)))).isClosed)
  exact hc.completeSpace_coe

end AsymptoticCornerKernel

namespace AsymptoticRegularTrace

open AsymptoticCornerKernel MeasureTheory Filter ContinuousLinearMap
open scoped lp Topology ENNReal

variable {G α J : Type*} [Group G] [MeasurableSpace α]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

theorem remaining_root_measurable (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (T : α → ℓ²(G,ℂ) →L[ℂ] J) (hT : ∀ x,(T x).comp (P x).starProjection=T x)
    (hp : Measurable (fun x => matrix (P x).starProjection 1 1))
    (hs : Measurable (fun x => matrix (T x).kerᗮ.starProjection 1 1)) :
    Measurable (fun x => matrix (remaining (P x) (T x)).starProjection 1 1) := by
  have he (x : α) : matrix (remaining (P x) (T x)).starProjection 1 1=
      matrix (P x).starProjection 1 1-matrix (T x).kerᗮ.starProjection 1 1 := by
    rw [remaining_projection (P x) (T x) (hT x)]
    exact map_sub (matrixCLM 1 1) _ _
  simp only [he]
  exact hp.sub hs

theorem remaining_trace_tendsto (μ : Measure α)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (T : ℕ → α → ℓ²(G,ℂ) →L[ℂ] J)
    (ha : ∀ x,Antitone (fun n => remaining (P x) (T n x)))
    (hm : ∀ n,Measurable (fun x => matrix (remaining (P x) (T n x)).starProjection 1 1))
    (hf : trace μ (fun x => (P x).starProjection)<∞) :
    Tendsto (fun n => (trace μ (fun x => (remaining (P x) (T n x)).starProjection)).toReal) atTop
      (𝓝 (trace μ (fun x => (globalRemaining (P x) (fun n => T n x)).starProjection)).toReal) := by
  let : ∀ x,CompleteSpace (⨅ n,remaining (P x) (T n x) : Submodule ℂ ℓ²(G,ℂ)) :=
    fun x => inferInstanceAs (CompleteSpace (globalRemaining (P x) (fun n => T n x)))
  exact trace_toReal_tendsto_antitone_projections μ _ ha hm
    (projection_trace_finite_of_le μ _ P (fun _ => inf_le_left) hf)

#print axioms remaining_root_measurable
#print axioms remaining_trace_tendsto

end AsymptoticRegularTrace

namespace AsymptoticMixing

open AsymptoticSubgroupSupport AsymptoticObservationStack AsymptoticCornerKernel
open AsymptoticRegularTrace MeasureTheory Filter ContinuousLinearMap
open scoped lp Topology ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι] [MeasurableSpace α] [MulAction G α]

/-- Normality passes the proved finite-observation rank estimate to
the global kernels, defined as intersections of decreasing observation
kernels. Bounds may depend on the compact observation index. -/
theorem global_rank_loss (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S) (hι : 0<Fintype.card ι)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (hp : Measurable (fun x => matrix (P x).starProjection 1 1))
    (L : ℕ → α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ n i g h,Measurable (fun x => matrix (L n x i) g h))
    (hc : ∀ n i,Covariant (fun x => L n x i))
    (hL : ∀ n x i,Supported S (L n x i))
    (hP : ∀ n x i,(L n x i).comp (P x).starProjection=L n x i)
    (M : ℕ → ℝ) (hM : ∀ n x,‖stack (L n x)‖≤M n)
    (hs : ∀ x,Antitone (fun n => remaining (P x) (stack (L n x))))
    (hb : ∀ x,Antitone (fun n => remaining (P x) (mixed a (L n x))))
    (hf : trace μ (fun x => (P x).starProjection)<∞) :
    ((trace μ (fun x => (P x).starProjection)).toReal-
      (trace μ (fun x => (globalRemaining (P x) (fun n => stack (L n x))).starProjection)).toReal)/
      (Fintype.card ι:ℝ)≤
    (trace μ (fun x => (P x).starProjection)).toReal-
      (trace μ (fun x => (globalRemaining (P x) (fun n => mixed a (L n x))).starProjection)).toReal := by
  have hsm (n : ℕ) := remaining_root_measurable P (fun x => stack (L n x))
    (fun x => stack_comp_projection (P x) (L n x) (hP n x)) hp
    (stack_support_matrix_measurable (L n) (hm n) (hc n) (M n) (hM n) 1 1)
  have hbm (n : ℕ) : Measurable (fun x => matrix (remaining (P x) (mixed a (L n x))).starProjection 1 1) := by
    have hr := normalizedMixed_regular a (L n) (hm n) (hc n)
    have hn := support_matrix_measurable _ hr.1 hr.2 (M n)
      (fun x => (normalizedMixed_norm a (L n x)).trans (hM n x)) 1 1
    have he := remaining_root_measurable P (fun x => normalizedMixed a (L n x))
      (fun x => normalizedMixed_comp_projection (P x) a (L n x) (hP n x)) hp hn
    simpa only [remaining,normalizedMixed_ker a hι] using he
  have hst := remaining_trace_tendsto μ P (fun n x => stack (L n x)) hs hsm hf
  have hbt := remaining_trace_tendsto μ P (fun n x => mixed a (L n x)) hb hbm hf
  exact le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub hst).div_const (Fintype.card ι:ℝ))
    (tendsto_const_nhds.sub hbt)
    (fun n => corner_rank_loss μ hmp S a ha hι P (L n) (hm n) (hc n) (hL n) (hP n) (M n) (hM n) hf)

#print axioms global_rank_loss

end AsymptoticMixing
