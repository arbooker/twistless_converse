module

public import AsymptoticMixingRankV1
public import AsymptoticCornerKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open AsymptoticObservationStack AsymptoticPolarIsometry MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α ι : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem support_matrix_measurable (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) (g h : G) :
    Measurable (fun x => matrix (T x).kerᗮ.starProjection g h) := by
  have hp := (polar_regular T hm hc M hM).1
  simpa only [polar_gram] using matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hp) hp g h

theorem stack_support_matrix_measurable [Fintype ι]
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) (g h : G) :
    Measurable (fun x => matrix (stack (L x)).kerᗮ.starProjection g h) := by
  have hp := stack_polarRow_regular L hm hc M hM
  have hs := matrix_finsetSum_measurable Finset.univ _ (fun i _ =>
    matrix_comp_measurable _ _ (matrix_adjoint_measurable _ (hp i).1) (hp i).1) g h
  simpa only [polar_rows_gram] using hs

#print axioms support_matrix_measurable
#print axioms stack_support_matrix_measurable

end AsymptoticRegularTrace

namespace AsymptoticMixing

open AsymptoticSubgroupSupport AsymptoticObservationStack AsymptoticCornerKernel
open AsymptoticRegularTrace MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Fintype ι]

omit [Group G] [Fintype ι] in
theorem stack_comp_projection (P : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace P]
    (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hL : ∀ i,(L i).comp P.starProjection=L i) :
    (stack L).comp P.starProjection=stack L := by
  apply ContinuousLinearMap.ext
  intro v
  ext i : 1
  exact congrArg (fun B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => B v) (hL i)

theorem normalizedMixed_comp_projection (P : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace P]
    (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,(L i).comp P.starProjection=L i) :
    (normalizedMixed a L).comp P.starProjection=normalizedMixed a L := by
  rw [normalizedMixed,comp_assoc,stack_comp_projection P L hL]

variable [Countable G] [MeasurableSpace α] [MulAction G α]

/-- The one-prime operator inequality in the paper's finite-corner
form. Setting the row count to q-1 gives the exact loss factor. The
averaged equation and the individual defects are the actual kernels. -/
theorem corner_rank_loss (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S) (hι : 0<Fintype.card ι)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (hL : ∀ x i,Supported S (L x i)) (hP : ∀ x i,(L x i).comp (P x).starProjection=L x i)
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) (hf : trace μ (fun x => (P x).starProjection)<∞) :
    ((trace μ (fun x => (P x).starProjection)).toReal-
      (trace μ (fun x => (remaining (P x) (stack (L x))).starProjection)).toReal)/(Fintype.card ι:ℝ)≤
    (trace μ (fun x => (P x).starProjection)).toReal-
      (trace μ (fun x => (remaining (P x) (mixed a (L x))).starProjection)).toReal := by
  have hs := stack_support_matrix_measurable L hm hc M hM 1 1
  have hr := normalizedMixed_regular a L hm hc
  have hb := support_matrix_measurable _ hr.1 hr.2 M
    (fun x => (normalizedMixed_norm a (L x)).trans (hM x)) 1 1
  have hsp := fun x => stack_comp_projection (P x) (L x) (hP x)
  have hbp := fun x => normalizedMixed_comp_projection (P x) a (L x) (hP x)
  have hbf := projection_trace_finite_of_le μ (fun x => (normalizedMixed a (L x)).kerᗮ) P
    (fun x => support_le (P x) _ (hbp x)) hf
  have he := ENNReal.toReal_mono hbf.ne (normalizedMixed_rank_loss μ hmp S a ha L hm hc hL M hM)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    corner_removed_trace μ P _ hsp hs hf,corner_removed_trace μ P _ hbp hb hf] at he
  simpa only [remaining,normalizedMixed_ker a hι,div_eq_mul_inv,mul_comm] using he

#print axioms stack_comp_projection
#print axioms normalizedMixed_comp_projection
#print axioms corner_rank_loss

end AsymptoticMixing
