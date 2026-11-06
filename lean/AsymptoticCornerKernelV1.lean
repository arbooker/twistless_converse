module

public import AsymptoticPolarRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCornerKernel

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- The kernel left inside a closed terminal subspace. -/
def remaining (P : Submodule ℂ H) (T : H →L[ℂ] J) : Submodule ℂ H := P ⊓ T.ker

instance remaining_complete (P : Submodule ℂ H) [CompleteSpace P] (T : H →L[ℂ] J) :
    CompleteSpace (remaining P T) := by
  have hp : IsClosed (P : Set H) :=
    (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace P)).isClosed
  exact (hp.inter T.isClosed_ker).completeSpace_coe

omit [CompleteSpace H] in
theorem support_le (P : Submodule ℂ H) [CompleteSpace P] (T : H →L[ℂ] J)
    (hT : T.comp P.starProjection=T) : T.kerᗮ≤P := by
  have hk : Pᗮ≤T.ker := by
    intro v hv
    change T v=0
    have he := congrArg (fun B : H →L[ℂ] J => B v) hT
    change T (P.starProjection v)=T v at he
    rw [P.starProjection_apply_eq_zero_iff.mpr hv,map_zero] at he
    exact he.symm
  simpa only [Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le hk

/-- The removed projection is exactly the source support, including
operators with nonclosed range. -/
theorem remaining_projection (P : Submodule ℂ H) [CompleteSpace P] (T : H →L[ℂ] J)
    (hT : T.comp P.starProjection=T) :
    (remaining P T).starProjection=P.starProjection-T.kerᗮ.starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · constructor
    · exact P.sub_mem (P.starProjection_apply_mem v)
        (support_le P T hT (T.kerᗮ.starProjection_apply_mem v))
    · change T (P.starProjection v-T.kerᗮ.starProjection v)=0
      have he := congrArg (fun B : H →L[ℂ] J => B v) hT
      change T (P.starProjection v)=T v at he
      have hs := T.kerᗮ.sub_starProjection_mem_orthogonal v
      rw [Submodule.orthogonal_orthogonal] at hs
      change T (v-T.kerᗮ.starProjection v)=0 at hs
      simpa only [map_sub,he] using hs
  · intro w hw
    change ⟪v-(P.starProjection v-T.kerᗮ.starProjection v),w⟫_ℂ=0
    rw [sub_sub_eq_add_sub,add_sub_right_comm,inner_add_left,
      P.starProjection_inner_eq_zero v w hw.1,zero_add]
    exact inner_eq_zero_symm.mp ((T.kerᗮ.starProjection_apply_mem v) w hw.2)

#print axioms support_le
#print axioms remaining_projection

end AsymptoticCornerKernel

namespace AsymptoticRegularTrace

open AsymptoticCornerKernel MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

variable {G α J : Type*} [Group G] [MeasurableSpace α]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- Additivity inside a finite or infinite terminal corner. Only root
measurability is required; no finite-dimensional rank formula is used. -/
theorem corner_trace_add (μ : Measure α)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (T : α → ℓ²(G,ℂ) →L[ℂ] J) (hT : ∀ x,(T x).comp (P x).starProjection=T x)
    (hm : Measurable (fun x => matrix (T x).kerᗮ.starProjection 1 1)) :
    trace μ (fun x => (P x).starProjection)=
      trace μ (fun x => (remaining (P x) (T x)).starProjection)+
        trace μ (fun x => (T x).kerᗮ.starProjection) := by
  have he (x : α) : (matrix (P x).starProjection 1 1).re=
      (matrix (remaining (P x) (T x)).starProjection 1 1).re+
        (matrix (T x).kerᗮ.starProjection 1 1).re := by
    rw [remaining_projection (P x) (T x) (hT x)]
    change Complex.reCLM (matrixCLM 1 1 (P x).starProjection)=
      Complex.reCLM (matrixCLM 1 1 ((P x).starProjection-(T x).kerᗮ.starProjection))+_
    rw [map_sub,map_sub]
    exact (sub_add_cancel _ _).symm
  have hadd (x : α) : ENNReal.ofReal (matrix (P x).starProjection 1 1).re=
      ENNReal.ofReal (matrix (remaining (P x) (T x)).starProjection 1 1).re+
        ENNReal.ofReal (matrix (T x).kerᗮ.starProjection 1 1).re := by
    rw [he]
    apply ENNReal.ofReal_add <;> rw [projection_root_eq_norm] <;> positivity
  unfold trace
  simp_rw [hadd]
  exact lintegral_add_right _ ((Complex.continuous_re.measurable.comp hm).ennreal_ofReal)

/-- The support dimension equals the trace removed from the terminal
kernel. Finiteness follows from inclusion in the given terminal corner. -/
theorem corner_removed_trace (μ : Measure α)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (P x)]
    (T : α → ℓ²(G,ℂ) →L[ℂ] J) (hT : ∀ x,(T x).comp (P x).starProjection=T x)
    (hm : Measurable (fun x => matrix (T x).kerᗮ.starProjection 1 1))
    (hf : trace μ (fun x => (P x).starProjection)<∞) :
    (trace μ (fun x => (T x).kerᗮ.starProjection)).toReal=
      (trace μ (fun x => (P x).starProjection)).toReal-
        (trace μ (fun x => (remaining (P x) (T x)).starProjection)).toReal := by
  have hs := projection_trace_finite_of_le μ (fun x => (T x).kerᗮ) P
    (fun x => support_le (P x) (T x) (hT x)) hf
  have hr := projection_trace_finite_of_le μ (fun x => remaining (P x) (T x)) P
    (fun _ => inf_le_left) hf
  have he := congrArg ENNReal.toReal (corner_trace_add μ P T hT hm)
  rw [ENNReal.toReal_add hr.ne hs.ne] at he
  linarith

#print axioms corner_trace_add
#print axioms corner_removed_trace

end AsymptoticRegularTrace
