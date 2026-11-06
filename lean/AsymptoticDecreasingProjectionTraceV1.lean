module

public import AsymptoticRegularStrongTraceV1
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticStrongConvergence

open Filter ContinuousLinearMap
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Decreasing closed subspaces have strongly convergent orthogonal
projections; the limit projects onto their intersection. -/
theorem antitone_projection_tendsto (U : ℕ → Submodule ℂ H)
    [∀ n,CompleteSpace (U n)] [CompleteSpace (⨅ n,U n : Submodule ℂ H)] (hU : Antitone U) (x : H) :
    Tendsto (fun n => (U n).starProjection x) atTop (𝓝 ((⨅ n,U n).starProjection x)) := by
  have hm : Monotone (fun n => (U n)ᗮ) := fun _ _ hij => Submodule.orthogonal_le (hU hij)
  have he : (⨆ n,(U n)ᗮ).topologicalClosure=(⨅ n,U n)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,← Submodule.iInf_orthogonal]
    simp only [Submodule.orthogonal_orthogonal]
  have ht := Submodule.starProjection_tendsto_closure_iSup (fun n => (U n)ᗮ) hm x
  simp only [he,Submodule.starProjection_orthogonal,sub_apply,id_apply] at ht
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub ht
  simpa only [sub_sub_cancel] using hh

omit [CompleteSpace H] in
theorem projection_norm_le_of_le (U V : Submodule ℂ H) [CompleteSpace U] [CompleteSpace V]
    (hUV : U≤V) (x : H) : ‖U.starProjection x‖≤‖V.starProjection x‖ := by
  have he := congrArg (fun T : H →L[ℂ] H => T x) (Submodule.starProjection_comp_starProjection_of_le hUV)
  change U.starProjection (V.starProjection x)=U.starProjection x at he
  rw [← he]
  exact U.norm_starProjection_apply_le (V.starProjection x)

#print axioms antitone_projection_tendsto
#print axioms projection_norm_le_of_le

end AsymptoticStrongConvergence

namespace AsymptoticRegularTrace

open MeasureTheory Filter ContinuousLinearMap
open scoped lp Topology ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem projection_root_eq_norm (U : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace U] :
    (matrix U.starProjection 1 1).re=‖U.starProjection (delta 1)‖^2 := by
  have hsa : U.starProjection.adjoint=U.starProjection := isSelfAdjoint_starProjection U
  have hp : U.starProjection.comp U.starProjection=U.starProjection := U.isIdempotentElem_starProjection
  have he := matrix_gram U.starProjection 1
  rwa [hsa,hp] at he

/-- Normality from above for a decreasing sequence of measurable regular
projections of finite initial trace. -/
theorem trace_toReal_tendsto_antitone_projections (μ : Measure α)
    (U : ℕ → α → Submodule ℂ ℓ²(G,ℂ))
    [∀ n x,CompleteSpace (U n x)] [∀ x,CompleteSpace (⨅ n,U n x : Submodule ℂ ℓ²(G,ℂ))]
    (hU : ∀ x,Antitone (fun n => U n x))
    (hm : ∀ n,Measurable (fun x => matrix (U n x).starProjection 1 1))
    (hf : trace μ (fun x => (U 0 x).starProjection)<∞) :
    Tendsto (fun n => (trace μ (fun x => (U n x).starProjection)).toReal) atTop
      (𝓝 (trace μ (fun x => (⨅ n,U n x).starProjection)).toReal) := by
  apply trace_toReal_tendsto_of_strong_dominated μ _ _ hm
    (fun x v => AsymptoticStrongConvergence.antitone_projection_tendsto (fun n => U n x) (hU x) v)
    (fun x => ENNReal.ofReal (matrix (U 0 x).starProjection 1 1).re) _ hf.ne
  intro n x
  apply ENNReal.ofReal_le_ofReal
  rw [projection_root_eq_norm,projection_root_eq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (AsymptoticStrongConvergence.projection_norm_le_of_le _ _ (hU x (Nat.zero_le n)) (delta 1)) 2

#print axioms projection_root_eq_norm
#print axioms trace_toReal_tendsto_antitone_projections

end AsymptoticRegularTrace
