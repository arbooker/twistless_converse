module

public import AsymptoticTwoOldSubspacesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticCornerKernel AsymptoticPolarIsometry
open AsymptoticSubspaceIntersection AsymptoticTwoOldSubspaces
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem support_trace_adjoint (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    trace μ (fun x => (T x).kerᗮ.starProjection)=
      trace μ (fun x => (T x).adjoint.kerᗮ.starProjection) := by
  have he (x : α) : (T x).adjoint.kerᗮ=outputSpace (T x) := by
    rw [ContinuousLinearMap.orthogonal_ker,adjoint_adjoint]
    rfl
  simp only [starProjection_congr _ _ (he _)]
  exact support_trace_eq μ hmp T hm hc M hM

/-- The trace remaining after removing two closed old directions.
The correction is their actual intersection, and no closedness of
their algebraic sum is assumed. -/
theorem two_old_trace (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (S U V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (S x)] [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hU : ∀ x,U x≤S x) (hV : ∀ x,V x≤S x)
    (hmS : ∀ g h,Measurable (fun x => matrix (S x).starProjection g h))
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmV : ∀ g h,Measurable (fun x => matrix (V x).starProjection g h))
    (hcS : Covariant (fun x => (S x).starProjection))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcV : Covariant (fun x => (V x).starProjection))
    (hf : trace μ (fun x => (S x).starProjection)<∞) :
    (trace μ (fun x => (newSpace (S x) (U x) (V x)).starProjection)).toReal=
      (trace μ (fun x => (S x).starProjection)).toReal-
      (trace μ (fun x => (U x).starProjection)).toReal-
      (trace μ (fun x => (V x).starProjection)).toReal+
      (trace μ (fun x => (inter (V x) (U x)).starProjection)).toReal := by
  let L := fun x => relativeComplement (S x) (U x)
  let T := fun x => (L x).starProjection.comp (V x).starProjection
  have hL := remaining_regular S hmS hcS (fun x => (U x).starProjection)
    hmU hcU 1 (fun x => (U x).starProjection_norm_le)
  have hmT : ∀ g h,Measurable (fun x => matrix (T x) g h) :=
    matrix_comp_measurable _ _ hL.1 hmV
  have hcT : Covariant T := covariant_comp _ _ hL.2 hcV
  have hT : ∀ x,‖T x‖≤1 := by
    intro x
    exact (restricted_norm_le (V x) (L x).starProjection).trans (L x).starProjection_norm_le
  have hrT := source_support_regular T hmT hcT 1 hT
  have hrA := source_support_regular (fun x => (T x).adjoint)
    (matrix_adjoint_measurable T hmT) (covariant_adjoint T hcT) 1
    (fun x => by simpa only [adjoint.norm_map] using hT x)
  have hLf := projection_trace_finite_of_le μ L S (fun _ => inf_le_left) hf
  have hVf := projection_trace_finite_of_le μ V S hV hf
  have heV := corner_removed_trace μ V T
    (fun x => restricted_comp_projection (V x) (L x).starProjection) (hrT.1 1 1) hVf
  have heL := corner_removed_trace μ L (fun x => (T x).adjoint)
    (fun x => by
      change ((relativeComplement (S x) (U x)).starProjection.comp (V x).starProjection).adjoint.comp
        (relativeComplement (S x) (U x)).starProjection=_
      rw [adjoint_complement]
      exact restricted_comp_projection (L x) (V x).starProjection) (hrA.1 1 1) hLf
  have heI (x : α) : remaining (V x) (T x)=inter (V x) (U x) :=
    remaining_complement_eq_inter (S x) (U x) (V x) (hU x) (hV x)
  have heN (x : α) : remaining (L x) (T x).adjoint=newSpace (S x) (U x) (V x) :=
    remaining_adjoint_eq_new (S x) (U x) (V x)
  simp only [starProjection_congr _ _ (heI _)] at heV
  simp only [starProjection_congr _ _ (heN _)] at heL
  have hproj (x : α) : (U x).starProjection.kerᗮ.starProjection=(U x).starProjection := by
    apply starProjection_congr
    rw [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal]
  have heU := corner_removed_trace μ S (fun x => (U x).starProjection)
    (fun x => Submodule.starProjection_comp_starProjection_of_le (hU x))
    (by simpa only [hproj] using hmU 1 1) hf
  simp only [hproj] at heU
  change (trace μ (fun x => (U x).starProjection)).toReal=
    (trace μ (fun x => (S x).starProjection)).toReal-
    (trace μ (fun x => (L x).starProjection)).toReal at heU
  have heRank := congrArg ENNReal.toReal (support_trace_adjoint μ hmp T hmT hcT 1 hT)
  linarith

#print axioms support_trace_adjoint
#print axioms two_old_trace

end AsymptoticRegularTrace
