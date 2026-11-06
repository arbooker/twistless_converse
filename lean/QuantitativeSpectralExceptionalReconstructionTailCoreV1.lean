module

public import QuantitativeHolomorphicRegularSourceV1
public import QuantitativeSpectralExceptionalFrickeSurvivorV1
public import QuantitativeSpectralExceptionalRowsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReconstructionTail

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticPolarIsometry AsymptoticCornerKernel
open QuantitativeHolomorphic QuantitativeSpectralObservability
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open scoped lp ENNReal

/-- Right composition may change the input support subspace, but cannot
increase its regular trace. The proof compares closed output ranges. -/
theorem composition_rank_le (T U : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hmT : ∀ g k, Measurable (fun x => matrix (T x) g k)) (hcT : Covariant T)
    (hmU : ∀ g k, Measurable (fun x => matrix (U x) g k)) (hcU : Covariant U)
    (M : ℝ) (hT : ∀ x, ‖T x‖≤M) (hU : ∀ x, ‖U x‖≤1) :
    trace volume (fun x => ((T x).comp (U x)).kerᗮ.starProjection)≤
      trace volume (fun x => (T x).kerᗮ.starProjection) := by
  have hcomp (x : ℍ) : ‖(T x).comp (U x)‖≤M :=
    (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left (hU x) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hT x))
  rw [support_trace_eq volume AsymptoticRationalGroup.measurePreserving _
    (matrix_comp_measurable _ _ hmT hmU) (covariant_comp _ _ hcT hcU) M hcomp,
    support_trace_eq volume AsymptoticRationalGroup.measurePreserving T hmT hcT M hT]
  apply projection_trace_mono volume
  intro x
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨v,rfl⟩
  exact ⟨U x v,rfl⟩

theorem absolute_comp_ker {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : ℓ²(OrbitGroup,ℂ) →L[ℂ] E)
    (U : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ)) :
    ((absolute T).comp U).ker=(T.comp U).ker := by
  ext v
  change absolute T (U v)=0 ↔ T (U v)=0
  change U v∈(absolute T).ker ↔ U v∈T.ker
  rw [absolute_ker]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def row (hN : 0<N) (P : Parameters A) (e : Sector N)
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ)) (x : ℍ) :
    ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (T x).comp (normalizedRegularAmbientCountReconstruction A hN P e x)

theorem row_regular (hN : 0<N) (P : Parameters A) (e : Sector N)
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g k, Measurable (fun x => matrix (T x) g k)) (hc : Covariant T) :
    (∀ g k, Measurable (fun x => matrix (row A hN P e T x) g k)) ∧ Covariant (row A hN P e T) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  exact ⟨matrix_comp_measurable _ _ hm hU.1,covariant_comp _ _ hc hU.2⟩

theorem row_norm (hN : 0<N) (P : Parameters A) (e : Sector N)
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ)) (x : ℍ) :
    ‖row A hN P e T x‖≤‖T x‖ := by
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (normalizedRegularAmbientCountReconstruction_norm_le A hN P e x) (norm_nonneg (T x))

theorem row_rank_le (hN : 0<N) (P : Parameters A) (e : Sector N)
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g k, Measurable (fun x => matrix (T x) g k)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x, ‖T x‖≤M) :
    trace volume (fun x => (row A hN P e T x).kerᗮ.starProjection)≤
      trace volume (fun x => (T x).kerᗮ.starProjection) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  exact composition_rank_le T _ hm hc hU.1 hU.2 M hM
    (normalizedRegularAmbientCountReconstruction_norm_le A hN P e)

theorem survivor_regular (hN : 0<N) (P : Parameters A) (e : Sector N)
    (V : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (V x)]
    (hmV : ∀ g k, Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection))
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g k, Measurable (fun x => matrix (T x) g k)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x, ‖T x‖≤M) :
    (∀ g k, Measurable (fun x => matrix (remaining (V x) (row A hN P e T x)).starProjection g k)) ∧
      Covariant (fun x => (remaining (V x) (row A hN P e T x)).starProjection) := by
  have hr := row_regular A hN P e T hm hc
  exact remaining_regular V hmV hcV _ hr.1 hr.2 M (fun x => (row_norm A hN P e T x).trans (hM x))

theorem survivor_trace (hN : 0<N) (P : Parameters A) (e : Sector N)
    (V : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (V x)]
    (hmV : ∀ g k, Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection))
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g k, Measurable (fun x => matrix (T x) g k)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x, ‖T x‖≤M) :
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) (row A hN P e T x)).starProjection)+
        trace volume (fun x => (T x).kerᗮ.starProjection) := by
  have hr := row_regular A hN P e T hm hc
  exact (source_trace_le_remaining_add_rank V hmV hcV _ hr.1 hr.2 M
    (fun x => (row_norm A hN P e T x).trans (hM x))).trans
      (add_le_add le_rfl (row_rank_le A hN P e T hm hc M hM))

#print axioms composition_rank_le
#print axioms row_rank_le
#print axioms survivor_trace

end QuantitativeSpectralExceptionalReconstructionTail
