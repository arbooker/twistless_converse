module

public import AsymptoticRegularKernelSubspacesV1
public import AsymptoticDecreasingProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open Filter
open scoped lp Topology

variable {G α : Type*} [Group G] [MulAction G α]

theorem covariant_of_strong_limit
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hc : ∀ n,Covariant (B n))
    (hB : ∀ x v,Tendsto (fun n => B n x v) atTop (𝓝 (C x v))) : Covariant C := by
  intro x a g h
  have h1 := matrix_tendsto_of_strong (fun n => B n (a • x)) (C (a • x)) (hB (a • x)) g h
  have h2 := matrix_tendsto_of_strong (fun n => B n x) (C x) (hB x) (g*a) (h*a)
  have he : (fun n => matrix (B n (a • x)) g h)=(fun n => matrix (B n x) (g*a) (h*a)) :=
    funext (fun n => hc n x a g h)
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

#print axioms covariant_of_strong_limit

end AsymptoticRegularTrace

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Filter ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open scoped Topology ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def infiniteKernelProjection (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  (infiniteKernelSpace A hN P r s hs e z).starProjection

theorem finiteKernelProjection_strong_limit (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) (v : Space) :
    Tendsto (fun n => jointKernelProjection A hN P
      (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e z v) atTop
      (𝓝 (infiniteKernelProjection A hN P r s hs e z v)) := by
  let : CompleteSpace (⨅ n,finiteKernelSpace A hN P r s hs e n z : Submodule ℂ Space) := by
    rw [← infiniteKernelSpace_eq_iInf]
    infer_instance
  have ht := AsymptoticStrongConvergence.antitone_projection_tendsto
    (fun n => finiteKernelSpace A hN P r s hs e n z) (finiteKernelSpace_antitone A hN P r s hs e z) v
  simpa only [← infiniteKernelSpace_eq_iInf,finiteKernelProjection_eq,infiniteKernelProjection] using ht

theorem infiniteKernelProjection_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (infiniteKernelProjection A hN P r s hs e z) a b) :=
  strong_limit_matrix_measurable _ _
    (fun n => jointKernelProjection_matrix_measurable A hN P
      (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e)
    (finiteKernelProjection_strong_limit A hN P r s hs e) a b

theorem jointKernelProjection_covariant {ι : Type*} [Fintype ι]
    (hN : 0<N) (P : Parameters A) (r : ι → Row N) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Covariant (jointKernelProjection A hN P r s hs e) :=
  covariant_of_strong_limit _ _
    (fun n => positive_covariant A hN P (fun j : Fin ((n+1)^2) × ι => r j.2)
      (fun j => s j.2) (fun j => hs j.2) e)
    (repeatedPositive_strong_limit A hN P r s hs e)

theorem infiniteKernelProjection_covariant (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Covariant (infiniteKernelProjection A hN P r s hs e) :=
  covariant_of_strong_limit _ _
    (fun n => jointKernelProjection_covariant A hN P (fun i : Fin n => r i)
      (fun i => s i) (fun i => hs i) e)
    (finiteKernelProjection_strong_limit A hN P r s hs e)

/-- Normality applies to the actual finite prefixes of any countable
family of known compact equations, yielding their full joint kernel. -/
theorem finiteKernelTrace_tendsto_infinite (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Tendsto (fun n => (trace volume (jointKernelProjection A hN P
      (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e)).toReal) atTop
      (𝓝 (trace volume (infiniteKernelProjection A hN P r s hs e)).toReal) := by
  let : ∀ z,CompleteSpace (⨅ n,finiteKernelSpace A hN P r s hs e n z : Submodule ℂ Space) := fun z => by
    rw [← infiniteKernelSpace_eq_iInf]
    infer_instance
  have hm (n : ℕ) : Measurable (fun z => matrix (finiteKernelSpace A hN P r s hs e n z).starProjection 1 1) := by
    simpa only [finiteKernelProjection_eq] using jointKernelProjection_matrix_measurable A hN P
      (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e 1 1
  have hf : trace volume (fun z => (finiteKernelSpace A hN P r s hs e 0 z).starProjection)<∞ := by
    simpa only [finiteKernelProjection_eq] using jointKernelProjection_trace_finite A hN P
      (fun i : Fin 0 => r i) (fun i => s i) (fun i => hs i) e
  have ht := trace_toReal_tendsto_antitone_projections volume
    (finiteKernelSpace A hN P r s hs e) (finiteKernelSpace_antitone A hN P r s hs e) hm hf
  unfold infiniteKernelProjection
  simpa only [← infiniteKernelSpace_eq_iInf,finiteKernelProjection_eq] using ht

#print axioms finiteKernelProjection_strong_limit
#print axioms infiniteKernelProjection_matrix_measurable
#print axioms jointKernelProjection_covariant
#print axioms infiniteKernelProjection_covariant
#print axioms finiteKernelTrace_tendsto_infinite

end AsymptoticRegularObservation
