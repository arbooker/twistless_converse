module

public import AsymptoticCompactRestrictionV1
public import AsymptoticInfiniteKernelTraceV1
public import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservationRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticSectorSigns

theorem row_restrict {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (row hN r e hu hε t x)=row hN r e hs hε t x := by
  cases r <;> exact family_restrict _ _ hs hu hsub hε t x

theorem row_kernel_restrict {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (row hN r e hu hε t x).ker≤(row hN r e hs hε t x).ker := by
  intro v hv
  change row hN r e hs hε t x v=0
  rw [← row_restrict hN r e hs hu hsub hε t x,comp_apply]
  rw [show row hN r e hu hε t x v=0 from hv,map_zero]

theorem exhaustion_zero_iff {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    (K : CompactExhaustion ℍ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    (∀ j,row hN r e (K.isCompact j) hε t x v=0) ↔
      ∀ s : Set ℍ,∀ hs : IsCompact s,row hN r e hs hε t x v=0 := by
  constructor
  · intro h s hs
    obtain ⟨j,hj⟩ := K.exists_superset_of_isCompact hs
    exact row_kernel_restrict hN r e hs (K.isCompact j) hj hε t x (h j)
  · intro h j
    exact h (K j) (K.isCompact j)

#print axioms row_restrict
#print axioms row_kernel_restrict
#print axioms exhaustion_zero_iff

end AsymptoticRegularObservationRows

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open AsymptoticRegularReconstruction AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open FinitenessCertificate FinitenessGlobalHeight
open scoped ENNReal

def familyRows {N : ℕ} (r : ℕ → Row N) (j : ℕ) : Row N := r (Nat.unpair j).1

def familyRegions (K : CompactExhaustion ℍ) (j : ℕ) : Set ℍ := K (Nat.unpair j).2

theorem familyRegions_compact (K : CompactExhaustion ℍ) (j : ℕ) :
    IsCompact (familyRegions K j) := K.isCompact _

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A countable family of the original equations, each imposed on every
compact region. This is the existing reconstructed joint kernel with a
specific countable indexing, so its trace and regularity are inherited. -/
noncomputable def globalKernelSpace (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) : Submodule ℂ Space :=
  infiniteKernelSpace A hN P (familyRows r) (familyRegions K) (familyRegions_compact K) e x

noncomputable instance globalKernelSpace_complete (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) :
    CompleteSpace (globalKernelSpace A hN P r K e x) :=
  inferInstanceAs (CompleteSpace (infiniteKernelSpace A hN P
    (familyRows r) (familyRegions K) (familyRegions_compact K) e x))

theorem globalKernelSpace_mem (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) (v : Space) :
    let P' := AsymptoticReconstructedCount.parameters A P
    v∈globalKernelSpace A hN P r K e x ↔
      v∈(includedExtension A hN P' (multiplier e) x).range ∧
        ∀ i,∀ s : Set ℍ,∀ hs : IsCompact s,row hN (r i) e hs P'.epsilon_pos (P'.s+4) x v=0 := by
  simp only [globalKernelSpace,infiniteKernelSpace,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker]
  apply and_congr_right
  intro _
  constructor
  · intro h i
    apply (exhaustion_zero_iff hN (r i) e K _ _ x v).mp
    intro j
    have he := h (Nat.pair i j)
    change row hN (familyRows r (Nat.pair i j)) e (familyRegions_compact K (Nat.pair i j))
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x v=0 at he
    simpa only [familyRows,familyRegions,Nat.unpair_pair] using he
  · intro h j
    exact h (Nat.unpair j).1 (K (Nat.unpair j).2) (K.isCompact (Nat.unpair j).2)

/-- The closed kernel does not depend on the compact exhaustion. -/
theorem globalKernelSpace_exhaustion_independent (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K J : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) :
    globalKernelSpace A hN P r K e x=globalKernelSpace A hN P r J e x := by
  ext v
  exact (globalKernelSpace_mem A hN P r K e x v).trans
    (globalKernelSpace_mem A hN P r J e x v).symm

theorem globalKernelSpace_le_of_range (hN : 0<N) (P : Parameters A) (r u : ℕ → Row N)
    (hru : Set.range r⊆Set.range u) (K : CompactExhaustion ℍ) (e : Sector N) (x : ℍ) :
    globalKernelSpace A hN P u K e x≤globalKernelSpace A hN P r K e x := by
  intro v hv
  have hv := (globalKernelSpace_mem A hN P u K e x v).mp hv
  apply (globalKernelSpace_mem A hN P r K e x v).mpr
  refine ⟨hv.1,?_⟩
  intro i
  obtain ⟨j,hj⟩ := hru ⟨i,rfl⟩
  simpa only [hj] using hv.2 j

theorem globalKernelProjection_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun x => matrix (globalKernelSpace A hN P r K e x).starProjection g h) :=
  infiniteKernelProjection_matrix_measurable A hN P
    (familyRows r) (familyRegions K) (familyRegions_compact K) e g h

theorem globalKernelProjection_covariant (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    Covariant (fun x => (globalKernelSpace A hN P r K e x).starProjection) :=
  infiniteKernelProjection_covariant A hN P
    (familyRows r) (familyRegions K) (familyRegions_compact K) e

theorem globalKernelProjection_trace_finite (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    trace volume (fun x => (globalKernelSpace A hN P r K e x).starProjection)<∞ :=
  infiniteKernelProjection_trace_finite A hN P
    (familyRows r) (familyRegions K) (familyRegions_compact K) e

#print axioms familyRegions_compact
#print axioms globalKernelSpace_mem
#print axioms globalKernelSpace_exhaustion_independent
#print axioms globalKernelSpace_le_of_range
#print axioms globalKernelProjection_matrix_measurable
#print axioms globalKernelProjection_covariant
#print axioms globalKernelProjection_trace_finite

end AsymptoticRegularObservation
