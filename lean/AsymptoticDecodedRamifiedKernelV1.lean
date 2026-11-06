module

public import AsymptoticUniversalObservationKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticOrbitDecode

open UpperHalfPlane AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticFreshCompactDefects AsymptoticRationalBranches
open AsymptoticRegularCompactBranch (Space)

noncomputable def ramifiedLabel (p : ℕ) (hp : 0<p) (a : Fin p) : AsymptoticRationalGroup.Group :=
  ofMatrix (ramified p hp a.val).matrix (ramified p hp a.val).positive

/-- Removing the cap pointwise from the actual ramified observation
gives the unnormalized U_p incidence equation on decoded coordinates. -/
theorem all_compact_ramified_zero_iff (p : ℕ) (hp : 0<p) (δ : ℂ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    (∀ s : Set ℍ,∀ hs : IsCompact s,bad p hp δ hs hε t x v=0) ↔
      ∀ g : AsymptoticRationalGroup.Group,
        (∑ a : Fin p,decode ε t x v (ramifiedLabel p hp a*g))=δ*decode ε t x v g := by
  change (∀ s : Set ℍ,∀ hs : IsCompact s,
    family (ramifiedBranches p hp) (Sum.elim (fun _ => 1) (fun _ => -δ)) hs hε t x v=0) ↔ _
  rw [all_compact_family_zero_iff]
  apply forall_congr'
  intro g
  rw [Fintype.sum_sum_type]
  simp only [ramifiedBranches,Sum.elim_inl,Sum.elim_inr,one_mul,Fintype.sum_unique]
  change (∑ a : Fin p,decode ε t x v (ramifiedLabel p hp a*g))+
    (-δ)*decode ε t x v (ofMatrix identityBranch.matrix identityBranch.positive*g)=0 ↔ _
  rw [identityBranch_label,one_mul]
  constructor <;> intro h <;> linear_combination h

#print axioms all_compact_ramified_zero_iff

end AsymptoticOrbitDecode

namespace AsymptoticRegularObservation

open UpperHalfPlane AsymptoticOrbitDecode AsymptoticRegularObservationRows
open AsymptoticCompactObservationCount AsymptoticSectorSigns AsymptoticFreshMatrices
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem universalKernel_fricke (hN : 0<N) (P : Parameters A) (K : CompactExhaustion ℍ)
    (e : Sector N) (x : ℍ) (v : Space) (hv : v∈globalKernelSpace A hN P (universalRows N) K e x) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ g : AsymptoticRationalGroup.Group,
      sign e.1*decode P'.ε (P'.s+4) x v (frickeLabel N hN*g)=decode P'.ε (P'.s+4) x v g := by
  apply (all_compact_untwisted_zero_iff N hN (sign e.1)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) x v).mp
  intro s hs
  have he := ((universalKernel_mem A hN P K e x v).mp hv).2 (.twist 1 Nat.zero_lt_one) s hs
  simpa only [row,multiplier_one] using he

theorem universalKernel_ramified (hN : 0<N) (P : Parameters A) (K : CompactExhaustion ℍ)
    (e : Sector N) (x : ℍ) (v : Space) (hv : v∈globalKernelSpace A hN P (universalRows N) K e x)
    (p : ℕ) (hp : p.Prime) (hpN : p∣N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ g : AsymptoticRationalGroup.Group,
      (∑ a : Fin p,decode P'.ε (P'.s+4) x v (ramifiedLabel p hp.pos a*g))=
        AsymptoticCylinderRamified.eigenvalue e p*decode P'.ε (P'.s+4) x v g := by
  apply (all_compact_ramified_zero_iff p hp.pos (AsymptoticCylinderRamified.eigenvalue e p)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) x v).mp
  intro s hs
  exact ((universalKernel_mem A hN P K e x v).mp hv).2 (.ramified p hp hpN) s hs

#print axioms universalKernel_fricke
#print axioms universalKernel_ramified

end AsymptoticRegularObservation
