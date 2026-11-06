module

public import AsymptoticFullCongruenceInvarianceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCompactObservationCount

/-- A concrete enumeration of all original twist and ramified rows.
Unused indices repeat the untwisted row. -/
noncomputable def universalRows (N j : ℕ) : Row N :=
  if (Nat.unpair j).1=0 then .twist ((Nat.unpair j).2+1) (Nat.succ_pos _)
  else if h : (Nat.unpair j).2.Prime ∧ (Nat.unpair j).2∣N then
    .ramified (Nat.unpair j).2 h.1 h.2 else .twist 1 Nat.zero_lt_one

theorem universalRows_twist (N q : ℕ) (hq : 0<q) : ∃ j,universalRows N j=.twist q hq := by
  cases q with
  | zero => omega
  | succ q => exact ⟨Nat.pair 0 q,by simp [universalRows,Nat.unpair_pair]⟩

theorem universalRows_surjective (N : ℕ) : Function.Surjective (universalRows N) := by
  intro r
  cases r with
  | twist q hq => exact universalRows_twist N q hq
  | ramified p hp hpN => exact ⟨Nat.pair 1 p,by simp [universalRows,Nat.unpair_pair,hp,hpN]⟩

#print axioms universalRows_twist
#print axioms universalRows_surjective

end AsymptoticCompactObservationCount

namespace AsymptoticRegularObservation

open UpperHalfPlane Matrix MeasureTheory AsymptoticOrbitDecode AsymptoticCongruenceLabels
open AsymptoticCompactObservationCount AsymptoticRegularReconstruction
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Membership in the enumerated full kernel is exactly membership in
the reconstruction range together with every original compact equation. -/
theorem universalKernel_mem (hN : 0<N) (P : Parameters A) (K : CompactExhaustion ℍ)
    (e : Sector N) (x : ℍ) (v : Space) :
    let P' := AsymptoticReconstructedCount.parameters A P
    v∈globalKernelSpace A hN P (universalRows N) K e x ↔
      v∈(includedExtension A hN P' (multiplier e) x).range ∧
        ∀ r : Row N,∀ s : Set ℍ,∀ hs : IsCompact s,
          AsymptoticRegularObservationRows.row hN r e hs P'.epsilon_pos (P'.s+4) x v=0 := by
  have he := globalKernelSpace_mem A hN P (universalRows N) K e x v
  dsimp only at he
  rw [he]
  apply and_congr_right
  intro _
  constructor
  · intro h r
    obtain ⟨j,rfl⟩ := universalRows_surjective N r
    exact h j
  · intro h j
    exact h (universalRows N j)

/-- The concrete full kernel used in the count-to-trace reduction is
modular in decoded coordinates, with no extra invariance assumption. -/
theorem universalKernel_ae_congruence_invariant (hN : 0<N) (P : Parameters A)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ᵐ x ∂volume,∀ γ∈CongruenceSubgroup.Gamma0 N,
      ∀ v∈globalKernelSpace A hN P (universalRows N) K e x,∀ g : AsymptoticRationalGroup.Group,
        decode P'.ε (P'.s+4) x v (integralLabel γ*g)=decode P'.ε (P'.s+4) x v g :=
  globalKernel_ae_congruence_invariant A hN P (universalRows N) (universalRows_twist N) K e

#print axioms universalKernel_mem
#print axioms universalKernel_ae_congruence_invariant

end AsymptoticRegularObservation
