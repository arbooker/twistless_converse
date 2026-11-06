module

public import AsymptoticCoprimeCosetChartV1
public import AsymptoticRamifiedCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

def coprimeRepresentative (M p : ℕ) (hc : p.Coprime M) : Option (Fin p) → CongruenceSubgroup.Gamma0 M
  | none => ⟨exceptional M p hc,exceptional_mem M p hc⟩
  | some j => representative M p j

def coprimeCoset (M p : ℕ) (hc : p.Coprime M) (j : Option (Fin p)) :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 (p*M)).subgroupOf (CongruenceSubgroup.Gamma0 M) :=
  QuotientGroup.mk (coprimeRepresentative M p hc j)

theorem coprimeCoset_injective (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M) :
    Function.Injective (coprimeCoset M p hc) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      have hh := QuotientGroup.eq.mp hij
      exact (exceptional_distinct M p hM hp hc j hh).elim
  | some i =>
    cases j with
    | none =>
      have hh := QuotientGroup.eq.mp hij.symm
      exact (exceptional_distinct M p hM hp hc i hh).elim
    | some j =>
      have hh := QuotientGroup.eq.mp hij
      exact congrArg some (representatives_distinct M p hM hp.pos i j hh)

theorem coprimeCoset_surjective (M p : ℕ) (hp : p.Prime) (hc : p.Coprime M) :
    Function.Surjective (coprimeCoset M p hc) := by
  let : Fact p.Prime := ⟨hp⟩
  intro y
  induction y using Quotient.inductionOn with
  | h A =>
    by_cases ha : (A.val 0 0:ZMod p)=0
    · exact ⟨none,QuotientGroup.eq.mpr (reduce_to_exceptional M p hc A.val A.property ha)⟩
    · obtain ⟨j,hj⟩ := reduce_of_topLeft_unit M p hp.pos A.val A.property (isUnit_iff_ne_zero.mpr ha)
      exact ⟨some j,QuotientGroup.eq.mpr hj⟩

noncomputable def coprimeCosetEquiv (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M) :
    Option (Fin p) ≃ (CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 (p*M)).subgroupOf (CongruenceSubgroup.Gamma0 M)) :=
  Equiv.ofBijective (coprimeCoset M p hc)
    ⟨coprimeCoset_injective M p hM hp hc,coprimeCoset_surjective M p hp hc⟩

/-- Exact index at a new prime factor: the affine p charts and the
explicit Bezout chart give all p+1 cosets. -/
theorem integral_index_coprime (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M) :
    (CongruenceSubgroup.Gamma0 (p*M)).relIndex (CongruenceSubgroup.Gamma0 M)=p+1 := by
  change Nat.card (CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 (p*M)).subgroupOf (CongruenceSubgroup.Gamma0 M))=p+1
  rw [Nat.card_congr (coprimeCosetEquiv M p hM hp hc).symm]
  simp [Nat.card_eq_fintype_card]

theorem projective_index_coprime (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M) :
    (gamma (p*M)).relIndex (gamma M)=p+1 := by
  rw [gamma_relIndex]
  exact integral_index_coprime M p hM hp hc

#print axioms coprimeCoset_injective
#print axioms coprimeCoset_surjective
#print axioms integral_index_coprime
#print axioms projective_index_coprime

end AsymptoticRamifiedCosets

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace

theorem new_prime_lower_trace (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    (trace volume (fun z => (lowerSpace (Nat.dvd_mul_left M p) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (p*M) hε ht)).toReal/(p+1:ℝ) := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  have hi : ((gamma (p*M)).subgroupOf (gamma M)).index=p+1 :=
    AsymptoticRamifiedCosets.projective_index_coprime M p hM hp hc
  rw [lowerSpace_trace,hi,Nat.cast_add,Nat.cast_one]

#print axioms new_prime_lower_trace

end AsymptoticCongruenceOldSpace
