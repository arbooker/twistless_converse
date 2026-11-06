module

public import AsymptoticRamifiedCosetReductionV1
public import AsymptoticProjectiveCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

def representative (M q : ℕ) (j : Fin q) : CongruenceSubgroup.Gamma0 M :=
  ⟨lowerSL M (j.val:ℤ),lowerSL_mem M (j.val:ℤ)⟩

def coset (M q : ℕ) (j : Fin q) :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 (q*M)).subgroupOf (CongruenceSubgroup.Gamma0 M) :=
  QuotientGroup.mk (representative M q j)

theorem coset_injective (M q : ℕ) (hM : 0<M) (hq : 0<q) : Function.Injective (coset M q) := by
  intro i j hij
  have he := QuotientGroup.eq.mp hij
  change (lowerSL M (i.val:ℤ))⁻¹*lowerSL M (j.val:ℤ)∈CongruenceSubgroup.Gamma0 (q*M) at he
  exact representatives_distinct M q hM hq i j he

theorem coset_surjective (M q : ℕ) (hq : 0<q) (hqM : q∣M) : Function.Surjective (coset M q) := by
  intro y
  induction y using Quotient.inductionOn with
  | h A =>
    obtain ⟨j,hj⟩ := reduce_to_finer M q hq hqM A.val A.property
    refine ⟨j,QuotientGroup.eq.mpr ?_⟩
    exact hj

noncomputable def cosetEquiv (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    Fin q ≃ (CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 (q*M)).subgroupOf (CongruenceSubgroup.Gamma0 M)) :=
  Equiv.ofBijective (coset M q) ⟨coset_injective M q hM hq,coset_surjective M q hq hqM⟩

/-- Exact repeated-factor congruence index, proved by explicit cosets. -/
theorem integral_index (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    (CongruenceSubgroup.Gamma0 (q*M)).relIndex (CongruenceSubgroup.Gamma0 M)=q := by
  change Nat.card (CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 (q*M)).subgroupOf (CongruenceSubgroup.Gamma0 M))=q
  rw [Nat.card_congr (cosetEquiv M q hM hq hqM).symm,Nat.card_fin]

theorem projective_index (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    (gamma (q*M)).relIndex (gamma M)=q := by
  rw [gamma_relIndex]
  exact integral_index M q hM hq hqM

#print axioms coset_injective
#print axioms coset_surjective
#print axioms integral_index
#print axioms projective_index

end AsymptoticRamifiedCosets

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace

/-- The first old projection at a repeated factor q has exactly 1/q
of the quotient trace, with its index calculated rather than supplied. -/
theorem repeated_factor_lower_trace (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (q*M) := ⟨(Nat.mul_pos hq hM).ne'⟩
    (trace volume (fun z => (lowerSpace (Nat.dvd_mul_left M q) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (q*M) hε ht)).toReal/(q:ℝ) := by
  let : NeZero (q*M) := ⟨(Nat.mul_pos hq hM).ne'⟩
  have hi : ((gamma (q*M)).subgroupOf (gamma M)).index=q :=
    AsymptoticRamifiedCosets.projective_index M q hM hq hqM
  rw [lowerSpace_trace,hi]

#print axioms repeated_factor_lower_trace

end AsymptoticCongruenceOldSpace
