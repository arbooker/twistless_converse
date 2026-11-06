module

public import QuantitativeEulerDiamondPrimesV1
public import QuantitativeArithmeticDiamondLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic QuantitativeArithmeticDiamondLabels
open scoped MatrixGroups Classical

/-- Choose one of the literal observed branches at the fixed Dirichlet
prime in each unit class. Its canonical convention is the swapped one
recovered from the original Fricke observation. -/
def observedPrimeMatrix (N : ℕ) [NeZero N] (a : UnitResidue N) : SL(2,ℤ) :=
  let P := primeLift N a
  letI : Fact P.q.Prime := ⟨P.prime⟩
  swappedCanonical N P.q (Nat.not_dvd_of_pos_of_lt (NeZero.pos N) P.large)
    ⟨0,by have h := P.prime.one_lt; omega⟩

theorem observedPrimeMatrix_mem (N : ℕ) [NeZero N] (a : UnitResidue N) :
    observedPrimeMatrix N a∈Gamma0 N := by
  let : Fact (primeLift N a).q.Prime := ⟨(primeLift N a).prime⟩
  exact swappedCanonical_mem _ _ _ _

theorem observedPrimeMatrix_residue (N : ℕ) [NeZero N] (a : UnitResidue N) :
    (observedPrimeMatrix N a 0 0 : ZMod N)=(a.val.val : ZMod N) := by
  change (((primeLift N a).q : ℤ) : ZMod N)=_
  simpa only [Int.cast_natCast] using (primeLift N a).residue

/-- The canonical branches recovered from the actual observations, with
Gamma1, generate Gamma0. No matching of independently chosen Bezout
representatives is assumed. -/
theorem gamma0_generated_by_observed_matrices (N : ℕ) [NeZero N] :
    Gamma0 N=Gamma1 N ⊔ Subgroup.closure (Set.range (observedPrimeMatrix N)) := by
  apply le_antisymm
  · intro A hA
    obtain ⟨a,ha⟩ := exists_leading_residue N A hA
    have hq : (observedPrimeMatrix N a)⁻¹*A∈Gamma1 N :=
      same_residue_quotient N _ _ (observedPrimeMatrix_mem N a) hA
        ((observedPrimeMatrix_residue N a).trans ha.symm)
    have hl : observedPrimeMatrix N a∈Subgroup.closure (Set.range (observedPrimeMatrix N)) :=
      Subgroup.subset_closure ⟨a,rfl⟩
    have hp := (Gamma1 N ⊔ Subgroup.closure (Set.range (observedPrimeMatrix N))).mul_mem
      ((show Subgroup.closure (Set.range (observedPrimeMatrix N)) ≤
        Gamma1 N ⊔ Subgroup.closure (Set.range (observedPrimeMatrix N)) from le_sup_right) hl)
      ((show Gamma1 N ≤ Gamma1 N ⊔ Subgroup.closure (Set.range (observedPrimeMatrix N)) from le_sup_left) hq)
    simpa only [mul_inv_cancel_left] using hp
  · apply sup_le (Gamma1_in_Gamma0 N)
    rw [Subgroup.closure_le]
    rintro _ ⟨a,rfl⟩
    exact observedPrimeMatrix_mem N a

/-- A fixed finite generating set built from the same Gamma1 generators
used by density preparation and the actual observed canonical branches. -/
def observedGenerators (N : ℕ) [NeZero N] : Finset SL(2,ℤ) :=
  generators N ∪ Finset.univ.image (observedPrimeMatrix N)

theorem observedGenerators_closure (N : ℕ) [NeZero N] :
    Subgroup.closure (observedGenerators N : Set SL(2,ℤ))=Gamma0 N := by
  rw [observedGenerators,Finset.coe_union,Subgroup.closure_union,generators_closure]
  have hr : (↑(Finset.univ.image (observedPrimeMatrix N)) : Set SL(2,ℤ))=
      Set.range (observedPrimeMatrix N) := by
    ext g
    simp
  rw [hr,←gamma0_generated_by_observed_matrices]

#print axioms gamma0_generated_by_observed_matrices
#print axioms observedGenerators_closure
end QuantitativeEulerDensityGenerators
