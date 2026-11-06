module

public import QuantitativeEulerDiamondGroupV1
public import AsymptoticFreshCongruenceV1
public import QuantitativeArithmeticCertificateChoiceV1
public import Mathlib.NumberTheory.LSeries.PrimesInAP

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic AsymptoticFreshMatrices
open scoped MatrixGroups

/-- A literal canonical branch with a=1 and the standard nonzero residue
1 ≤ b < q. Bezout and an integral translation construct its last entry. -/
theorem exists_canonical_one (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N) :
    ∃ b c : ℤ, 1≤b ∧ b<q ∧ (q : ℤ)*c=(N : ℤ)*1*b+1 := by
  have hb := Nat.gcd_eq_gcd_ab q N
  rw [hc] at hb
  have hd : (q : ℤ)*Nat.gcdA q N-(N : ℤ)*(-1)*Nat.gcdB q N=1 := by
    have h := hb.symm
    simp only [Nat.cast_one] at h
    nlinarith [h]
  obtain ⟨b,l,hb1,hbq,hbl,_⟩ := exists_canonical_residue
    (q : ℤ) (Nat.gcdB q N) N (-1) (Nat.gcdA q N)
    (by exact_mod_cast hq.one_lt) hd
  refine ⟨b,Nat.gcdA q N-(N : ℤ)*l,hb1,hbq,?_⟩
  nlinarith [hd,congrArg (fun x : ℤ => (N : ℤ)*x) hbl]

/-- Dirichlet supplies a fixed prime in every unit class. Its canonical
matrix is an actual original prime-equation branch, not an arbitrary lift. -/
theorem exists_prime_canonical (N : ℕ) [NeZero N] (a : UnitResidue N) :
    ∃ q : ℕ, ∃ b c : ℤ, q.Prime ∧ N<q ∧
      (q : ZMod N)=(a.val.val : ZMod N) ∧
      1≤b ∧ b<q ∧ (q : ℤ)*c=(N : ℤ)*1*b+1 := by
  have ha : IsUnit (a.val.val : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ _).mpr a.property
  obtain ⟨q,hqN,hq,hqa⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha N
  have hc : q.Coprime N := (ZMod.isUnit_iff_coprime _ _).mp (hqa ▸ ha)
  obtain ⟨b,c,hb,hbq,hbc⟩ := exists_canonical_one N q hq hc
  exact ⟨q,b,c,hq,hqN,hqa,hb,hbq,hbc⟩

structure PrimeLift (N : ℕ) (a : UnitResidue N) where
  q : ℕ
  b : ℤ
  c : ℤ
  prime : q.Prime
  large : N<q
  residue : (q : ZMod N)=(a.val.val : ZMod N)
  b_pos : 1≤b
  b_lt : b<q
  determinant : (q : ℤ)*c=(N : ℤ)*1*b+1

def primeLift (N : ℕ) [NeZero N] (a : UnitResidue N) : PrimeLift N a := by
  apply Classical.choice
  obtain ⟨q,b,c,hq,hqN,hqa,hb,hbq,hbc⟩ := exists_prime_canonical N a
  exact ⟨⟨q,b,c,hq,hqN,hqa,hb,hbq,hbc⟩⟩

def primeMatrix (N : ℕ) [NeZero N] (a : UnitResidue N) : SL(2,ℤ) :=
  let P := primeLift N a
  canonical N P.q 1 P.b P.c P.determinant

theorem primeMatrix_mem (N : ℕ) [NeZero N] (a : UnitResidue N) :
    primeMatrix N a∈Gamma0 N :=
  canonical_mem_Gamma0 N _ _ _ _ (primeLift N a).determinant

theorem primeMatrix_residue (N : ℕ) [NeZero N] (a : UnitResidue N) :
    (primeMatrix N a 0 0 : ZMod N)=(a.val.val : ZMod N) := by
  change (((primeLift N a).q : ℤ) : ZMod N)=_
  simpa only [Int.cast_natCast] using (primeLift N a).residue

/-- The fixed finite family of actual prime-equation matrices removes the
entire diamond quotient. No quotient generation hypothesis remains. -/
theorem gamma0_generated_by_prime_matrices (N : ℕ) [NeZero N] :
    Gamma0 N=Gamma1 N ⊔ Subgroup.closure (Set.range (primeMatrix N)) := by
  apply le_antisymm
  · intro A hA
    obtain ⟨a,ha⟩ := exists_leading_residue N A hA
    have hq : (primeMatrix N a)⁻¹*A∈Gamma1 N :=
      same_residue_quotient N _ _ (primeMatrix_mem N a) hA
        ((primeMatrix_residue N a).trans ha.symm)
    have hl : primeMatrix N a∈Subgroup.closure (Set.range (primeMatrix N)) :=
      Subgroup.subset_closure ⟨a,rfl⟩
    have hp := (Gamma1 N ⊔ Subgroup.closure (Set.range (primeMatrix N))).mul_mem
      ((show Subgroup.closure (Set.range (primeMatrix N)) ≤
        Gamma1 N ⊔ Subgroup.closure (Set.range (primeMatrix N)) from le_sup_right) hl)
      ((show Gamma1 N ≤ Gamma1 N ⊔ Subgroup.closure (Set.range (primeMatrix N)) from le_sup_left) hq)
    simpa only [mul_inv_cancel_left] using hp
  · apply sup_le (Gamma1_in_Gamma0 N)
    rw [Subgroup.closure_le]
    rintro _ ⟨a,rfl⟩
    exact primeMatrix_mem N a

#print axioms exists_canonical_one
#print axioms exists_prime_canonical
#print axioms gamma0_generated_by_prime_matrices
end QuantitativeEulerDensityGenerators
