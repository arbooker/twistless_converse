module

public import AsymptoticFreshResiduesV1
public import AsymptoticFreshCanonicalReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshResidues

variable (q : ℕ) [Fact q.Prime]

/-- Integer residues in the canonical matrix have the same index type
as the original q-1 compact defect rows. -/
def integerIndex (b : ℤ) (hb : 0<b) (hbq : b<(q:ℤ)) : Fin (q-1) :=
  ⟨b.toNat-1,by omega⟩

omit [Fact q.Prime] in
theorem integerIndex_val (b : ℤ) (hb : 0<b) (hbq : b<(q:ℤ)) :
    ((integerIndex q b hb hbq).val:ℤ)+1=b := by
  dsimp only [integerIndex]
  omega

theorem index_eq_of_cast_eq (i j : Fin (q-1))
    (h : ((i.val+1:ℕ):ZMod q)=((j.val+1:ℕ):ZMod q)) : i=j := by
  have hi : i.val+1<q := by omega
  have hj : j.val+1<q := by omega
  have he := congrArg ZMod.val h
  rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at he
  exact Fin.ext (by omega)

variable (N : ℕ) (hN : ¬q∣N)

/-- Uniqueness of the residue a(b) proves that a canonical matrix is
one of the actual individual relations, not merely congruent to one. -/
theorem permutation_unique (i j : Fin (q-1))
    (h : (N:ZMod q)*((j.val+1:ℕ):ZMod q)*((i.val+1:ℕ):ZMod q)= -1) :
    permutation q N hN i=j := by
  have he : (N:ZMod q)*((permutation q N hN i).val+1)*((i.val:ZMod q)+1)=
      (N:ZMod q)*((j.val:ZMod q)+1)*((i.val:ZMod q)+1) :=
    (permutation_relation q N hN i).trans (by simpa only [Nat.cast_add,Nat.cast_one] using h.symm)
  have hi : (i.val:ZMod q)+1≠0 := by
    simpa only [indexUnit_val,Nat.cast_add,Nat.cast_one] using (indexUnit q i).ne_zero
  have hn : (N:ZMod q)≠0 := (levelUnit q N hN).ne_zero
  have ha := mul_left_cancel₀ hn (mul_right_cancel₀ hi he)
  apply index_eq_of_cast_eq q
  simpa only [Nat.cast_add,Nat.cast_one] using ha

theorem canonical_indices (a b c : ℤ) (ha : 0<a) (haq : a<(q:ℤ))
    (hb : 0<b) (hbq : b<(q:ℤ)) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    ((permutation q N hN (integerIndex q b hb hbq)).val:ℤ)+1=a ∧
      quotient q N hN (integerIndex q b hb hbq)=c := by
  let i := integerIndex q b hb hbq
  let j := integerIndex q a ha haq
  have hi : (i.val:ℤ)+1=b := integerIndex_val q b hb hbq
  have hj : (j.val:ℤ)+1=a := integerIndex_val q a ha haq
  have he : permutation q N hN i=j := by
    apply permutation_unique q N hN i j
    have hc := congrArg (fun z : ℤ => (z:ZMod q)) h
    have hi' := congrArg (fun z : ℤ => (z:ZMod q)) hi
    have hj' := congrArg (fun z : ℤ => (z:ZMod q)) hj
    simp only [Int.cast_add,Int.cast_natCast,Int.cast_one] at hi' hj'
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_add,Int.cast_one,ZMod.natCast_self,zero_mul] at hc
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hi',hj']
    linear_combination -hc
  refine ⟨by rw [he]; exact hj,?_⟩
  have hquot := quotient_relation q N hN i
  rw [he,hj,hi] at hquot
  exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero : (q:ℤ)≠0)
    (hquot.trans h.symm)

#print axioms integerIndex_val
#print axioms index_eq_of_cast_eq
#print axioms permutation_unique
#print axioms canonical_indices

end AsymptoticFreshResidues
