module

public import AsymptoticFreshMatricesV1
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshResidues

variable (q : ℕ) [Fact q.Prime]

theorem index_coprime (i : Fin (q-1)) : Nat.Coprime (i.val+1) q := by
  apply Nat.Coprime.symm
  apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have he := Nat.le_of_dvd (Nat.succ_pos i.val) hd
  omega

def indexUnit (i : Fin (q-1)) : (ZMod q)ˣ := ZMod.unitOfCoprime (i.val+1) (index_coprime q i)

def unitIndex (u : (ZMod q)ˣ) : Fin (q-1) :=
  ⟨(u:ZMod q).val-1,by
    have hp := Nat.pos_of_ne_zero ((ZMod.val_ne_zero (u:ZMod q)).mpr u.ne_zero)
    have hl := ZMod.val_lt (u:ZMod q)
    omega⟩

theorem indexUnit_val (i : Fin (q-1)) : (indexUnit q i:ZMod q)=((i.val+1:ℕ):ZMod q) := rfl

def unitEquiv : Fin (q-1) ≃ (ZMod q)ˣ where
  toFun := indexUnit q
  invFun := unitIndex q
  left_inv i := by
    apply Fin.ext
    change ((indexUnit q i:ZMod q).val-1)=i.val
    rw [indexUnit_val,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
    omega
  right_inv u := by
    apply Units.ext
    rw [indexUnit_val]
    change (((u:ZMod q).val-1+1:ℕ):ZMod q)=(u:ZMod q)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero _).mpr u.ne_zero)),
      ZMod.natCast_zmod_val]

variable (N : ℕ) (hN : ¬q∣N)

def levelUnit : (ZMod q)ˣ :=
  ZMod.unitOfCoprime N ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hN).symm

/-- b maps to -1/(Nb), as a permutation of the nonzero residues. -/
def unitPermutation : Equiv.Perm (ZMod q)ˣ :=
  (Equiv.inv (ZMod q)ˣ).trans (Equiv.mulLeft (-(levelUnit q N hN)⁻¹))

def permutation : Equiv.Perm (Fin (q-1)) :=
  (unitEquiv q).trans ((unitPermutation q N hN).trans (unitEquiv q).symm)

theorem permutation_unit (i : Fin (q-1)) :
    indexUnit q (permutation q N hN i)=unitPermutation q N hN (indexUnit q i) :=
  (unitEquiv q).apply_symm_apply _

/-- The permutation has the exact congruence needed for the determinant-N
representative of every individual defect. -/
theorem permutation_relation (i : Fin (q-1)) :
    (N:ZMod q)*((permutation q N hN i).val+1)*((i.val:ZMod q)+1)= -1 := by
  have he := congrArg (fun u : (ZMod q)ˣ => (u:ZMod q)) (permutation_unit q N hN i)
  have ha : ((permutation q N hN i).val:ZMod q)+1=
      -(N:ZMod q)⁻¹*((i.val:ZMod q)+1)⁻¹ := by
    simpa [unitPermutation,levelUnit,indexUnit] using he
  have hnz : (N:ZMod q)≠0 := (levelUnit q N hN).ne_zero
  have hbz : (i.val:ZMod q)+1≠0 := by
    simpa [indexUnit] using (indexUnit q i).ne_zero
  rw [ha]
  field_simp

theorem permutation_divisibility (i : Fin (q-1)) :
    (q:ℤ)∣(N:ℤ)*((permutation q N hN i).val+1)*(i.val+1)+1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  push_cast
  rw [permutation_relation]
  simp

noncomputable def quotient (i : Fin (q-1)) : ℤ :=
  ((N:ℤ)*((permutation q N hN i).val+1)*(i.val+1)+1)/q

theorem quotient_relation (i : Fin (q-1)) :
    (q:ℤ)*quotient q N hN i=(N:ℤ)*((permutation q N hN i).val+1)*(i.val+1)+1 :=
  Int.mul_ediv_cancel' (permutation_divisibility q N hN i)

#print axioms permutation_relation
#print axioms permutation_divisibility
#print axioms quotient_relation
#print axioms index_coprime
#print axioms indexUnit_val
#print axioms permutation_unit

end AsymptoticFreshResidues
