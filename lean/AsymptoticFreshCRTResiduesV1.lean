module

public import AsymptoticFreshCongruenceV1
public import Mathlib.Data.ZMod.Units

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshCRT

open Matrix
open scoped MatrixGroups

/-- The determinant identity makes the top-left entry a unit modulo
every divisor of the lower-left entry. -/
theorem topLeft_isUnit (γ : SL(2,ℤ)) (m : ℕ) (hm : (m:ℤ)∣γ 1 0) :
    IsUnit (γ 0 0:ZMod m) := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hd' : (γ 0 0:ZMod m)*(γ 1 1:ZMod m)-(γ 0 1:ZMod m)*(γ 1 0:ZMod m)=1 := by
    have he := congrArg (fun z : ℤ => (z:ZMod m)) hd
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one] using he
  have hz : (γ 1 0:ZMod m)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hm
  rw [hz,mul_zero,sub_zero] at hd'
  exact IsUnit.of_mul_eq_one _ hd'

/-- Classical lifting of units gives the residue class required for a
generator. The common modulus need only be a nonzero multiple of m. -/
theorem generator_residue (γ : SL(2,ℤ)) (m L : ℕ) [NeZero L]
    (hm : (m:ℤ)∣γ 1 0) (hL : m∣L) :
    ∃ r : ℕ,r<L ∧ r.Coprime L ∧ (r:ZMod m)=(γ 0 0:ZMod m) := by
  have hu := topLeft_isUnit γ m hm
  obtain ⟨v,hv⟩ := ZMod.unitsMap_surjective hL hu.unit
  refine ⟨(v:ZMod L).val,ZMod.val_lt _,ZMod.val_coe_unit_coprime v,?_⟩
  calc
    ((v:ZMod L).val:ZMod m)=((v:ZMod L).cast:ZMod m) := by
      have he := congrArg (fun z : ZMod L => (z.cast:ZMod m)) (ZMod.natCast_zmod_val (v:ZMod L))
      simpa only [ZMod.cast_natCast hL] using he
    _ = ((ZMod.unitsMap hL v):ZMod m) := (ZMod.unitsMap_val hL v).symm
    _ = (γ 0 0:ZMod m) := by rw [hv,hu.unit_spec]

/-- A prime in the lifted class has the prescribed generator residue
modulo m. This is the divisibility needed for the initial translation. -/
theorem residue_descends (m L r q : ℕ) (a : ℤ) (hL : m∣L)
    (hr : (r:ZMod m)=(a:ZMod m)) (hq : (q:ZMod L)=(r:ZMod L)) :
    (m:ℤ)∣(q:ℤ)-a := by
  have he := congrArg (fun z : ZMod L => (z.cast:ZMod m)) hq
  rw [ZMod.cast_natCast hL,ZMod.cast_natCast hL,hr] at he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub,Int.cast_natCast,he,sub_self]

#print axioms topLeft_isUnit
#print axioms generator_residue
#print axioms residue_descends

end AsymptoticFreshCRT
