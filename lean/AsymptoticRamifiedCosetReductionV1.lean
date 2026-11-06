module

public import AsymptoticCongruenceTransvectionsV1
public import AsymptoticFreshCRTResiduesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open Matrix AsymptoticCongruenceLabels AsymptoticFreshCRT
open scoped MatrixGroups

/-- A unit top-left entry selects a unique lower-transvection chart. -/
theorem reduce_of_topLeft_unit (M q : ℕ) (hq : 0<q)
    (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 M) (hu : IsUnit (A 0 0:ZMod q)) :
    ∃ j : Fin q,(lowerSL M (j.val:ℤ))⁻¹*A∈CongruenceSubgroup.Gamma0 (q*M) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hcdiv := (gamma0_mem_dvd M A).mp hA
  obtain ⟨c,hc⟩ := hcdiv
  let u : (ZMod q)ˣ := hu.unit
  let r : ZMod q := (c:ZMod q)*(u⁻¹: (ZMod q)ˣ)
  let j : Fin q := ⟨r.val,ZMod.val_lt r⟩
  have hj : (j.val:ZMod q)=r := ZMod.natCast_zmod_val r
  have hau : (u:ZMod q)=(A 0 0:ZMod q) := hu.unit_spec
  have hm : ((c-(j.val:ℤ)*A 0 0:ℤ):ZMod q)=0 := by
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,hj,← hau]
    simp [r,mul_assoc]
  obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hm
  refine ⟨j,(gamma0_mem_dvd (q*M) _).mpr ⟨a,?_⟩⟩
  rw [lowerSL_inv_mul_bottom,hc,Nat.cast_mul]
  calc
    (M:ℤ)*c-(M:ℤ)*(j.val:ℤ)*A 0 0=(M:ℤ)*(c-(j.val:ℤ)*A 0 0) := by ring
    _=(M:ℤ)*((q:ℤ)*a) := by rw [ha]
    _=((q:ℤ)*(M:ℤ))*a := by ring

/-- At a repeated level factor every top-left entry is a unit modulo q.
The reduction works for any positive divisor q of M, not just primes. -/
theorem reduce_to_finer (M q : ℕ) (hq : 0<q) (hqM : q∣M)
    (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 M) :
    ∃ j : Fin q,(lowerSL M (j.val:ℤ))⁻¹*A∈CongruenceSubgroup.Gamma0 (q*M) := by
  have hqM' : (q:ℤ)∣(M:ℤ) := by exact_mod_cast hqM
  exact reduce_of_topLeft_unit M q hq A hA
    (topLeft_isUnit A q (hqM'.trans ((gamma0_mem_dvd M A).mp hA)))

/-- The transvection representatives are distinct modulo the finer
subgroup, so the preceding reduction counts cosets exactly. -/
theorem representatives_distinct (M q : ℕ) (hM : 0<M) (hq : 0<q) (i j : Fin q)
    (h : (lowerSL M (i.val:ℤ))⁻¹*lowerSL M (j.val:ℤ)∈CongruenceSubgroup.Gamma0 (q*M)) : i=j := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [lowerSL_inv,lowerSL_mul,gamma0_mem_dvd] at h
  change ((q*M:ℕ):ℤ)∣(M:ℤ)*(-(i.val:ℤ)+(j.val:ℤ)) at h
  rw [Nat.cast_mul,mul_comm (q:ℤ) (M:ℤ)] at h
  have hM0 : (M:ℤ)≠0 := by exact_mod_cast hM.ne'
  have hd : (q:ℤ)∣(-(i.val:ℤ)+(j.val:ℤ)) := (mul_dvd_mul_iff_left hM0).mp h
  have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hd
  have he : (i.val:ZMod q)=(j.val:ZMod q) := by
    simp only [Int.cast_add,Int.cast_neg,Int.cast_natCast] at hm
    exact neg_add_eq_zero.mp hm
  apply Fin.ext
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hv

#print axioms reduce_of_topLeft_unit
#print axioms reduce_to_finer
#print axioms representatives_distinct

end AsymptoticRamifiedCosets
