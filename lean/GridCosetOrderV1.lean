module

public import GridOrderTriangularityV1
public import GridPrimePartsV1

@[expose] public section

namespace GridCosetOrder

open GridPrimeParts GridOrderTriangularity

theorem order_annihilation (G a : ℕ) : G∣addOrderOf (a:ZMod G)*a := by
  apply (ZMod.natCast_eq_zero_iff _ G).mp
  rw [Nat.cast_mul,←nsmul_eq_mul]
  exact addOrderOf_nsmul_eq_zero (a:ZMod G)

theorem grid_coset_strict {G a z : ℕ} (hG : 0<G)
    (hza : Nat.ModEq (primePart G (fun p => p∣addOrderOf (a:ZMod G))) z a)
    (hne : ¬Nat.ModEq G z a) :
    addOrderOf (a:ZMod G)<addOrderOf (z:ZMod G) := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  let s := addOrderOf (a:ZMod G)
  let m := primePart G (fun p => p∣s)
  let d := primePart G (fun p => ¬p∣s)
  have hm : 0<m := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
  have hd : 0<d := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
  have hmd : m*d=G := part_complement (Nat.ne_of_gt hG) _
  have hcop : Nat.Coprime m d := parts_coprime (Nat.ne_of_gt hG) _
  have hsd : Nat.Coprime s d := divisor_complement_coprime (Nat.ne_of_gt hG)
  have hda : d∣a := hsd.symm.dvd_of_dvd_mul_left ((part_dvd G _).trans (order_annihilation G a))
  have hae : addOrderOf (a:ZMod (m*d))=s := congrArg (fun n => addOrderOf (a:ZMod n)) hmd
  have hze : addOrderOf (z:ZMod (m*d))=addOrderOf (z:ZMod G) :=
    congrArg (fun n => addOrderOf (z:ZMod n)) hmd
  have hh := residue_coset_strict_order hm hd hcop hda hza
    (show Nat.Coprime (addOrderOf (a:ZMod (m*d))) d by rw [hae]; exact hsd)
    (by simpa [hmd] using hne)
  rw [hae,hze] at hh
  exact hh

#print axioms grid_coset_strict

end GridCosetOrder
