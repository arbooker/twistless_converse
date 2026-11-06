module

public import GridCosetOrderV1
public import GridUnitChoiceV1

@[expose] public section

namespace GridCenterChoice

open GridPrimeParts GridCosetOrder GridUnitChoice

theorem order_dvd_iff {G a n : ℕ} : addOrderOf (a:ZMod G)∣n ↔ G∣n*a := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero,nsmul_eq_mul]
  simpa only [Nat.cast_mul] using (ZMod.natCast_eq_zero_iff (n*a) G)

theorem prime_part_order {G a : ℕ} (hG : 0<G) :
    addOrderOf (a:ZMod (primePart G (fun p => p∣addOrderOf (a:ZMod G))))=
      addOrderOf (a:ZMod G) := by
  let s := addOrderOf (a:ZMod G)
  let m := primePart G (fun p => p∣s)
  let d := primePart G (fun p => ¬p∣s)
  have hmd : m*d=G := part_complement (Nat.ne_of_gt hG) _
  have hcop : Nat.Coprime m d := parts_coprime (Nat.ne_of_gt hG) _
  have hsd : Nat.Coprime s d := divisor_complement_coprime (Nat.ne_of_gt hG)
  have hda : d∣a := hsd.symm.dvd_of_dvd_mul_left ((part_dvd G _).trans (order_annihilation G a))
  change addOrderOf (a:ZMod m)=s
  apply Nat.dvd_antisymm
  · exact order_dvd_iff.mpr ((part_dvd G _).trans (order_annihilation G a))
  · apply order_dvd_iff.mpr
    have hh := hcop.mul_dvd_of_dvd_of_dvd (order_annihilation m a) (hda.trans (dvd_mul_left a _))
    rwa [hmd] at hh

theorem gcd_center {G a : ℕ} (hG : 0<G) :
    Nat.gcd a (primePart G (fun p => p∣addOrderOf (a:ZMod G)))=
      primePart G (fun p => p∣addOrderOf (a:ZMod G))/addOrderOf (a:ZMod G) := by
  let m := primePart G (fun p => p∣addOrderOf (a:ZMod G))
  have hm : m≠0 := part_ne_zero (Nat.ne_of_gt hG) _
  have ho := prime_part_order (a:=a) hG
  change addOrderOf (a:ZMod m)=addOrderOf (a:ZMod G) at ho
  change Nat.gcd a m=m/addOrderOf (a:ZMod G)
  rw [←ho,ZMod.addOrderOf_coe a hm,Nat.div_div_self (Nat.gcd_dvd_left m a) hm]
  exact Nat.gcd_comm a m

theorem positive_center_choice {G a : ℕ} (hG : 0<G) :
    ∃r:ℕ,0<r ∧ Nat.Coprime r G ∧
      Nat.ModEq (primePart G (fun p => p∣addOrderOf (a:ZMod G)))
        (r*a) ((primePart G (fun p => p∣addOrderOf (a:ZMod G)))/addOrderOf (a:ZMod G)) := by
  obtain ⟨r,hr,hc,he⟩ := positive_unit_to_gcd
    (m:=primePart G (fun p => p∣addOrderOf (a:ZMod G))) (a:=a) hG
    (Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)) (part_dvd G _)
  refine ⟨r,hr,hc,?_⟩
  rwa [gcd_center hG] at he

#print axioms positive_center_choice

end GridCenterChoice
