module

public import GridPrimePartsV1
public import Mathlib.Data.ZMod.Units

@[expose] public section

namespace GridUnitChoice

theorem positive_unit_inverse {G s a : ℕ} (hG : 0<G) (hs : s∣G) (ha : Nat.Coprime a s) :
    ∃r:ℕ,0<r ∧ Nat.Coprime r G ∧ Nat.ModEq s (r*a) 1 := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  let v := (ZMod.unitOfCoprime a ha)⁻¹
  obtain ⟨u,hu⟩ := ZMod.unitsMap_surjective hs v
  let r := (u:ZMod G).val+G
  refine ⟨r,by dsimp [r]; omega,?_,?_⟩
  · exact Nat.coprime_add_self_left.mpr (ZMod.val_coe_unit_coprime u)
  · apply (ZMod.natCast_eq_natCast_iff (r*a) 1 s).mp
    have hc : ((u:ZMod G).val:ZMod s)=(v:ZMod s) := by
      have hh := congrArg (fun z:(ZMod s)ˣ => (z:ZMod s)) hu
      simpa only [ZMod.unitsMap_val,ZMod.cast_eq_val] using hh
    have hGs : (G:ZMod s)=0 := (ZMod.natCast_eq_zero_iff G s).mpr hs
    simp only [r,Nat.cast_mul,Nat.cast_add,hGs,add_zero,Nat.cast_one,hc]
    change ((ZMod.unitOfCoprime a ha)⁻¹: (ZMod s)ˣ).val*(a:ZMod s)=1
    rw [←ZMod.coe_unitOfCoprime a ha]
    exact Units.inv_mul (ZMod.unitOfCoprime a ha)

#print axioms positive_unit_inverse

/-- A unit modulo the whole grid sends any residue modulo a divisor to
its gcd with that divisor. This is the selected-row congruence. -/
theorem positive_unit_to_gcd {G m a : ℕ} (hG : 0<G) (hm : 0<m) (hmG : m∣G) :
    ∃r:ℕ,0<r ∧ Nat.Coprime r G ∧ Nat.ModEq m (r*a) (Nat.gcd a m) := by
  let c := Nat.gcd a m
  let s := m/c
  let b := a/c
  have hc : 0<c := Nat.gcd_pos_of_pos_right a hm
  have hbs : Nat.Coprime b s := Nat.coprime_div_gcd_div_gcd hc
  have hsG : s∣G := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a m)).trans hmG
  obtain ⟨r,hr,hrG,hrs⟩ := positive_unit_inverse hG hsG hbs
  refine ⟨r,hr,hrG,?_⟩
  have hmc : s*c=m := Nat.div_mul_cancel (Nat.gcd_dvd_right a m)
  have hac : b*c=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a m)
  have hh := hrs.mul_right' c
  simpa only [hmc,Nat.mul_assoc,hac,one_mul] using hh

#print axioms positive_unit_to_gcd

end GridUnitChoice
