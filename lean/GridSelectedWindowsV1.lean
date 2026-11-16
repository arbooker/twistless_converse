module

public import GridRadiusV1
public import GridCenterChoiceV1
public import GridLabelDetectionV1

@[expose] public section

namespace GridSelectedWindows

open GridPrimeParts GridAdmissibleGap GridRadius GridCenterChoice
  GridLabelDetection SpanningActualKernel SpanningWindows

theorem label_order_dvd {G : ℕ} (hG : 0<G) (a : Fin G) : labelOrder a∣G := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  simpa only [labelOrder,Nat.card_eq_fintype_card,ZMod.card] using addOrderOf_dvd_natCard (a.val:ZMod G)

theorem label_order_pos {G : ℕ} (hG : 0<G) (a : Fin G) : 0<labelOrder a := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  exact addOrderOf_pos (a.val:ZMod G)

theorem label_order_dvd_modulus {G : ℕ} (hG : 0<G) (a : Fin G) : labelOrder a∣labelModulus a :=
  divisor_dvd_part (Nat.ne_of_gt hG) (Nat.ne_of_gt (label_order_pos hG a)) (label_order_dvd hG a)

theorem center_positive {G : ℕ} (hG : 0<G) (a : Fin G) : 0<labelModulus a/labelOrder a := by
  change 0<(primePart G (fun p => p∣addOrderOf (a.val:ZMod G)))/addOrderOf (a.val:ZMod G)
  rw [←gcd_center hG]
  exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _))

#print axioms label_order_dvd_modulus
#print axioms center_positive

end GridSelectedWindows
