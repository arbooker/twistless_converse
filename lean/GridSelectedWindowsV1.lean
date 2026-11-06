module

public import GridBufferedWindowV1
public import GridCenterChoiceV1
public import GridLabelDetectionV1

@[expose] public section

namespace GridSelectedWindows

open GridPrimeParts GridAdmissibleGap GridRadius GridBufferedWindow GridCenterChoice
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

theorem selected_window {N G r R v w : ℕ} (hN : Admissible N) (hG : 0<G) (hNG : N∣G)
    (a : Fin G) (ha : 2<labelOrder a) (hr : 0<r) (hrG : Nat.Coprime r G)
    (hrR : r≤R) (hv : 16*R≤v) (hvw : v=r*w) (t : ℤ)
    (ht : |(t:ℝ)|≤(v:ℝ)/(8*R)) :
    let c := labelModulus a/labelOrder a
    let d := primePart G (fun p => ¬p∣labelOrder a)
    Legal (radius N (G*v) (d*r)) ((c*w:ℕ)+t) ∧
      3*(v:ℝ)/(40*R)-1≤radius N (G*v) (d*r)-1-(((c*w:ℕ):ℤ)+t:ℤ) := by
  let m := labelModulus a
  let c := m/labelOrder a
  let d := primePart G (fun p => ¬p∣labelOrder a)
  have hc : 1≤c := center_positive hG a
  have hmc : m=c*labelOrder a := (Nat.div_mul_cancel (label_order_dvd_modulus hG a)).symm
  have hrR' : (r:ℝ)≤R := by exact_mod_cast hrR
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hR' : (0:ℝ)<R := lt_of_lt_of_le hr' hrR'
  have hv' : (16:ℝ)*R≤v := by exact_mod_cast hv
  have hvw' : (v:ℝ)=(r:ℝ)*w := by exact_mod_cast hvw
  have hcentre : (v:ℝ)/r≤(c:ℝ)*w := by
    rw [hvw',mul_div_cancel_left₀ _ (ne_of_gt hr')]
    have hc' : (1:ℝ)≤c := by exact_mod_cast hc
    nlinarith [show (0:ℝ)≤w from Nat.cast_nonneg w]
  have hex := excess_from_ratio (m:=(m:ℝ)) (c:=(c:ℝ)) (s:=(labelOrder a:ℝ))
    (v:=(v:ℝ)) (r:=(r:ℝ)) (n:=Real.sqrt (levelPart N (labelOrder a)))
    (by exact_mod_cast hc) (Nat.cast_nonneg _) hr' (by exact_mod_cast hmc) (order_ratio hN ha)
  have hcenterEq : (c:ℝ)*v/r=(c:ℝ)*w := by rw [hvw']; field_simp
  rw [hcenterEq] at hex
  have hrad := grid_radius (s:=labelOrder a) hN.1 hG hr hNG hrG v
  change radius N (G*v) (d*r)=(m:ℝ)*v/((r:ℝ)*Real.sqrt (levelPart N (labelOrder a))) at hrad
  rw [←hrad] at hex
  apply window_from_excess hr' hR' hrR' hv' hcentre hex ht
  norm_cast

#print axioms selected_window

end GridSelectedWindows
