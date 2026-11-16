module

public import GridSupportedDetectionV1

@[expose] public section

namespace QuantitativeArithmeticMixedLabelDetection

open GridLabelDetection GridTriangularDetection

/-- The labels in a complete prime row. Unlike the selected legal rows,
this row is available at every translate. -/
noncomputable def primeHit {G : ℕ} (p : ℕ) (a : Fin G) : Finset (Fin G) := by
  classical
  exact Finset.univ.filter (fun z => Nat.ModEq (G / p) z.val a.val)

theorem mem_primeHit {G p : ℕ} (a z : Fin G) :
    z ∈ primeHit p a ↔ Nat.ModEq (G / p) z.val a.val := by
  classical
  simp [primeHit]

/-- The off-diagonal entries of a complete prime row have order exactly
`p` times the pivot order, provided `p` does not divide that order. -/
theorem primeHit_order {G p : ℕ} (hG : 0 < G) (hp : p.Prime) (hpG : p ∣ G)
    (a z : Fin G) (hpa : ¬ p ∣ labelOrder a)
    (hz : z ∈ primeHit p a) (hne : z ≠ a) :
    labelOrder z = labelOrder a * p := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  let x : ZMod G := a.val
  let y : ZMod G := z.val - a.val
  have hy0 : y ≠ 0 := by
    intro he
    have he' : (z.val : ZMod G) = a.val := sub_eq_zero.mp he
    have hm := (ZMod.natCast_eq_natCast_iff z.val a.val G).mp he'
    apply hne
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt z.isLt, Nat.mod_eq_of_lt a.isLt] using hm
  have hpy : p • y = 0 := by
    have hm := (mem_primeHit a z |>.mp hz).mul_left' p
    rw [Nat.mul_div_cancel' hpG] at hm
    have he := (ZMod.natCast_eq_natCast_iff (p*z.val) (p*a.val) G).mpr hm
    simpa only [y, nsmul_eq_mul, mul_sub, Nat.cast_mul, sub_eq_zero] using he
  have hyo : addOrderOf y = p := by
    have hd : addOrderOf y ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpy
    rcases hp.eq_one_or_self_of_dvd _ hd with he | he
    · exact False.elim (hy0 (AddMonoid.addOrderOf_eq_one_iff.mp he))
    · exact he
  have hc : Nat.Coprime (addOrderOf x) (addOrderOf y) := by
    rw [hyo]
    exact (hp.coprime_iff_not_dvd.mpr hpa).symm
  have he := (show AddCommute x y from add_comm x y).addOrderOf_add_eq_mul_addOrderOf_of_coprime hc
  have hxy : x + y = (z.val : ZMod G) := by dsimp [x, y]; ring
  rw [hxy, hyo] at he
  exact he

theorem primeHit_strict {G p : ℕ} (hG : 0 < G) (hp : p.Prime) (hpG : p ∣ G)
    (a z : Fin G) (hpa : ¬ p ∣ labelOrder a)
    (hz : z ∈ primeHit p a) (hne : z ≠ a) : labelOrder a < labelOrder z := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  rw [primeHit_order hG hp hpG a z hpa hz hne]
  have hpos : 0 < labelOrder a := addOrderOf_pos (a.val : ZMod G)
  nlinarith [hp.two_le]

#print axioms primeHit_order
#print axioms primeHit_strict

end QuantitativeArithmeticMixedLabelDetection
