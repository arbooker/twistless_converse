module

public import GridAdmissibleGapV1

@[expose] public section

namespace GridLevelFormula

open GridPrimeParts GridAdmissibleGap

theorem lcm_of_coprime_part (a b D : ℕ) (hc : Nat.Coprime a D) (hb : b∣D) :
    Nat.lcm (a*b) D=a*D := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd (Nat.mul_dvd_mul_left a hb) (dvd_mul_left D a)
  · apply hc.mul_dvd_of_dvd_of_dvd
    · exact (dvd_mul_right a b).trans (Nat.dvd_lcm_left (a*b) D)
    · exact Nat.dvd_lcm_right (a*b) D

theorem grid_level {N G s r : ℕ} (hN : N≠0) (hG : G≠0) (hNG : N∣G)
    (hr : Nat.Coprime r G) :
    let d := primePart G (fun p => ¬p∣s)
    Nat.lcm N ((d*r)^2)=levelPart N s*((d*r)^2) := by
  let S := fun p:ℕ => p∣s
  let a := primePart N S
  let b := primePart N (fun p => ¬S p)
  let d := primePart G (fun p => ¬S p)
  have hab : a*b=N := part_complement hN S
  have hbd : b∣d := part_dvd_part hN hG hNG _
  have ham : a∣primePart G S := part_dvd_part hN hG hNG S
  have had : Nat.Coprime a d := (parts_coprime hG S).coprime_dvd_left ham
  have haG : a∣G := (part_dvd N S).trans hNG
  have har : Nat.Coprime a r := hr.symm.coprime_dvd_left haG
  have hac : Nat.Coprime a ((d*r)^2) := (had.mul_right har).pow_right 2
  have hbD : b∣(d*r)^2 := (hbd.trans (dvd_mul_right d r)).trans (dvd_pow_self (d*r) (by omega : 2≠0))
  change Nat.lcm N ((d*r)^2)=a*((d*r)^2)
  rw [←hab]
  exact lcm_of_coprime_part a b _ hac hbD

#print axioms grid_level

end GridLevelFormula
