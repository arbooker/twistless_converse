module

public import QuantitativeMaassExactAtkinCuspV1
public import GridAdmissibleGapV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeMaass

/-- A denominator is either odd or contains the entire repeated dyadic
part of an admissible level. Only the tests at four and eight are needed. -/
def fullDyadicDenominator (N c : ℕ) : Prop :=
  2∣c → (4∣N → 4∣c) ∧ (8∣N → 8∣c)

theorem admissible_div_gcd_coprime (N c : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h2 : fullDyadicDenominator N c) : Nat.Coprime (N/Nat.gcd N c) c := by
  let D := Nat.gcd N c
  let Q := N/D
  have hQD : Q*D=N := Nat.div_mul_cancel (Nat.gcd_dvd_left N c)
  have hQN : Q∣N := ⟨D,hQD.symm⟩
  by_contra h
  obtain ⟨p,hp,hpQ,hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpD : p∣D := Nat.dvd_gcd (hpQ.trans hQN) hpc
  have hp2N : p^2∣N := by
    rw [←hQD,pow_two]
    exact mul_dvd_mul hpQ hpD
  have hp2 : p=2 := by
    by_contra hne
    exact hN.2.2 p hp hne hp2N
  subst p
  have h4N : 4∣N := by simpa using hp2N
  have h4c : 4∣c := (h2 hpc).1 h4N
  have h4D : 4∣D := Nat.dvd_gcd h4N h4c
  have h8N : 8∣N := by
    rw [←hQD]
    exact mul_dvd_mul hpQ h4D
  have h8c : 8∣c := (h2 hpc).2 h8N
  have h8D : 8∣D := Nat.dvd_gcd h8N h8c
  apply hN.2.1
  rw [←hQD]
  exact mul_dvd_mul hpQ h8D

theorem admissible_cusp_divisor (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (c : ℤ) (h2 : fullDyadicDenominator N c.natAbs) :
    ∃ D Q : ℕ,Q*D=N ∧ Nat.Coprime Q D ∧ (D:ℤ)∣c ∧ IsCoprime (Q:ℤ) c := by
  let D := Nat.gcd N c.natAbs
  let Q := N/D
  have hd : D∣c.natAbs := Nat.gcd_dvd_right N c.natAbs
  have hq : Nat.Coprime Q c.natAbs := admissible_div_gcd_coprime N c.natAbs hN h2
  refine ⟨D,Q,Nat.div_mul_cancel (Nat.gcd_dvd_left N c.natAbs),
    hq.of_dvd_right hd,Int.natCast_dvd.mpr hd,?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one,Int.gcd_def,Int.natAbs_natCast]
  exact hq

theorem admissible_cusp_atkin_matrix (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (a : SL(2,ℤ)) (h2 : fullDyadicDenominator N (a 1 0).natAbs) :
    ∃ D Q : ℕ,∃ A B : ℤ,∃ b : SL(2,ℤ),
      Q*D=N ∧ 0<Q ∧ (Q:ℤ)*A+(D:ℤ)*B=1 ∧
      b∈CongruenceSubgroup.Gamma0 N ∧
      (b.val*exactAtkinMatrix D Q A B*a.val) 1 0=0 := by
  obtain ⟨D,Q,hQD,hcop,hDc,hQc⟩ := admissible_cusp_divisor N hN (a 1 0) h2
  obtain ⟨A,B,hAB⟩ := hcop.isCoprime
  have hab : (Q:ℤ)*A+(D:ℤ)*B=1 := by simpa only [mul_comm] using hAB
  obtain ⟨c,hc⟩ := hDc
  obtain ⟨b,hb,hzero⟩ := exactAtkin_cusp_to_infinity D Q A B hab a c hc hQc
  refine ⟨D,Q,A,B,b,hQD,?_,hab,?_,hzero⟩
  · apply Nat.pos_of_ne_zero
    intro hQ
    have : N=0 := by simpa only [hQ,zero_mul] using hQD.symm
    exact hN.1.ne' this
  · simpa only [hQD] using hb

#print axioms admissible_div_gcd_coprime
#print axioms admissible_cusp_divisor
#print axioms admissible_cusp_atkin_matrix

end QuantitativeMaass
