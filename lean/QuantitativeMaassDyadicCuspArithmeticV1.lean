module

public import QuantitativeMaassAdmissibleCuspDivisorV1
public import QuantitativeMaassLowerHalfNormalizerV1
public import QuantitativeMaassHalfCuspReductionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticFreshCRT
open scoped MatrixGroups

namespace QuantitativeMaass

theorem fullDyadicDenominator_of_odd (N : ℕ) (c : ℤ) (hc : ¬(2:ℤ)∣c) :
    fullDyadicDenominator N c.natAbs := by
  intro h
  exact (hc (Int.natCast_dvd.mpr h)).elim

theorem fullDyadicDenominator_of_eight (N : ℕ) (c : ℤ) (hc : (8:ℤ)∣c) :
    fullDyadicDenominator N c.natAbs := by
  have h8 : 8∣c.natAbs := Int.natCast_dvd.mp hc
  exact fun _ => ⟨fun _ => (by decide : 4∣8).trans h8,fun _ => h8⟩

theorem fullDyadicDenominator_of_four (N : ℕ) (hN : ¬8∣N)
    (c : ℤ) (hc : (4:ℤ)∣c) : fullDyadicDenominator N c.natAbs := by
  exact fun _ => ⟨fun _ => Int.natCast_dvd.mp hc,fun h8 => (hN h8).elim⟩

theorem fullDyadicDenominator_of_level (N : ℕ) (hN : ¬4∣N) (c : ℤ) :
    fullDyadicDenominator N c.natAbs := by
  exact fun _ => ⟨fun h4 => (hN h4).elim,
    fun h8 => (hN ((by decide : 4∣8).trans h8)).elim⟩

/-- At a level with exactly three factors of two, the integral lower
half-translation sends a cusp denominator of valuation two to one
divisible by eight. -/
theorem lowerHalf_cusp_eight (M : ℕ) (hN : ¬16∣8*M) (a : SL(2,ℤ))
    (hc4 : (4:ℤ)∣a 1 0) (hc8 : ¬(8:ℤ)∣a 1 0) :
    (8:ℤ)∣((lowerSL (4*M) 1)*a) 1 0 := by
  have hM : ¬2∣M := by
    rintro ⟨k,hk⟩
    apply hN
    exact ⟨k,by rw [hk]; ring⟩
  have hMo : Odd (M:ℤ) := by
    apply Int.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro h
    exact hM (by exact_mod_cast h)
  obtain ⟨c,hc⟩ := hc4
  have hco : Odd c := by
    apply Int.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    rintro ⟨d,hd⟩
    apply hc8
    exact ⟨d,by rw [hc,hd]; ring⟩
  have hd := a.property
  rw [Matrix.det_fin_two] at hd
  change a 0 0*a 1 1-a 0 1*a 1 0=1 at hd
  have ho : Odd (a 0 0*a 1 1) := ⟨2*a 0 1*c,by rw [hc] at hd; linear_combination hd⟩
  obtain ⟨u,hu⟩ := hMo.mul (Int.odd_mul.mp ho).1
  obtain ⟨v,hv⟩ := hco
  refine ⟨u+v+1,?_⟩
  change ((lowerSL (4*M) 1).val*a.val) 1 0=8*(u+v+1)
  simp only [lowerSL,lower,Matrix.mul_apply,Fin.sum_univ_two]
  simp only [Matrix.of_apply,Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.cons_val_fin_one,Nat.cast_mul,Nat.cast_ofNat,mul_one,one_mul,hc]
  linear_combination 4*hu+4*hv

#print axioms fullDyadicDenominator_of_odd
#print axioms fullDyadicDenominator_of_eight
#print axioms fullDyadicDenominator_of_four
#print axioms fullDyadicDenominator_of_level
#print axioms lowerHalf_cusp_eight

end QuantitativeMaass
