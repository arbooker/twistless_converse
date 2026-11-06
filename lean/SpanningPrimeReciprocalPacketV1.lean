module

/-
The two finite Erdős estimates below are adapted from Michael Stoll's
Mathlib.NumberTheory.SumPrimeReciprocals (copyright2023, Apache2.0),
commit065356127b1dc0016f66b7283ce0ce2c4055aa55. They avoid importing the
unneeded analytic infinite-sum/P-series development. The proof terms,
including the underlying smooth-number estimates, are checked locally.
-/
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic

@[expose] public section

namespace SpanningPrimeReciprocalPacket

open Nat

theorem rough_count_bound (N k:ℕ) :
    (roughNumbersUpTo N k).card≤
      N*(N.succ.primesBelow \ k.primesBelow).sum (fun p => (1:ℝ)/p) := by
  simp_rw [Finset.mul_sum,mul_one_div]
  exact (Nat.cast_le.mpr (roughNumbersUpTo_card_le N k)).trans
    (cast_sum (R:=ℝ) .. ▸ Finset.sum_le_sum (fun n _ => cast_div_le))

theorem half_sum (k:ℕ) :
    (1:ℝ)/2≤∑p∈(4^(k.primesBelow.card+1)).succ.primesBelow \ k.primesBelow,1/(p:ℝ) := by
  set m:ℕ := 2^k.primesBelow.card
  set N₀:ℕ := 2*m^2 with hN₀
  let S:ℝ := ((2*N₀).succ.primesBelow \ k.primesBelow).sum (fun p => 1/(p:ℝ))
  suffices 1/2≤S by
    convert! this using 5
    rw [show 4=2^2 by simp,pow_right_comm]
    ring
  suffices 2*N₀≤m*(2*N₀).sqrt+2*N₀*S by
    rwa [hN₀,←mul_assoc,←pow_two 2,←mul_pow,sqrt_eq',←sub_le_iff_le_add',
      cast_mul,cast_mul,cast_pow,cast_two,
      show (2*(2*m^2)-m*(2*m):ℝ)=2*(2*m^2)*(1/2) by ring,
      mul_le_mul_iff_right₀ (by positivity)] at this
  calc
    (2*N₀:ℝ)=((2*N₀).smoothNumbersUpTo k).card+((2*N₀).roughNumbersUpTo k).card := by
      exact_mod_cast ((2*N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _≤m*(2*N₀).sqrt+((2*N₀).roughNumbersUpTo k).card := by
      exact_mod_cast Nat.add_le_add_right ((2*N₀).smoothNumbersUpTo_card_le k) _
    _≤m*(2*N₀).sqrt+2*N₀*S := by
      have he := add_le_add_right (rough_count_bound (2*N₀) k) ((m:ℝ)*(2*N₀).sqrt)
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using he

#print axioms half_sum

end SpanningPrimeReciprocalPacket
