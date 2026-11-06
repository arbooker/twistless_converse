module

public import AsymptoticPrimesInAPV1
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
@[expose] public section

namespace AsymptoticPrimesInAP

open Filter
open scoped Topology

/-- Enumerate fresh primes in a fixed unit class, beyond any prescribed
finite bound. Their actual one-prime loss parameters have divergent sum. -/
theorem exists_prime_sequence {L : ℕ} [NeZero L] {a : ZMod L}
    (ha : IsUnit a) (B : ℕ) :
    ∃ q : ℕ → ℕ,StrictMono q ∧
      (∀ n,B<q n ∧ (q n).Prime ∧ (q n:ZMod L)=a) ∧
      Tendsto (fun n => ∑ i∈Finset.range n,1/((q i:ℝ)-1)) atTop atTop := by
  classical
  let S : Set ℕ := {p | p.Prime ∧ (p:ZMod L)=a} \ Set.Iic B
  have hi : S.Infinite := (Nat.infinite_setOfPred_prime_and_eq_mod ha).sdiff (Set.finite_Iic B)
  let : Infinite S := hi.to_subtype
  let e : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
  let q : ℕ → ℕ := fun n => (e n).val
  have hp (n : ℕ) : B<q n ∧ (q n).Prime ∧ (q n:ZMod L)=a := by
    have hn := (e n).property
    exact ⟨lt_of_not_ge hn.2,hn.1⟩
  have hns : ¬Summable (fun n => (q n:ℝ)⁻¹) := by
    intro hs
    have hsub : Summable (fun p : S => (p.val:ℝ)⁻¹) := e.toEquiv.summable_iff.mp hs
    have hind : Summable (S.indicator (fun p : ℕ => (p:ℝ)⁻¹)) :=
      summable_subtype_iff_indicator.mp hsub
    apply not_summable_reciprocal ha
    apply hind.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop B] with n hn
    simp [S,reciprocal,Set.indicator,hn.not_ge]
  have hnl : ¬Summable (fun n => 1/((q n:ℝ)-1)) := by
    intro hs
    apply hns
    apply Summable.of_nonneg_of_le (fun n => inv_nonneg.mpr (Nat.cast_nonneg _)) _ hs
    intro n
    have hq : (1:ℝ)<q n := by exact_mod_cast (hp n).2.1.one_lt
    simpa only [one_div] using inv_anti₀ (by linarith : 0<(q n:ℝ)-1) (by linarith : (q n:ℝ)-1≤q n)
  refine ⟨q,(fun _ _ h => e.strictMono h),hp,?_⟩
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n =>
    div_nonneg zero_le_one (by have h := (hp n).2.1.one_lt; exact sub_nonneg.mpr (by exact_mod_cast h.le)))).mp hnl

#print axioms exists_prime_sequence

/-- The enumeration also discharges freshness against a fixed positive
certificate modulus and every earlier prime in the same sequence. -/
theorem exists_fresh_prime_sequence {L : ℕ} [NeZero L] {a : ZMod L}
    (ha : IsUnit a) (B : ℕ) (hB : 0<B) :
    ∃ q : ℕ → ℕ,StrictMono q ∧
      (∀ n,(q n).Prime ∧ ¬q n∣B ∧ (q n:ZMod L)=a) ∧
      (∀ m n,m<n → ¬q n∣q m) ∧
      Tendsto (fun n => ∑ i∈Finset.range n,1/((q i:ℝ)-1)) atTop atTop := by
  obtain ⟨q,hmono,hq,hdiv⟩ := exists_prime_sequence ha B
  refine ⟨q,hmono,(fun n => ⟨(hq n).2.1,?_,(hq n).2.2⟩),?_,hdiv⟩
  · intro h
    exact (not_le_of_gt (hq n).1) (Nat.le_of_dvd hB h)
  · intro m n hmn h
    exact (not_le_of_gt (hmono hmn)) (Nat.le_of_dvd (hq m).2.1.pos h)

#print axioms exists_fresh_prime_sequence

end AsymptoticPrimesInAP
