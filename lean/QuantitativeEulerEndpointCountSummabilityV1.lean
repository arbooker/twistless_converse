module

public import Mathlib.Data.Nat.Count
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset

def reciprocalIndicator (A : ℕ → Prop) [DecidablePred A] (n : ℕ) : ℝ :=
  if A n then 1/(n : ℝ) else 0

theorem reciprocalIndicator_nonneg (A : ℕ → Prop) [DecidablePred A] (n : ℕ) :
    0≤reciprocalIndicator A n := by unfold reciprocalIndicator; split_ifs <;> positivity

/-- Reciprocal mass on a block is bounded by the actual cumulative count
at its upper endpoint divided by its lower endpoint. -/
theorem reciprocal_block_le_count (A : ℕ → Prop) [DecidablePred A]
    (u v : ℕ) (hu : 0<u) :
    (∑ n∈Ico u v, reciprocalIndicator A n)≤(Nat.count A v : ℝ)/(u : ℝ) := by
  rw [show (∑ n∈Ico u v, reciprocalIndicator A n)=
    ∑ n∈(Ico u v).filter A, 1/(n : ℝ) from (sum_filter A (fun n : ℕ => 1/(n : ℝ))).symm]
  have hle : (∑ n∈(Ico u v).filter A, 1/(n : ℝ))≤
      ∑ _n∈(Ico u v).filter A, 1/(u : ℝ) := by
    apply sum_le_sum
    intro n hn
    apply one_div_le_one_div_of_le (by exact_mod_cast hu)
    exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
  have hc : ((Ico u v).filter A).card≤Nat.count A v := by
    rw [Nat.count_eq_card_filter_range]
    apply card_le_card
    intro n hn
    exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp (mem_filter.mp hn).1).2,(mem_filter.mp hn).2⟩
  simp only [sum_const,nsmul_eq_mul,mul_one_div] at hle
  exact hle.trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg u))

/-- A general block-count criterion for reciprocal summability, with all
partition and convergence steps proved. -/
theorem summable_reciprocal_of_block_counts (A : ℕ → Prop) [DecidablePred A]
    (u : ℕ → ℕ) (hu : Monotone u) (hpos : ∀ j, 0<u j)
    (hcofinal : ∀ n : ℕ, ∃ j : ℕ, n≤u j)
    (hs : Summable (fun j : ℕ => (Nat.count A (u (j+1)) : ℝ)/(u j : ℝ))) :
    Summable (reciprocalIndicator A) := by
  let g : ℕ → ℝ := fun j => (Nat.count A (u (j+1)) : ℝ)/(u j : ℝ)
  have hg0 (j : ℕ) : 0≤g j := by dsimp [g]; positivity
  have hprefix (J : ℕ) : (∑ n∈range (u J), reciprocalIndicator A n)≤
      (∑ n∈range (u 0), reciprocalIndicator A n)+∑ j∈range J, g j := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← sum_range_add_sum_Ico (reciprocalIndicator A) (hu (Nat.le_succ J))]
      have hb := reciprocal_block_le_count A (u J) (u (J+1)) (hpos J)
      have hh := add_le_add ih hb
      simpa only [sum_range_succ,add_assoc,g] using hh
  apply summable_of_sum_range_le (reciprocalIndicator_nonneg A)
    (c := (∑ n∈range (u 0), reciprocalIndicator A n)+∑' j, g j)
  intro n
  obtain ⟨J,hJ⟩ := hcofinal n
  have hsub : (∑ i∈range n, reciprocalIndicator A i)≤∑ i∈range (u J), reciprocalIndicator A i :=
    sum_le_sum_of_subset_of_nonneg (range_mono hJ) (fun i _ _ => reciprocalIndicator_nonneg A i)
  exact (hsub.trans (hprefix J)).trans
    (add_le_add le_rfl (hs.sum_le_tsum (range J) (fun j _ => hg0 j)))

#print axioms summable_reciprocal_of_block_counts
end QuantitativeEulerEndpointAP
