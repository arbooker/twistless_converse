module

public import SpanningPolynomialDeterminantsV1
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.BigOperators.ModEq

@[expose] public section

namespace SpanningCRTExponents

open scoped BigOperators

variable {I:Type*} [Fintype I] [DecidableEq I]

def weight (c:I→ℕ) (i:I) := ∏k∈Finset.univ.erase i,c k

theorem mul_weight (c:I→ℕ) (i:I) : c i * weight c i = ∏k,c k :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ i)

theorem weight_positive (c:I→ℕ) (hc:∀i,0<c i) (i:I) : 0<weight c i :=
  Finset.prod_pos (fun k _ => hc k)

theorem weight_coprime (c:I→ℕ) (hc:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (i:I) : Nat.Coprime (c i) (weight c i) := by
  apply Nat.Coprime.prod_right
  intro j hj
  exact hc (Finset.mem_erase.mp hj).1.symm

theorem divides_other_weight (c:I→ℕ) {i j:I} (hne:i≠j) : c i ∣ weight c j :=
  Finset.dvd_prod_of_mem c (Finset.mem_erase.mpr ⟨hne,Finset.mem_univ i⟩)

theorem exponent_congr (c:I→ℕ) (a:∀i,Fin (c i)) (i:I) :
    Nat.ModEq (c i) (∑j,(a j).val * weight c j) ((a i).val*weight c i) := by
  apply Nat.sum_modEq_single
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
  · intro j _ hne
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (divides_other_weight c hne.symm) _)

theorem exponent_injective (c:I→ℕ)
    (hc:Pairwise (fun i j => Nat.Coprime (c i) (c j))) :
    Function.Injective (fun a:∀i,Fin (c i) => ∑i,(a i).val*weight c i) := by
  intro a b hab
  funext i
  apply Fin.ext
  have heq : Nat.ModEq (c i) (∑j,(a j).val*weight c j)
      (∑j,(b j).val*weight c j) := congrArg (fun n => n % c i) hab
  have he := (exponent_congr c a i).symm.trans
    (heq.trans (exponent_congr c b i))
  exact (he.cancel_right_of_coprime (weight_coprime c hc i)).eq_of_lt_of_lt
    (a i).isLt (b i).isLt

theorem exponent_bound (c:I→ℕ) (a:∀i,Fin (c i)) :
    (∑i,(a i).val*weight c i) ≤ Fintype.card I*(∏i,c i) := by
  calc
    _ ≤ ∑i,c i*weight c i := Finset.sum_le_sum (fun i _ =>
      Nat.mul_le_mul_right _ (Nat.le_of_lt (a i).isLt))
    _ = _ := by simp only [mul_weight,Finset.sum_const,Finset.card_univ,smul_eq_mul]

#print axioms exponent_injective

end SpanningCRTExponents
