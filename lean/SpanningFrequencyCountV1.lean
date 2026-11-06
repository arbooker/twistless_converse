module

public import SpanningInitialSpectralVanishingV1
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

namespace SpanningFrequencyCount

open SpanningInitialSpectralVanishing

theorem card_fin_coprime (P:ℕ) :
    ((Finset.univ:Finset (Fin P)).filter (fun i => Nat.Coprime P i.val)).card=P.totient := by
  classical
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact Fin.ext he
  · intro i hi
    obtain ⟨hi,hcop⟩ := Finset.mem_filter.mp hi
    exact ⟨⟨i,Finset.mem_range.mp hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcop⟩,rfl⟩

theorem card_fin_coprime_multiple (M P:ℕ) :
    ((Finset.univ:Finset (Fin (M*P))).filter (fun i => Nat.Coprime P i.val)).card=
      M*P.totient := by
  classical
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [←finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑a:Fin M,∑b:Fin P,if Nat.Coprime P (b.val+P*a.val) then 1 else 0)=_
  simp_rw [Nat.coprime_add_mul_left_right]
  rw [←card_fin_coprime P,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp

theorem prime_product_coprime (S:Finset ℕ) (hp:∀p∈S,p.Prime) (i:ℕ) :
    Nat.Coprime (∏p∈S,p) i ↔ ∀p∈S,¬p∣i := by
  rw [Nat.coprime_prod_left_iff]
  exact forall_congr' (fun p => forall_congr' (fun h => (hp p h).coprime_iff_not_dvd))

theorem remaining_count (S:Finset ℕ) (hp:∀p∈S,p.Prime) (M:ℕ) :
    (remainingFrequencies (M*(∏p∈S,p)) (S:Set ℕ)).card=M*(∏p∈S,p).totient := by
  classical
  have he : remainingFrequencies (M*(∏p∈S,p)) (S:Set ℕ)=
      Finset.univ.filter (fun i:Fin (M*(∏p∈S,p)) => Nat.Coprime (∏p∈S,p) i.val) := by
    ext i
    simp only [remainingFrequencies,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (prime_product_coprime S hp i.val).symm
  rw [he,card_fin_coprime_multiple]

theorem totient_prime_product (S:Finset ℕ) (hp:∀p∈S,p.Prime) :
    (∏p∈S,p).totient=∏p∈S,(p-1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hnot ih =>
    have hpp := hp p (Finset.mem_insert_self _ _)
    have hps : ∀r∈S,r.Prime := fun r hr => hp r (Finset.mem_insert_of_mem hr)
    have hcop : Nat.Coprime p (∏r∈S,r) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro r hr
      exact (hpp.coprime_iff_not_dvd).mpr (by
        intro hd
        have he := (Nat.prime_dvd_prime_iff_eq hpp (hps r hr)).mp hd
        exact hnot (he ▸ hr))
    rw [Finset.prod_insert hnot,Finset.prod_insert hnot,Nat.totient_mul hcop,
      Nat.totient_prime hpp,ih hps]

#print axioms remaining_count
#print axioms totient_prime_product

end SpanningFrequencyCount
