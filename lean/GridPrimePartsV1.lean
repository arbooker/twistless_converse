module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GridPrimeParts

def primePart (n : ℕ) (S : ℕ → Prop) [DecidablePred S] : ℕ :=
  (n.factorization.filter S).prod (fun p a => p^a)

theorem filter_le (n : ℕ) (S : ℕ → Prop) [DecidablePred S] :
    n.factorization.filter S≤n.factorization := by
  intro p
  simp only [Finsupp.filter_apply]
  split_ifs <;> omega

theorem part_dvd (n : ℕ) (S : ℕ → Prop) [DecidablePred S] : primePart n S∣n :=
  Nat.prod_pow_dvd_of_le_factorization (filter_le n S)

theorem part_ne_zero {n : ℕ} (hn : n≠0) (S : ℕ → Prop) [DecidablePred S] : primePart n S≠0 := by
  intro h
  have hh := part_dvd n S
  rw [h,zero_dvd_iff] at hh
  exact hn hh

theorem factorization_part (n : ℕ) (S : ℕ → Prop) [DecidablePred S] :
    (primePart n S).factorization=n.factorization.filter S :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (filter_le n S)

theorem part_complement {n : ℕ} (hn : n≠0) (S : ℕ → Prop) [DecidablePred S] :
    primePart n S*primePart n (fun p => ¬S p)=n := by
  apply Nat.eq_of_factorization_eq' (mul_ne_zero (part_ne_zero hn S) (part_ne_zero hn (fun p => ¬S p))) hn
  rw [Nat.factorization_mul (part_ne_zero hn S) (part_ne_zero hn (fun p => ¬S p)),
    factorization_part,factorization_part,Finsupp.filter_add_filter_not]

theorem prime_dvd_part {n p : ℕ} (hn : n≠0) (hp : p.Prime)
    (S : ℕ → Prop) [DecidablePred S] : p∣primePart n S ↔ p∣n ∧ S p := by
  rw [hp.dvd_iff_one_le_factorization (part_ne_zero hn S),factorization_part,Finsupp.filter_apply]
  by_cases hS : S p
  · simp only [hS,ite_true,and_true]
    exact (hp.dvd_iff_one_le_factorization hn).symm
  · simp [hS]

theorem parts_coprime {n : ℕ} (hn : n≠0) (S : ℕ → Prop) [DecidablePred S] :
    Nat.Coprime (primePart n S) (primePart n (fun p => ¬S p)) := by
  apply Nat.coprime_of_dvd'
  intro p hp h1 h2
  have hpos := (prime_dvd_part hn hp S).mp h1
  have hneg := (prime_dvd_part hn hp (fun p => ¬S p)).mp h2
  exact False.elim (hneg.2 hpos.2)

theorem divisor_dvd_part {n s : ℕ} (hn : n≠0) (hs : s≠0) (hdiv : s∣n) :
    s∣primePart n (fun p => p∣s) := by
  apply (Nat.factorization_le_iff_dvd hs (part_ne_zero hn _)).mp
  rw [factorization_part]
  intro p
  simp only [Finsupp.filter_apply]
  by_cases hp : p∣s
  · rw [ite_eq_left hp]
    exact (Nat.factorization_le_iff_dvd hs hn).mpr hdiv p
  · rw [ite_eq_right hp,Nat.factorization_eq_zero_of_not_dvd hp]

theorem divisor_complement_coprime {n s : ℕ} (hn : n≠0) :
    Nat.Coprime s (primePart n (fun p => ¬p∣s)) := by
  apply Nat.coprime_of_dvd'
  intro p hp hs hd
  exact False.elim (((prime_dvd_part hn hp _).mp hd).2 hs)

#print axioms part_complement
#print axioms parts_coprime
#print axioms divisor_dvd_part

theorem part_dvd_part {n G : ℕ} (hn : n≠0) (hG : G≠0) (hdiv : n∣G)
    (S : ℕ → Prop) [DecidablePred S] : primePart n S∣primePart G S := by
  apply (Nat.factorization_le_iff_dvd (part_ne_zero hn S) (part_ne_zero hG S)).mp
  rw [factorization_part,factorization_part]
  intro p
  simp only [Finsupp.filter_apply]
  by_cases hp : S p
  · simp only [hp,ite_true]
    exact (Nat.factorization_le_iff_dvd hn hG).mpr hdiv p
  · simp [hp]

#print axioms part_dvd_part

end GridPrimeParts
