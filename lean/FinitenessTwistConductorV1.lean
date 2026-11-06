module

public import FinitenessFiniteOrderClosureV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessTwistConductor

def excess (N p α : ℕ) : ℕ := 2*α-N.factorization p

def ratio (N q : ℕ) : ℕ := Nat.lcm N (q^2)/N

theorem ratio_pos {N q : ℕ} (hN : 0<N) (hq : 0<q) : 0<ratio N q := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (Nat.lcm_pos hN (pow_pos hq _)) (Nat.dvd_lcm_left _ _)
  · exact hN

theorem mul_ratio (N q : ℕ) : N*ratio N q=Nat.lcm N (q^2) :=
  Nat.mul_div_cancel' (Nat.dvd_lcm_left _ _)

theorem ratio_factorization {N q : ℕ} (hN : 0<N) (hq : 0<q) (p : ℕ) :
    (ratio N q).factorization p=excess N p (q.factorization p) := by
  unfold ratio excess
  rw [Nat.factorization_div (Nat.dvd_lcm_left _ _),
    Nat.factorization_lcm hN.ne' (pow_ne_zero _ hq.ne'),Nat.factorization_pow]
  simp only [Finsupp.tsub_apply,Finsupp.sup_apply,Finsupp.smul_apply,smul_eq_mul]
  omega

/-- The exact conductor quotient, with no coprimality restriction on N,q. -/
theorem ratio_product {N q : ℕ} (hN : 0<N) (hq : 0<q) :
    ratio N q=∏ p ∈ q.primeFactors, p^(excess N p (q.factorization p)) := by
  have hs : (ratio N q).factorization.support⊆q.primeFactors := by
    intro p hp
    have hp' : (ratio N q).factorization p≠0 := Finsupp.mem_support_iff.mp hp
    rw [ratio_factorization hN hq] at hp'
    have hq' : q.factorization p≠0 := by
      intro he
      simp [he,excess] at hp'
    exact Finsupp.mem_support_iff.mpr hq'
  calc
    ratio N q=(ratio N q).factorization.prod (fun p α => p^α) :=
      (Nat.prod_factorization_pow_eq_self (ratio_pos hN hq).ne').symm
    _ = ∏ p ∈ q.primeFactors, p^((ratio N q).factorization p) :=
      Finsupp.prod_of_support_subset _ hs _ (fun _ _ => pow_zero _)
    _ = _ := Finset.prod_congr rfl (fun p _ => by rw [ratio_factorization hN hq])

theorem good_excess {N p : ℕ} (hpN : ¬p ∣ N) (α : ℕ) : excess N p α=2*α := by
  simp [excess,Nat.factorization_eq_zero_of_not_dvd hpN]

theorem simple_bad_valuation {N p : ℕ} (hN : 0<N) (hp : p.Prime)
    (hpN : p ∣ N) (hpsq : ¬p^2 ∣ N) : N.factorization p=1 := by
  have hpos := hp.factorization_pos_of_dvd hN.ne' hpN
  have hnot : ¬2≤N.factorization p := by
    intro h
    exact hpsq ((hp.pow_dvd_iff_le_factorization hN.ne').mpr h)
  omega

theorem simple_bad_excess {N p : ℕ} (hN : 0<N) (hp : p.Prime)
    (hpN : p ∣ N) (hpsq : ¬p^2 ∣ N) (j : ℕ) : excess N p (j+1)=2*j+1 := by
  rw [excess,simple_bad_valuation hN hp hpN hpsq]
  omega

theorem square_bad_excess {N p : ℕ} (hN : 0<N) (hp : p.Prime)
    (hpsq : p^2 ∣ N) : excess N p 1=0 := by
  have h : 2≤N.factorization p := (hp.pow_dvd_iff_le_factorization hN.ne').mp hpsq
  unfold excess
  omega

#print axioms ratio_product
#print axioms simple_bad_excess
#print axioms square_bad_excess

end FinitenessTwistConductor
