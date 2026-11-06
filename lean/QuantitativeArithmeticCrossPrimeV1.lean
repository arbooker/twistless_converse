module

public import QuantitativeArithmeticCrossPrimeTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCrossPrime

open AsymptoticCongruenceStrip AsymptoticFreshMatrices
open scoped Pointwise

/-- Distinct prime divisors supply the common lowered level. -/
theorem two_prime_level (N p q : ℕ) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
    (hpN : p∣N) (hqN : q∣N) (hpq : p≠q) :
    ∃ M, 0<M ∧ N=p*(q*M) ∧ N/p=q*M ∧ N/q=p*M := by
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  obtain ⟨M,he⟩ := hc.mul_dvd_of_dvd_of_dvd hpN hqN
  have hM : 0<M := by
    by_contra hn
    have hm : M=0 := by omega
    simp [hm] at he
    omega
  have he' : N=p*(q*M) := by rw [he]; ring
  refine ⟨M,hM,he',?_,?_⟩
  · simp [he',hp.ne_zero]
  · rw [show N=q*(p*M) by rw [he']; ring]
    simp [hq.ne_zero]

variable (N p q : ℕ) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
  (hpN : p∣N) (hqN : q∣N) (hpq : p≠q)

include hN hp hq hpN hqN hpq

/-- First-old overgroups at distinct prime divisors commute setwise. -/
theorem first_first_permute :
    (gamma (N/p):Set AsymptoticRationalGroup.Group)*(gamma (N/q):Set AsymptoticRationalGroup.Group)=
    (gamma (N/q):Set AsymptoticRationalGroup.Group)*(gamma (N/p):Set AsymptoticRationalGroup.Group) := by
  obtain ⟨M,hM,_,hNp,hNq⟩ := two_prime_level N p q hN hp hq hpN hqN hpq
  rw [hNp,hNq]
  exact gamma_gamma_permute M p q hM hp hq hpq

/-- Mixed actual old overgroups commute setwise, with no assumption on
the exponents of p or q in N. -/
theorem first_second_permute :
    (gamma (N/p):Set AsymptoticRationalGroup.Group)*
      (frickeOldGroup N (N/q) hN:Set AsymptoticRationalGroup.Group)=
    (frickeOldGroup N (N/q) hN:Set AsymptoticRationalGroup.Group)*
      (gamma (N/p):Set AsymptoticRationalGroup.Group) := by
  obtain ⟨M,hM,he,hNp,hNq⟩ := two_prime_level N p q hN hp hq hpN hqN hpq
  have hk : frickeOldGroup N (N/q) hN=degeneracyGroup (p*M) q hq.pos := by
    rw [hNq]
    have he' : N=q*(p*M) := by rw [he]; ring
    subst N
    simpa only [Nat.mul_left_comm] using
      frickeOldGroup_eq_degeneracy (p*M) q (Nat.mul_pos hp.pos hM) hq.pos
  rw [hNp,hk]
  exact gamma_degeneracy_permute M p q hM hp hq hpq

/-- The reverse mixed pair follows by exchanging the primes. -/
theorem second_first_permute :
    (frickeOldGroup N (N/p) hN:Set AsymptoticRationalGroup.Group)*
      (gamma (N/q):Set AsymptoticRationalGroup.Group)=
    (gamma (N/q):Set AsymptoticRationalGroup.Group)*
      (frickeOldGroup N (N/p) hN:Set AsymptoticRationalGroup.Group) :=
  (first_second_permute N q p hN hq hp hqN hpN hpq.symm).symm

/-- Simultaneous conjugation by the literal global Fricke element gives
the second-old/second-old pair. -/
theorem second_second_permute :
    (frickeOldGroup N (N/p) hN:Set AsymptoticRationalGroup.Group)*
      (frickeOldGroup N (N/q) hN:Set AsymptoticRationalGroup.Group)=
    (frickeOldGroup N (N/q) hN:Set AsymptoticRationalGroup.Group)*
      (frickeOldGroup N (N/p) hN:Set AsymptoticRationalGroup.Group) :=
  permutes_map (gamma (N/p)) (gamma (N/q)) (MulAut.conj (frickeLabel N hN)).toMonoidHom
    (first_first_permute N p q hN hp hq hpN hqN hpq)

/-- Both literal old overgroups, indexed by a Boolean for finite-family consumers. -/
def oldGroup (N : ℕ) (hN : 0<N) (p : ℕ) (second : Bool) :
    Subgroup AsymptoticRationalGroup.Group :=
  if second then frickeOldGroup N (N/p) hN else gamma (N/p)

theorem oldGroups_permute (a b : Bool) :
    (oldGroup N hN p a:Set AsymptoticRationalGroup.Group)*
      (oldGroup N hN q b:Set AsymptoticRationalGroup.Group)=
    (oldGroup N hN q b:Set AsymptoticRationalGroup.Group)*
      (oldGroup N hN p a:Set AsymptoticRationalGroup.Group) := by
  cases a <;> cases b
  · exact first_first_permute N p q hN hp hq hpN hqN hpq
  · exact first_second_permute N p q hN hp hq hpN hqN hpq
  · exact second_first_permute N p q hN hp hq hpN hqN hpq
  · exact second_second_permute N p q hN hp hq hpN hqN hpq

#print axioms first_first_permute
#print axioms first_second_permute
#print axioms second_first_permute
#print axioms second_second_permute
#print axioms oldGroups_permute

end QuantitativeArithmeticCrossPrime
