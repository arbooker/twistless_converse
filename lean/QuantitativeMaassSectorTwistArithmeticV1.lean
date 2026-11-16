module

public import QuantitativeMaassMixedPowerReflectionV1
public import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AsymptoticSectorSigns

theorem delta_sq {N : ℕ} (e : Sector N) (p : ℕ) : delta e p^2=1 := by
  unfold delta
  split_ifs <;> simp only [sign_sq,one_pow]

theorem multiplier_coprime {N q : ℕ} (e : Sector N) (hc : N.Coprime q) :
    multiplier e q=sign e.1 := by
  classical
  have he : q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hpn
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p,Nat.prime_of_mem_primeFactors hp,hpn.1,Nat.dvd_of_mem_primeFactors hp⟩) hc
  simp only [multiplier,he,Finset.prod_empty,mul_one]

theorem multiplier_prime_power_mul {N : ℕ} (e : Sector N) (q p : ℕ)
    (hq : 0<q) (hp : p.Prime) (hc : p.Coprime q) (k : ℕ) :
    multiplier e (q*p^(k+1))=
      if p∣N ∧ ¬p^2∣N then (-delta e p)*multiplier e q else multiplier e q := by
  classical
  have hn : p∉q.primeFactors := fun h =>
    (hp.coprime_iff_not_dvd.mp hc) (Nat.dvd_of_mem_primeFactors h)
  unfold multiplier
  rw [Nat.primeFactors_mul hq.ne' (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_pow_succ,hp.primeFactors,Finset.union_singleton]
  by_cases h : p∣N ∧ ¬p^2∣N
  · simp only [Finset.filter_insert,ite_eq_left h,
      Finset.prod_insert (show p∉q.primeFactors.filter _ from fun hh => hn (Finset.mem_filter.mp hh).1)]
    ring
  · simp only [Finset.filter_insert,ite_eq_right h]

end AsymptoticSectorSigns

namespace QuantitativeMaass

theorem simple_lcm_factor (N q p : ℕ) (hN : 0<N) (hq : 0<q) (hp : p.Prime)
    (hpN : p∣N) (hp2 : ¬p^2∣N) (hc : p.Coprime q) :
    ∃ M : ℕ,0<M ∧ M.Coprime p ∧ Nat.lcm N (q^2)=p*M := by
  let L := Nat.lcm N (q^2)
  have hL : 0<L := Nat.lcm_pos hN (pow_pos hq 2)
  have hd : p∣L := hpN.trans (Nat.dvd_lcm_left _ _)
  have h₂ : ¬p^2∣L := by
    intro h
    have hx : p^2∣N*q^2 := h.trans (Nat.lcm_dvd_mul _ _)
    exact hp2 (((hc.pow_left 2).pow_right 2).dvd_mul_right.mp hx)
  refine ⟨L/p,Nat.div_pos (Nat.le_of_dvd hL hd) hp.pos,?_,(Nat.mul_div_cancel' hd).symm⟩
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro h
  exact h₂ (by simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hd).mp h)

theorem ramified_prime_power_split (q p : ℕ) (hq : 0<q) (hp : p.Prime) (hd : p∣q) :
    ∃ a k : ℕ,0<a ∧ a<q ∧ p.Coprime a ∧ q=a*p^(k+1) := by
  have ht := hp.factorization_pos_of_dvd hq.ne' hd
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  refine ⟨ordCompl[p] q,k,Nat.ordCompl_pos p hq.ne',?_,Nat.coprime_ordCompl hp hq.ne',?_⟩
  · apply Nat.div_lt_self hq
    rw [hk]
    exact one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero k)
  · have he := Nat.ordProj_mul_ordCompl_eq_self q p
    simpa only [hk,Nat.succ_eq_add_one,Nat.mul_comm] using he.symm

#print axioms AsymptoticSectorSigns.delta_sq
#print axioms AsymptoticSectorSigns.multiplier_coprime
#print axioms AsymptoticSectorSigns.multiplier_prime_power_mul
#print axioms simple_lcm_factor
#print axioms ramified_prime_power_split

end QuantitativeMaass
