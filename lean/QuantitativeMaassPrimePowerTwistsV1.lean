module

public import QuantitativeMaassRamifiedPowerAveragesV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Finset

namespace QuantitativeMaass

/-- Multiples of p in a finite interval are parametrized by the shorter
interval, with the literal summand retained. -/
theorem sum_multiples_interval (p m : ℕ) (hp : 0<p) (G : ℕ → ℂ) :
    (∑ a ∈ (range (p*m)).filter (fun a => p∣a),G a)=∑ b ∈ range m,G (p*b) := by
  classical
  symm
  apply sum_bij (fun b _ => p*b)
  · intro b hb
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp),
      Nat.dvd_mul_right p b⟩
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hp he
  · intro a ha
    obtain ⟨ha,hd⟩ := mem_filter.mp ha
    obtain ⟨b,rfl⟩ := hd
    exact ⟨b,mem_range.mpr (Nat.lt_of_mul_lt_mul_left (mem_range.mp ha)),rfl⟩
  · intro b _
    rfl

/-- At a prime power, the primitive translation sum is the difference
of two successive complete sums. -/
theorem analytic_twist_prime_power (p : ℕ) (hp : p.Prime) (k : ℕ)
    (F : ℂ → ℂ) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F (p^(k+1)) z=
      (∑ a : Fin (p^(k+1)),F (z+(a.val:ℂ)/(p^(k+1):ℕ)))-
        ∑ a : Fin (p^k),F (z+(a.val:ℂ)/(p^k:ℕ)) := by
  classical
  have hc (a : ℕ) : a.Coprime (p^(k+1)) ↔ ¬p∣a := by
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos k),Nat.coprime_comm,hp.coprime_iff_not_dvd]
  have hs := sum_filter_add_sum_filter_not (range (p^(k+1))) (fun a => p∣a)
    (fun a => F (z+(a:ℂ)/(p^(k+1):ℕ)))
  have hd : (∑ a ∈ (range (p^(k+1))).filter (fun a => p∣a),F (z+(a:ℂ)/(p^(k+1):ℕ)))=
      ∑ a ∈ range (p^k),F (z+(a:ℂ)/(p^k:ℕ)) := by
    rw [pow_succ',sum_multiples_interval p (p^k) hp.pos]
    apply sum_congr rfl
    intro a _
    apply congrArg F
    have hpc : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
    push_cast
    rw [mul_div_mul_left _ _ hpc]
  rw [hd] at hs
  unfold FinitenessAnalyticReconstruction.twist
  simp_rw [hc]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => F (z+(a:ℂ)/(p^(k+1):ℕ))) (p^(k+1)),
    Fin.sum_univ_eq_sum_range (fun a : ℕ => F (z+(a:ℂ)/(p^k:ℕ))) (p^k)]
  linear_combination hs

/-- The actual U_p eigenrelation gives an explicit prime-power primitive
twist, including zero twists when the ramified eigenvalue vanishes. -/
theorem analytic_twist_prime_power_of_ramified (p : ℕ) (hp : p.Prime) (k : ℕ)
    (F : ℂ → ℂ) (δ : ℂ) (hU : ∀ z,ramifiedAverage p F z=δ*F z) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F (p^(k+1)) z=
      δ^(k+1)*F ((p^(k+1):ℕ)*z)-δ^k*F ((p^k:ℕ)*z) := by
  rw [analytic_twist_prime_power p hp k,completeTranslation_pow p hp.pos F δ hU,
    completeTranslation_pow p hp.pos F δ hU]

theorem analytic_twist_repeated_power_zero (p : ℕ) (hp : p.Prime) (k : ℕ)
    (F : ℂ → ℂ) (hU : ∀ z,ramifiedAverage p F z=0) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F (p^(k+2)) z=0 := by
  have he := analytic_twist_prime_power_of_ramified p hp (k+1) F 0
    (fun y => by simpa only [zero_mul] using hU y) z
  simpa only [Nat.add_assoc,zero_pow (by omega : k+1+1≠0),zero_pow (by omega : k+1≠0),
    zero_mul,sub_self] using he

#print axioms sum_multiples_interval
#print axioms analytic_twist_prime_power
#print axioms analytic_twist_prime_power_of_ramified
#print axioms analytic_twist_repeated_power_zero

end QuantitativeMaass
