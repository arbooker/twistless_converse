module

public import QuantitativeMaassZeroExtensionTwistsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

theorem coprime_twist_conductor (N a b : ℕ) (hc : a.Coprime b) :
    Nat.lcm (Nat.lcm N (a^2)) (b^2)=Nat.lcm N ((a*b)^2) := by
  rw [Nat.lcm_assoc,((hc.pow_left 2).pow_right 2).lcm_eq_mul,mul_pow]

/-- Adding a simply ramified prime-power factor to an already proved
reflection law. The ramified equation is inherited from the original function. -/
theorem analytic_twist_simple_extension (N M p q : ℕ) (hM : 0<M) (hp : p.Prime)
    (hq : 0<q) (hc : M.Coprime p) (hpq : p.Coprime q)
    (hL : Nat.lcm N (q^2)=p*M) (k : ℕ)
    (F : ℂ → ℂ) (hF : Function.Periodic F 1) (w δ : ℂ) (hδ : δ^2=1)
    (hU : ∀ z,ramifiedAverage p F z=δ*F z)
    (hW : ∀ z,w*FinitenessAnalyticReconstruction.twist F q
      (-1/((Nat.lcm N (q^2):ℂ)*z))=FinitenessAnalyticReconstruction.twist F q z)
    (z : ℂ) (hz : z≠0) :
    FinitenessAnalyticReconstruction.twist F (q*p^(k+1)) z=
      (-w*δ)*FinitenessAnalyticReconstruction.twist F (q*p^(k+1))
        (-1/((Nat.lcm N ((q*p^(k+1))^2):ℂ)*z)) := by
  have he := simple_prime_power_analytic_law M p hM hp hc k
    (FinitenessAnalyticReconstruction.twist F q) w δ hδ
    (analytic_twist_ramified F hF p q hp.pos hq hpq δ hU)
    (by simpa only [hL] using hW) z hz
  have htw (t : ℂ) : FinitenessAnalyticReconstruction.twist
      (FinitenessAnalyticReconstruction.twist F q) (p^(k+1)) t=
      FinitenessAnalyticReconstruction.twist F (q*p^(k+1)) t := by
    rw [←analytic_twist_coprime_mul F hF _ _ (pow_pos hp.pos _) hq (hpq.pow_left _),Nat.mul_comm]
  simp_rw [htw] at he
  rw [←hL,coprime_twist_conductor N q (p^(k+1)) (hpq.symm.pow_right _)] at he
  exact he

/-- The same extension step at a repeated prime; higher powers vanish. -/
theorem analytic_twist_repeated_extension (N p q : ℕ) (hp : p.Prime) (hq : 0<q)
    (hpq : p.Coprime q) (hp2 : p^2∣N) (k : ℕ)
    (F : ℂ → ℂ) (hF : Function.Periodic F 1) (w : ℂ)
    (hU : ∀ z,ramifiedAverage p F z=0)
    (hW : ∀ z,w*FinitenessAnalyticReconstruction.twist F q
      (-1/((Nat.lcm N (q^2):ℂ)*z))=FinitenessAnalyticReconstruction.twist F q z)
    (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F (q*p^(k+1)) z=
      w*FinitenessAnalyticReconstruction.twist F (q*p^(k+1))
        (-1/((Nat.lcm N ((q*p^(k+1))^2):ℂ)*z)) := by
  have hu (t : ℂ) : ramifiedAverage p (FinitenessAnalyticReconstruction.twist F q) t=0 := by
    simpa only [zero_mul] using analytic_twist_ramified F hF p q hp.pos hq hpq 0
      (fun y => by simpa only [zero_mul] using hU y) t
  have htw (t : ℂ) : FinitenessAnalyticReconstruction.twist F (q*p^(k+1)) t=
      FinitenessAnalyticReconstruction.twist
        (FinitenessAnalyticReconstruction.twist F q) (p^(k+1)) t := by
    rw [Nat.mul_comm,analytic_twist_coprime_mul F hF _ _ (pow_pos hp.pos _) hq (hpq.pow_left _)]
  simp_rw [htw]
  rw [←coprime_twist_conductor N q (p^(k+1)) (hpq.symm.pow_right _)]
  cases k with
  | zero =>
    have ht (y : ℂ) : FinitenessAnalyticReconstruction.twist
        (FinitenessAnalyticReconstruction.twist F q) p y=
        -FinitenessAnalyticReconstruction.twist F q y := by
      simpa using analytic_twist_prime_power_of_ramified p hp 0
        (FinitenessAnalyticReconstruction.twist F q) 0
        (fun t => by simpa only [zero_mul] using hu t) y
    rw [Nat.zero_add,pow_one,Nat.lcm_eq_left (hp2.trans (Nat.dvd_lcm_left _ _)),ht,ht,mul_neg,hW]
  | succ k =>
    have ht := analytic_twist_repeated_power_zero p hp k (FinitenessAnalyticReconstruction.twist F q) hu
    simp only [Nat.add_assoc,ht,mul_zero]

#print axioms coprime_twist_conductor
#print axioms analytic_twist_simple_extension
#print axioms analytic_twist_repeated_extension

end QuantitativeMaass
