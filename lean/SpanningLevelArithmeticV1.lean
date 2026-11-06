module

/- Arithmetic of the actual level lcm(N,q^2), before square roots. -/
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace SpanningLevelArithmetic

def level (N q : ℕ) : ℕ := Nat.lcm N (q^2)

theorem level_pos {N q : ℕ} (hN : 0<N) (hq : 0<q) : 0<level N q := by
  exact Nat.lcm_pos hN (pow_pos hq _)

theorem level_dvd {N d q : ℕ} (hd : d∣q) : level N d∣level N q :=
  Nat.lcm_dvd_lcm_of_dvd_right N (pow_dvd_pow_of_dvd hd 2)

/-- No primality or restriction on p|q is needed, only coprimality to N. -/
theorem level_coprime_mul {N p : ℕ} (hp : Nat.Coprime N p) (q : ℕ) :
    level N (p*q)=p^2*level N q := by
  unfold level
  rw [mul_pow,Nat.lcm_mul_right_right_eq_mul_of_lcm_eq_mul (hp.pow_right 2).lcm_eq_mul]
  exact Nat.mul_comm _ _

#print axioms level_coprime_mul

end SpanningLevelArithmetic
