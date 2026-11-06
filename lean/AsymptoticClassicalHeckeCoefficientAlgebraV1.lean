module

public import AsymptoticClassicalHeckePrimeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalHeckeCoefficients

/-- The coefficient action of substitution X ↦ X^p. -/
def down (p : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ := if p ∣ n then c (n / p) else 0

theorem down_add (p : ℕ) (c d : ℕ → ℂ) (n : ℕ) :
    down p (fun m => c m + d m) n = down p c n + down p d n := by
  unfold down
  split_ifs <;> simp

theorem down_mul (p : ℕ) (a : ℂ) (c : ℕ → ℂ) (n : ℕ) :
    down p (fun m => a * c m) n = a * down p c n := by
  unfold down
  split_ifs <;> simp

theorem down_up (p q : ℕ) (h : p.Coprime q) (c : ℕ → ℂ) (n : ℕ) :
    down p (fun m => c (q * m)) n = down p c (q * n) := by
  unfold down
  simp only [h.dvd_mul_left]
  split_ifs with hn
  · rw [Nat.mul_div_assoc q hn]
  · rfl

theorem down_down (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (c : ℕ → ℂ) (n : ℕ) :
    down p (down q c) n = down q (down p c) n := by
  have he : PowerSeries.expand p hp.ne' (PowerSeries.expand q hq.ne' (PowerSeries.mk c)) =
      PowerSeries.expand q hq.ne' (PowerSeries.expand p hp.ne' (PowerSeries.mk c)) := by
    rw [← AlgHom.comp_apply, ← PowerSeries.expand_mul_eq_comp,
      ← AlgHom.comp_apply, ← PowerSeries.expand_mul_eq_comp]
    simp only [Nat.mul_comm p q]
  have hh := congrArg (fun f : PowerSeries ℂ => f.coeff n) he
  simpa only [PowerSeries.coeff_expand, PowerSeries.coeff_mk, down] using hh

/-- The coefficient action of the classical good-prime operator. -/
def hecke (p : ℕ) (a : ℂ) (c : ℕ → ℂ) (n : ℕ) : ℂ := c (p * n) + a * down p c n

/-- Coprime Hecke coefficient operators commute for arbitrary complex weights. -/
theorem hecke_commute (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (h : p.Coprime q)
    (a b : ℂ) (c : ℕ → ℂ) : hecke p a (hecke q b c) = hecke q b (hecke p a c) := by
  funext n
  change (c (q * (p * n)) + b * down q c (p * n)) +
    a * down p (fun m => c (q * m) + b * down q c m) n =
      (c (p * (q * n)) + a * down p c (q * n)) +
        b * down q (fun m => c (p * m) + a * down p c m) n
  simp only [down_add, down_mul, down_up p q h, down_up q p h.symm,
    down_down p q hp hq, Nat.mul_left_comm p q n]
  ring

#print axioms down_add
#print axioms down_mul
#print axioms down_up
#print axioms down_down
#print axioms hecke_commute

end AsymptoticClassicalHeckeCoefficients
