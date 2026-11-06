module

public import AsymptoticClassicalNewDimensionDifferenceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

/-- A list of distinct simply ramified prime divisors of a level. -/
def SimplePrimesAt (ps : List ℕ) (N : ℕ) : Prop :=
  ps.Nodup ∧ ∀ p ∈ ps, p.Prime ∧ p ∣ N ∧ p.Coprime (N / p)

theorem SimplePrimesAt.tail {p N : ℕ} {ps : List ℕ} (h : SimplePrimesAt (p :: ps) N) :
    SimplePrimesAt ps N :=
  ⟨h.1.of_cons, fun q hq => h.2 q (List.mem_cons_of_mem p hq)⟩

/-- Removing one simple prime leaves every other selected prime simple. -/
theorem SimplePrimesAt.tail_div {p N : ℕ} {ps : List ℕ}
    (hN : 0 < N) (h : SimplePrimesAt (p :: ps) N) : SimplePrimesAt ps (N / p) := by
  have hp := h.2 p (List.mem_cons_self)
  have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hp.2.1) hp.1.pos
  refine ⟨h.1.of_cons, ?_⟩
  intro q hq
  have hqN := h.2 q (List.mem_cons_of_mem p hq)
  have hne : q ≠ p := by
    intro he
    exact (List.nodup_cons.mp h.1).1 (he ▸ hq)
  have hn : ¬q ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq hqN.1 hp.1).mp hd)
  have hqdiv : q ∣ N / p := by
    have hd : q ∣ p * (N / p) := by simpa only [Nat.mul_div_cancel' hp.2.1] using hqN.2.1
    exact (hqN.1.dvd_mul.mp hd).resolve_left hn
  refine ⟨hqN.1, hqdiv, ?_⟩
  have hd : N / p / q ∣ N / q := by
    rw [Nat.div_right_comm]
    exact Nat.div_dvd_of_dvd (by
      have hpq : p.Coprime q := (hqN.1.coprime_iff_not_dvd.mpr hn).symm
      exact hpq.dvd_of_dvd_mul_right (by
        simpa only [Nat.div_mul_cancel hqN.2.1] using hp.2.1))
  exact hqN.2.2.of_dvd_right hd

/-- A coprime fixed base divisor survives removal of a selected prime. -/
theorem base_dvd_div {b N p : ℕ} (hb : b ∣ N) (hp : p ∣ N)
    (hc : p.Coprime b) : b ∣ N / p := by
  exact hc.symm.dvd_of_dvd_mul_left (by
    simpa only [Nat.mul_div_cancel' hp] using hb)

#print axioms SimplePrimesAt.tail
#print axioms SimplePrimesAt.tail_div
#print axioms base_dvd_div

end AsymptoticClassicalDimension
