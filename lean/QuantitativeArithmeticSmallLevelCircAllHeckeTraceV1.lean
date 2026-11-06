module

public import QuantitativeArithmeticSmallLevelCircHeckeAdjointV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp

/-- Every ordinary trace equation of Mcirc survives every prime Hecke
operator, including at the prime of the trace itself. -/
theorem allPrimeHecke_first_trace_zero (N p k : ℕ) [NeZero N] (hN : 0 < N)
    (hp : p.Prime) (hk : Even k) (F : ModularForm (level N) (k : ℤ))
    (hF : F ∈ space N hN k) (q : {q : ℕ // q.Prime ∧ q ∣ N}) :
    primeTrace N hN (k : ℤ) q (ModularHecke.primeHecke N p hp (k : ℤ) F) = 0 := by
  rcases q with ⟨q, hq, hqN⟩
  obtain ⟨M, rfl⟩ := hqN
  have hM : 0 < M := Nat.pos_of_mul_pos_left hN
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have ht := factor_traces M q k hq hM F hF
  dsimp only at ht
  rw [primeTrace_factor_zero_iff M q hq hN (k : ℤ)]
  by_cases hpq : p = q
  · subst p
    let : Fact q.Prime := ⟨hq⟩
    simp only [ModularHecke.primeHecke, Nat.dvd_mul_right q M, ite_true]
    by_cases hqM : q ∣ M
    · rw [ModularHecke.upperTrace_repeated_zero_of_trace M q hq hqM (k : ℤ) F ht.2,
        map_zero]
    · have hc : q.Coprime M := hq.coprime_iff_not_dvd.mpr hqM
      have hAB : (q : ℤ)*Nat.gcdA q M+(M : ℤ)*Nat.gcdB q M=1 := by
        have hh := Nat.gcd_eq_gcd_ab q M
        rw [hc.gcd_eq_one, Nat.cast_one] at hh
        exact hh.symm
      rw [ModularHecke.upperTrace_simple_eq_neg_local M q hM hqM
        (Nat.gcdA q M) (Nat.gcdB q M) hAB (k : ℤ) F ht.2, map_neg,
        ModularHecke.localAtkin_trace_zero M q hq.pos (Nat.gcdA q M) (Nat.gcdB q M)
          hAB (k : ℤ) F ht.2, neg_zero]
  · have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
    rw [← dilationTrace_eq_primeHecke (q * M) p k hN hp hk F hF,
      ModularHecke.dilationTrace_cross_trace M p q hM hp.pos hq hc (k : ℤ) F,
      ht.1, map_zero]

#print axioms allPrimeHecke_first_trace_zero
end QuantitativeArithmeticSmallLevelCirc
