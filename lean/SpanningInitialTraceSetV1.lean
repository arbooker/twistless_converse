module

public import SpanningSmallPrimeDensityV1
public import SpanningFrequencyCountV1
public import SpanningCharacteristicZeroV1

@[expose] public section

namespace SpanningInitialTraceSet

open SpanningSmallPrimeDensity SpanningFrequencyCount SpanningInitialSpectralVanishing
  SpanningCharacteristicZero SpanningActualKernel SpanningLevelArithmetic

theorem totient_density (S:Finset ℕ) (hp:∀p∈S,p.Prime) :
    ((∏p∈S,p).totient:ℝ)=(∏p∈S,(p:ℝ))*density S := by
  rw [totient_prime_product S hp,Nat.cast_prod]
  unfold density
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p h
  have hpos : (0:ℝ)<p := by exact_mod_cast (hp p h).pos
  rw [Nat.cast_sub (hp p h).one_lt.le,Nat.cast_one,mul_sub,mul_one]
  rw [mul_one_div_cancel (ne_of_gt hpos)]

theorem exists_initial_trace_set {N:ℕ} (hN:0<N) :
    ∃(S:Finset ℕ) (D:ℕ),0<D ∧ N∣D ∧
      (∀p∈S,p.Prime ∧ Nat.Coprime N p ∧ p∣D) ∧
      ∀f:ℤ → ℚ,Augmented N (S:Set ℕ) D f → f=0 := by
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  obtain ⟨S,hS,hρ⟩ := arbitrarily_small_density N (one_div_pos.mpr hsqrt)
  let P := ∏p∈S,p
  have hP : 0<P := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
  have hprime : ∀p∈S,p.Prime := fun p hp => (hS p hp).1
  have hdiv : ∀p∈S,p∣N*P := fun p hp =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) N
  refine ⟨S,N*P,Nat.mul_pos hN hP,dvd_mul_right _ _,?_,?_⟩
  · intro p hp
    refine ⟨hprime p hp,?_,hdiv p hp⟩
    apply Nat.Coprime.symm
    apply (hprime p hp).coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le.mpr (hS p hp).2) (Nat.le_of_dvd hN hd)
  · apply rational_augmented_zero_of_spectral_count (Nat.mul_pos hN hP) hdiv
    rw [remaining_count S hprime N,Nat.cast_mul,totient_density S hprime]
    rw [←Nat.cast_prod]
    change (N:ℝ)*((P:ℝ)*density S)<radius N (N*P) 1
    have hmul := mul_lt_mul_of_pos_left hρ
      (show (0:ℝ)<N*P by exact_mod_cast Nat.mul_pos hN hP)
    simpa only [radius,level,Nat.one_pow,Nat.lcm_one_right,Nat.cast_mul,
      mul_assoc,mul_one_div] using hmul

#print axioms exists_initial_trace_set

end SpanningInitialTraceSet
