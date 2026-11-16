module

public import SpanningCriterionCharacterV1
public import SpanningCriterionObstructionBoundsV1

@[expose] public section

namespace SpanningCriterionObstruction

open GridAdmissibleGap SpanningActualKernel SpanningWindows SpanningTraceAlgebra
  SpanningCriterionCharacter SpanningCriterionObstructionBounds

variable {K : Type*} [Field K]

theorem trace_zero_of_not_coprime {m s q : ℕ} (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) (hqd : q ∣ m*s) (hc : ¬ Nat.Coprime q s) :
    trace q ((m*s)/q) (obstruction m ζ) = 0 := by
  let d := Nat.gcd q s
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right q hs
  have hd : 1 < d := by
    have hh : d ≠ 1 := hc
    omega
  have hdq : d ∣ q := Nat.gcd_dvd_left q s
  have he : d*((q/d)*((m*s)/q)) = m*s := by
    rw [←mul_assoc, Nat.mul_div_cancel' hdq, Nat.mul_div_cancel' hqd]
  have hb : (q/d)*((m*s)/q) = (m*s)/d := by
    conv_rhs => rw [←he]
    rw [Nat.mul_div_cancel_left _ hd0]
  have ht := trace_comp d (q/d) ((m*s)/q) (obstruction m ζ)
  rw [Nat.mul_div_cancel' hdq, hb,
    obstruction_trace_zero hm hs hζ hd (Nat.gcd_dvd_right q s)] at ht
  rw [←ht]
  funext u
  simp [trace]

theorem support_zero_translate {m s q a : ℕ} (hm : 0 < m) (hqd : q ∣ m*s)
    (hc : Nat.Coprime q s) (ha : a < q)
    (hd : (m : ℤ) ∣ (a : ℤ)*((m*s)/q : ℕ)) : a = 0 := by
  obtain ⟨k,hk⟩ := hd
  have he : (q : ℤ)*((m*s)/q : ℕ) = (m : ℤ)*s := by
    exact_mod_cast Nat.mul_div_cancel' hqd
  have he' : (m : ℤ)*((a : ℤ)*s) = (m : ℤ)*((q : ℤ)*k) := by
    calc (m : ℤ)*((a : ℤ)*s) = (a : ℤ)*((q : ℤ)*((m*s)/q : ℕ)) := by
           rw [he]; ring
         _ = (q : ℤ)*((a : ℤ)*((m*s)/q : ℕ)) := by ring
         _ = _ := by rw [hk]; ring
  have hdiv : (q : ℤ) ∣ (a : ℤ)*s :=
    ⟨k,mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) he'⟩
  have hqa : q ∣ a := by exact_mod_cast hc.isCoprime.dvd_of_dvd_mul_right hdiv
  exact Nat.eq_zero_of_dvd_of_lt hqa ha

theorem trace_zero_legal {N m s q : ℕ} (hN : 0 < N) (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) (hbad : s^2 ≤ levelPart N s)
    (hqd : q ∣ m*s) {u : ℤ} (hu : Legal (radius N (m*s) q) u) :
    trace q ((m*s)/q) (obstruction m ζ) u = 0 := by
  by_cases hc : Nat.Coprime q s
  · have hq : 0 < q := Nat.pos_of_dvd_of_pos hqd (Nat.mul_pos hm hs)
    apply Finset.sum_eq_zero
    intro a ha
    have haq : a < q := Finset.mem_range.mp ha
    by_cases hd : (m : ℤ) ∣ u + a*((m*s)/q : ℕ)
    · have hu0 := legal_support_translate_zero hN hq hm hs hqd hc hbad hu a hd
      subst u
      simp only [zero_add] at hd
      have ha0 := support_zero_translate hm hqd hc haq hd
      subst a
      simpa only [Nat.cast_zero, zero_mul, zero_add] using obstruction_zero m ζ
    · exact obstruction_off_support hd
  · exact congrFun (trace_zero_of_not_coprime hm hs hζ hqd hc) u

/-- The explicit nonzero obstruction annihilates every legal row and every
retained complete row if the arithmetic criterion fails at `s`. -/
theorem augmented_obstruction {N m s : ℕ} (hN : 0 < N) (hm : 0 < m) (hs : 2 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) (hbad : s^2 ≤ levelPart N s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hps : ∀ p ∈ P, p ∣ s) :
    Augmented N (P : Set ℕ) (m*s) (obstruction m ζ) ∧ obstruction m ζ ≠ 0 := by
  refine ⟨⟨⟨obstruction_cyclic hm (by omega) hζ,?_⟩,?_⟩,
    obstruction_nonzero hm hs hζ⟩
  · intro q hq u hu
    exact trace_zero_legal hN hm (by omega) hζ hbad hq hu
  · intro p hp
    exact obstruction_trace_zero hm (by omega) hζ (hP p hp).one_lt (hps p hp)

#print axioms augmented_obstruction

end SpanningCriterionObstruction
