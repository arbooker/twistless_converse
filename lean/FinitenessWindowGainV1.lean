module

public import FinitenessCertificateV1

@[expose] public section

namespace FinitenessWindowGain

open FinitenessCertificate SpanningIntegerRows SpanningActualKernel SpanningLevelArithmetic

noncomputable def horizontalBound (Q : ℕ) (u : ℤ) : ℝ :=
  max |(u : ℝ)| |(u : ℝ) + 1| / (Q : ℝ)

theorem row_horizontal_bound {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (i : RowIndex N Q) :
    0 ≤ horizontalBound Q i.val.2 ∧
    (level N i.val.1 : ℝ) * (horizontalBound Q i.val.2)^2 < 1 ∧
    ∀ x : ℝ, (i.val.2 : ℝ) / Q ≤ x → x ≤ ((i.val.2 : ℝ) + 1) / Q →
      (level N i.val.1 : ℝ) * x^2 ≤
        (level N i.val.1 : ℝ) * (horizontalBound Q i.val.2)^2 := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hq : 0 < i.val.1 := Nat.pos_of_dvd_of_pos i.property.1 hQ
  have hL : (0 : ℝ) < level N i.val.1 := by exact_mod_cast level_pos hN hq
  have hs : 0 < Real.sqrt (level N i.val.1) := Real.sqrt_pos.mpr hL
  obtain ⟨hl, hu⟩ := i.property.2
  change -((Q : ℝ) / Real.sqrt (level N i.val.1)) < (i.val.2 : ℝ) at hl
  change (i.val.2 : ℝ) + 1 < (Q : ℝ) / Real.sqrt (level N i.val.1) at hu
  have ha : max |(i.val.2 : ℝ)| |(i.val.2 : ℝ) + 1| <
      (Q : ℝ) / Real.sqrt (level N i.val.1) := by
    apply max_lt
    · exact abs_lt.mpr ⟨hl, by linarith⟩
    · exact abs_lt.mpr ⟨by linarith, hu⟩
  have ha0 : 0 ≤ max |(i.val.2 : ℝ)| |(i.val.2 : ℝ) + 1| :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hb0 : 0 ≤ horizontalBound Q i.val.2 := div_nonneg ha0 hQ'.le
  have hprod : horizontalBound Q i.val.2 * Real.sqrt (level N i.val.1) < 1 := by
    unfold horizontalBound
    rw [div_mul_eq_mul_div, div_lt_iff₀ hQ']
    simpa using (lt_div_iff₀ hs).mp ha
  have hp0 : 0 ≤ horizontalBound Q i.val.2 * Real.sqrt (level N i.val.1) :=
    mul_nonneg hb0 hs.le
  have hsq : (horizontalBound Q i.val.2 * Real.sqrt (level N i.val.1))^2 < 1 := by
    nlinarith
  rw [mul_pow, Real.sq_sqrt hL.le] at hsq
  refine ⟨hb0, by nlinarith, ?_⟩
  intro x hxlo hxhi
  have hlo : -(horizontalBound Q i.val.2) ≤ x := by
    apply le_trans _ hxlo
    unfold horizontalBound
    rw [← neg_div]
    exact div_le_div_of_nonneg_right
      (by have := neg_abs_le (i.val.2 : ℝ); have := le_max_left |(i.val.2 : ℝ)| |(i.val.2 : ℝ)+1|; linarith)
      hQ'.le
  have hhi : x ≤ horizontalBound Q i.val.2 := by
    apply hxhi.trans
    exact div_le_div_of_nonneg_right
      ((le_abs_self _).trans (le_max_right _ _)) hQ'.le
  exact mul_le_mul_of_nonneg_left (by nlinarith) hL.le

/-- An individual strict horizontal margin gives a positive-height margin. -/
theorem individual_gain {L a : ℝ} (hL : 0 < L) (ha : L * a^2 < 1) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ x y : ℝ, L * x^2 ≤ L * a^2 → 0 ≤ y → y ≤ ε →
        L * (x^2 + y^2) ≤ ρ := by
  let ρ : ℝ := (1 + L * a^2) / 2
  let ε : ℝ := Real.sqrt ((1 - L * a^2) / (2 * L))
  have hdiv : 0 < (1 - L * a^2) / (2 * L) := div_pos (by linarith) (by linarith)
  have he : 0 < ε := Real.sqrt_pos.mpr hdiv
  have heq : ε^2 = (1 - L * a^2) / (2 * L) := Real.sq_sqrt hdiv.le
  have heq' : 2 * L * ε^2 = 1 - L * a^2 := by
    rw [heq]
    field_simp
  refine ⟨ε, ρ, he, ?_, ?_, ?_⟩
  · dsimp [ρ]
    nlinarith [mul_nonneg hL.le (sq_nonneg a)]
  · dsimp [ρ]
    linarith
  · intro x y hx hy hye
    have hyy : y^2 ≤ ε^2 := by nlinarith
    have hLy := mul_le_mul_of_nonneg_left hyy hL.le
    dsimp [ρ]
    nlinarith

/-- A single pair of constants works for a finite family of literal rows. -/
theorem finite_gain {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (s : Finset (RowIndex N Q)) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ i ∈ s, ∀ x y : ℝ, (i.val.2 : ℝ) / Q ≤ x →
        x ≤ ((i.val.2 : ℝ) + 1) / Q → 0 ≤ y → y ≤ ε →
        (level N i.val.1 : ℝ) * (x^2 + y^2) ≤ ρ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp
  | @insert i s _ ih =>
      obtain ⟨ε, ρ, he, hr, hr1, hbound⟩ := ih
      obtain ⟨_, ha, hx⟩ := row_horizontal_bound hN hQ i
      have hq : 0 < i.val.1 := Nat.pos_of_dvd_of_pos i.property.1 hQ
      have hL : (0 : ℝ) < level N i.val.1 := by exact_mod_cast level_pos hN hq
      obtain ⟨ε', ρ', he', hr', hr1', hbound'⟩ := individual_gain hL ha
      refine ⟨min ε ε', max ρ ρ', lt_min he he',
        hr.trans_le (le_max_left _ _), max_lt hr1 hr1', ?_⟩
      intro j hj x y hxlo hxhi hy hye
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hbound' x y (hx x hxlo hxhi) hy
          (hye.trans (min_le_right _ _))).trans (le_max_right _ _)
      · exact (hbound j hj x y hxlo hxhi hy
          (hye.trans (min_le_left _ _))).trans (le_max_left _ _)

theorem certificate_gain {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (A : Certificate N Q hQ) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ j : Fin Q, ∀ i ∈ (A.coeff j).support, ∀ x y : ℝ,
        (i.val.2 : ℝ) / Q ≤ x → x ≤ ((i.val.2 : ℝ) + 1) / Q →
        0 ≤ y → y ≤ ε → (level N i.val.1 : ℝ) * (x^2 + y^2) ≤ ρ := by
  classical
  obtain ⟨ε, ρ, he, hr, hr1, hb⟩ :=
    finite_gain hN hQ (Finset.univ.biUnion (fun j : Fin Q => (A.coeff j).support))
  refine ⟨ε, ρ, he, hr, hr1, ?_⟩
  intro j i hi
  exact hb i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩)

/-- The reflected height y/(L|z|²) is uniformly larger than y. -/
theorem reflected_height_gain {L x y ρ : ℝ} (hL : 0 < L) (hy : 0 < y)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hb : L * (x^2 + y^2) ≤ ρ) :
    1 < ρ⁻¹ ∧ ρ⁻¹ * y ≤ y / (L * (x^2 + y^2)) := by
  have hd : 0 < L * (x^2 + y^2) := mul_pos hL (by nlinarith [sq_nonneg x])
  refine ⟨(one_lt_inv₀ hρ).mpr hρ1, ?_⟩
  simpa [div_eq_mul_inv, mul_comm] using div_le_div_of_nonneg_left hy.le hd hb

#print axioms row_horizontal_bound
#print axioms individual_gain
#print axioms certificate_gain
#print axioms reflected_height_gain

end FinitenessWindowGain
