module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The real-variable iteration in the direct-height proof. No boundedness
at height zero, strict low-height contraction, or attained supremum is assumed.
The analytic application must separately construct its finite tail envelope. -/

namespace FinitenessHeightEnvelope

theorem finite_ascent (E : ℝ → ℝ) {ε r : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hanti : AntitoneOn E (Set.Ioi 0))
    (hstep : ∀ y, 0 < y → y < ε → E y ≤ max (E ε) (E (r * y)))
    (n : ℕ) : ∀ y, 0 < y → ε ≤ r ^ n * y → E y ≤ E ε := by
  induction n with
  | zero =>
      intro y hy hn
      simp only [pow_zero, one_mul] at hn
      exact hanti hε hy hn
  | succ n ih =>
      intro y hy hn
      by_cases he : ε ≤ y
      · exact hanti hε hy he
      · apply (hstep y hy (lt_of_not_ge he)).trans
        apply max_le le_rfl
        apply ih (r * y) (mul_pos (by linarith) hy)
        calc
          ε ≤ r ^ (n + 1) * y := hn
          _ = r ^ n * (r * y) := by rw [pow_succ]; ring

theorem localization (E : ℝ → ℝ) {ε r : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hanti : AntitoneOn E (Set.Ioi 0))
    (hstep : ∀ y, 0 < y → y < ε → E y ≤ max (E ε) (E (r * y))) :
    ∀ y, 0 < y → E y ≤ E ε := by
  intro y hy
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ε / y) hr
  exact finite_ascent E hε hr hanti hstep n y hy
    (le_of_lt ((div_lt_iff₀ hy).mp hn))

theorem localization_eq (E : ℝ → ℝ) {ε r : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hanti : AntitoneOn E (Set.Ioi 0))
    (hstep : ∀ y, 0 < y → y < ε → E y ≤ max (E ε) (E (r * y)))
    {y : ℝ} (hy : 0 < y) (hye : y ≤ ε) : E y = E ε := by
  exact le_antisymm (localization E hε hr hanti hstep y hy) (hanti hy hε hye)

/-- Supremum contraction does not need a maximizing point. -/
theorem zero_of_contraction {M κ : ℝ} (hM : 0 ≤ M) (hκ : κ < 1)
    (h : M ≤ κ * M) : M = 0 := by
  nlinarith

/-- A pointwise strict bound on a nonempty bounded set contracts its supremum. -/
theorem sSup_zero_of_contraction {S : Set ℝ} (hne : S.Nonempty)
    (hpos : 0 ≤ sSup S) {κ : ℝ} (hκ : κ < 1)
    (h : ∀ x ∈ S, x ≤ κ * sSup S) : sSup S = 0 := by
  exact zero_of_contraction hpos hκ (csSup_le hne h)

def tailSet {ι : Type*} (height value : ι → ℝ) (y : ℝ) : Set ℝ :=
  {a | ∃ i, y ≤ height i ∧ value i = a}

noncomputable def envelope {ι : Type*} (height value : ι → ℝ) (y : ℝ) : ℝ :=
  sSup (tailSet height value y)

theorem envelope_antitone {ι : Type*} (height value : ι → ℝ)
    (hne : ∀ y, 0 < y → (tailSet height value y).Nonempty)
    (hb : ∀ y, 0 < y → BddAbove (tailSet height value y)) :
    AntitoneOn (envelope height value) (Set.Ioi 0) := by
  intro x hx y hy hxy
  apply csSup_le (hne y hy)
  rintro a ⟨i, hi, rfl⟩
  exact le_csSup (hb x hx) ⟨i, hxy.trans hi, rfl⟩

/-- Build the tail recursion from the pointwise upward reconstruction bound.
All finiteness assumptions concern strictly positive heights only. -/
theorem envelope_step {ι : Type*} (height value : ι → ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 1 < r)
    (hne : ∀ y, 0 < y → (tailSet height value y).Nonempty)
    (hb : ∀ y, 0 < y → BddAbove (tailSet height value y))
    (hpoint : ∀ i, 0 < height i → height i < ε →
      value i ≤ envelope height value (r * height i)) :
    ∀ y, 0 < y → y < ε → envelope height value y ≤
      max (envelope height value ε) (envelope height value (r * y)) := by
  intro y hy _
  apply csSup_le (hne y hy)
  rintro a ⟨i, hi, rfl⟩
  by_cases he : ε ≤ height i
  · exact (le_csSup (hb ε hε) ⟨i, he, rfl⟩).trans (le_max_left _ _)
  · have hp : 0 < height i := hy.trans_le hi
    apply (hpoint i hp (lt_of_not_ge he)).trans
    apply le_trans _ (le_max_right _ _)
    exact envelope_antitone height value hne hb
      (mul_pos (by linarith) hy) (mul_pos (by linarith) hp)
      (mul_le_mul_of_nonneg_left hi (by linarith))

theorem pointwise_global_bound {ι : Type*} (height value : ι → ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hne : ∀ y, 0 < y → (tailSet height value y).Nonempty)
    (hb : ∀ y, 0 < y → BddAbove (tailSet height value y))
    (hpoint : ∀ i, 0 < height i → height i < ε →
      value i ≤ envelope height value (r * height i))
    (i : ι) (hi : 0 < height i) : value i ≤ envelope height value ε := by
  apply (le_csSup (hb (height i) hi) ⟨i, le_rfl, rfl⟩).trans
  exact localization (envelope height value) hε hr
    (envelope_antitone height value hne hb)
    (envelope_step height value hε hr hne hb hpoint) (height i) hi

#print axioms localization
#print axioms sSup_zero_of_contraction
#print axioms pointwise_global_bound

end FinitenessHeightEnvelope
