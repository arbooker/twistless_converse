module

public import QuantitativeArithmeticRetainedCertificateV1
public import FinitenessWindowGainV1
public import FinitenessComplexGeometryV1
public import Mathlib.Data.Finset.Sum

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedWindowGain

open QuantitativeArithmeticRetainedCertificate SpanningIntegerRows
  SpanningLevelArithmetic FinitenessComplexGeometry

/-- Uniform strict-height constants for the legal part of a retained
certificate. The lower bound on `ρ` also accommodates prime dilations. -/
theorem certificate_gain {N Q : ℕ} {P : Finset ℕ}
    (hN : 0 < N) (hQ : 0 < Q) (A : Certificate N P Q hQ) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < 1 ∧ 1 / 2 ≤ ρ ∧
      ∀ j : Fin Q, ∀ i : RowIndex N Q, Sum.inl i ∈ (A.coeff j).support →
        ∀ x y : ℝ, (i.val.2 : ℝ) / Q ≤ x →
          x ≤ ((i.val.2 : ℝ) + 1) / Q → 0 ≤ y → y ≤ ε →
          (level N i.val.1 : ℝ) * (x ^ 2 + y ^ 2) ≤ ρ := by
  classical
  obtain ⟨ε, ρ, he, hr, hr1, hb⟩ := FinitenessWindowGain.finite_gain hN hQ
    (Finset.univ.biUnion (fun j : Fin Q => (A.coeff j).support.toLeft))
  refine ⟨ε, max ρ (1 / 2), he, hr.trans_le (le_max_left _ _),
    max_lt hr1 (by norm_num), le_max_right _ _, ?_⟩
  intro j i hi x y hxlo hxhi hy hye
  have hmem : i ∈ Finset.univ.biUnion (fun j : Fin Q => (A.coeff j).support.toLeft) :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_toLeft.mpr hi⟩
  exact (hb i hmem x y hxlo hxhi hy hye).trans (le_max_left _ _)

/-- The same constants in the shifted complex-coordinate form used by
analytic reconstruction. No restriction is put on the retained rows. -/
theorem certificate_denominator_gain {N Q : ℕ} {P : Finset ℕ}
    (hN : 0 < N) (hQ : 0 < Q) (A : Certificate N P Q hQ) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < 1 ∧ 1 / 2 ≤ ρ ∧
      ∀ j : Fin Q, ∀ i : RowIndex N Q, Sum.inl i ∈ (A.coeff j).support →
        ∀ z : ℂ, (j : ℝ) / Q ≤ z.re → z.re ≤ ((j : ℝ) + 1) / Q →
          0 ≤ z.im → z.im ≤ ε →
          denominator (Nat.lcm N (i.val.1 ^ 2))
            (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q) ≤ ρ := by
  obtain ⟨ε, ρ, he, hr, hr1, hrhalf, hb⟩ := certificate_gain hN hQ A
  refine ⟨ε, ρ, he, hr, hr1, hrhalf, ?_⟩
  intro j i hi z hxlo hxhi hy hye
  have hre : (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q).re =
      z.re + ((i.val.2 : ℝ) - (j : ℝ)) / Q := by simp
  have him : (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q).im = z.im := by simp
  unfold denominator
  rw [hre, him]
  apply hb j i hi _ z.im _ _ hy hye
  · simp only [sub_div]
    linarith
  · simp only [sub_div, add_div] at *
    linarith

/-- Every prime dilation has inverse height ratio at most the chosen ρ. -/
theorem prime_reciprocal_le {p : ℕ} (hp : p.Prime) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) :
    1 / (p : ℝ) ≤ ρ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2).trans hρ

/-- The prime branch reaches at least the same target height y/ρ as
the Fricke branches of the legal reconstruction rows. -/
theorem prime_height_gain {p : ℕ} (hp : p.Prime) {ρ y : ℝ}
    (hρ : 1 / 2 ≤ ρ) (hy : 0 ≤ y) : y / ρ ≤ (p : ℝ) * y := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hρ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hh : 1 ≤ ρ * (p : ℝ) := (div_le_iff₀ hp0).mp (prime_reciprocal_le hp hρ)
  apply (div_le_iff₀ hρ0).mpr
  nlinarith [mul_le_mul_of_nonneg_right hh hy]

#print axioms certificate_gain
#print axioms certificate_denominator_gain
#print axioms prime_reciprocal_le
#print axioms prime_height_gain

end QuantitativeArithmeticRetainedWindowGain
