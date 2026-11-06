module

public import FinitenessAllLevelRegularDegreeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Bornology

/-- Regular parameters can be chosen in an unbounded sequence. -/
theorem codiscrete_escaping_sequence {G : Set ℂ} (hG : G ∈ codiscrete ℂ) :
    ∃ z : ℕ → ℂ, (∀ n, z n ∈ G) ∧ Tendsto z atTop (cobounded ℂ) := by
  have hc : Gᶜ.Countable := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (mem_codiscrete'.mp hG).2
  have hd : Dense G := by simpa only [compl_compl] using hc.dense_compl ℂ
  have hex (n : ℕ) : ∃ z ∈ G, (n : ℝ) < ‖z‖ := by
    have hne : {z : ℂ | (n : ℝ) < ‖z‖}.Nonempty := by
      refine ⟨((n + 1 : ℕ) : ℂ), ?_⟩
      simp only [mem_ofPred_eq, Complex.norm_natCast]
      exact_mod_cast Nat.lt_succ_self n
    obtain ⟨z, hz, hg⟩ := hd.inter_open_nonempty _ (isOpen_lt continuous_const continuous_norm) hne
    exact ⟨z, hg, hz⟩
  choose z hz hn using hex
  refine ⟨z, hz, tendsto_norm_atTop_iff_cobounded.mp ?_⟩
  exact tendsto_atTop_mono (fun n => (hn n).le) tendsto_natCast_atTop_atTop

/-- Forward bounds multiply over a finite fiber, retaining its cardinal. -/
theorem fiber_product_forward {κ : Type*} [Fintype κ] (B : κ → ℝ)
    (hB : ∀ i, 0 ≤ B i) (A C : ℝ) (m q : ℕ)
    (hb : ∀ i, (B i) ^ m ≤ C * (1 + A) ^ q) :
    (∏ i, B i) ^ m ≤ C ^ Fintype.card κ * (1 + A) ^ (q * Fintype.card κ) := by
  calc
    _ = ∏ i, (B i) ^ m := by rw [Finset.prod_pow]
    _ ≤ ∏ _i : κ, C * (1 + A) ^ q := Finset.prod_le_prod₀
      (fun i _ => pow_nonneg (hB i) _) (fun i _ => hb i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, mul_pow, ← pow_mul]

/-- Once every observable norm is at least one, the reverse bounds also
multiply, replacing the product of (1+B) by 2^D times the product of B. -/
theorem fiber_product_reverse {κ : Type*} [Fintype κ] (B : κ → ℝ)
    (hB : ∀ i, 1 ≤ B i) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (m q : ℕ)
    (hb : ∀ i, A ^ m ≤ C * (1 + B i) ^ q) :
    A ^ (m * Fintype.card κ) ≤
      (C ^ Fintype.card κ * 2 ^ (q * Fintype.card κ)) * (∏ i, B i) ^ q := by
  calc
    _ = ∏ _i : κ, A ^ m := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]
    _ ≤ ∏ i, C * (2 * B i) ^ q := Finset.prod_le_prod₀
      (fun _ _ => pow_nonneg hA _) (fun i _ => (hb i).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hB i])
          (by linarith [hB i]) q) hC))
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      mul_pow, ← Finset.prod_pow, ← pow_mul]; ring

/-- The first reverse bound forces all observable norms above one,
uniformly over a fiber as the base norm tends to infinity. -/
theorem observable_one_le {A B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (q : ℕ)
    (hb : A ≤ C * (1 + B) ^ q) (hA : C * 2 ^ q < A) : 1 ≤ B := by
  by_contra! hn
  have hpow : (1 + B) ^ q ≤ (2 : ℝ) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
  exact (not_le_of_gt hA) (hb.trans (mul_le_mul_of_nonneg_left hpow hC))

#print axioms codiscrete_escaping_sequence
#print axioms fiber_product_forward
#print axioms fiber_product_reverse
#print axioms observable_one_le

end FinitenessAllLevelPolynomialPresentation
