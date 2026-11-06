module

public import FinitenessAllLevelSymmetricAnalyticV1
public import Mathlib.Analysis.Polynomial.MahlerMeasure

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Polynomial

/-- A uniform bound for elementary symmetric coefficients, with the
fiber degree retained explicitly. -/
theorem root_product_coeff_bound {κ : Type*} [Fintype κ] (b : κ → ℂ)
    (M : ℝ) (hb : ∀ i, ‖b i‖ ≤ M) (n : ℕ) :
    ‖(∏ i, (Polynomial.X - Polynomial.C (b i))).coeff n‖ ≤
      (Fintype.card κ).choose n * (max 1 M) ^ Fintype.card κ := by
  classical
  have hd : (∏ i, (Polynomial.X - Polynomial.C (b i))).natDegree = Fintype.card κ := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (b i))]
    simp
  have hm (s : Finset κ) : (∏ i ∈ s, (Polynomial.X - Polynomial.C (b i))).mahlerMeasure =
      ∏ i ∈ s, max 1 ‖b i‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Polynomial.mahlerMeasure_mul,
        Polynomial.mahlerMeasure_X_sub_C, ih]
  have hbound : (∏ i, max 1 ‖b i‖) ≤ (max 1 M) ^ Fintype.card κ := by
    calc
      _ ≤ ∏ _i : κ, max 1 M := Finset.prod_le_prod₀
        (fun i _ => le_trans zero_le_one (le_max_left _ _))
        (fun i _ => max_le_max_left 1 (hb i))
      _ = _ := by simp
  calc
    _ ≤ _ := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure n _
    _ ≤ _ := by rw [hd, hm]; exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

variable {X : Type*}

/-- Fiber polynomials are monic with degree equal to the number of actual
points, rather than the number of distinct observable values. -/
theorem fiberPolynomial_monic_degree (R : ℂ → X → Prop) (b : X → ℂ)
    (z : ℂ) (hf : {x | R z x}.Finite) :
    (fiberPolynomial R b z).Monic ∧ (fiberPolynomial R b z).natDegree = Nat.card {x | R z x} := by
  classical
  let := hf.fintype
  rw [fiberPolynomial, finprod_eq_prod_of_fintype]
  refine ⟨Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _), ?_⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
  simp [Nat.card_eq_fintype_card]

/-- Polynomial growth of one observable gives polynomial growth of every
fiber coefficient on any set where the fiber degree is fixed. -/
theorem fiberPolynomial_coeff_growth (R : ℂ → X → Prop) (b : X → ℂ)
    (z : ℂ) (hf : {x | R z x}.Finite) (D k : ℕ)
    (hD : Nat.card {x | R z x} = D) {C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ x, R z x → ‖b x‖ ≤ C * (1 + ‖z‖) ^ k) (n : ℕ) :
    ‖(fiberPolynomial R b z).coeff n‖ ≤
      ((D.choose n : ℝ) * C ^ D) * (1 + ‖z‖) ^ (k * D) := by
  classical
  let := hf.fintype
  have hcard : Fintype.card {x | R z x} = D := by rwa [← Nat.card_eq_fintype_card]
  have hM : 1 ≤ C * (1 + ‖z‖) ^ k :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by linarith [norm_nonneg z]))
  have h := root_product_coeff_bound (fun x : {x | R z x} => b x.val)
    (C * (1 + ‖z‖) ^ k) (fun x => hb x.val x.property) n
  simpa only [fiberPolynomial, finprod_eq_prod_of_fintype, hcard,
    max_eq_right hM, mul_pow, ← pow_mul, mul_assoc] using h

#print axioms root_product_coeff_bound
#print axioms fiberPolynomial_monic_degree
#print axioms fiberPolynomial_coeff_growth

end FinitenessAllLevelPolynomialPresentation
