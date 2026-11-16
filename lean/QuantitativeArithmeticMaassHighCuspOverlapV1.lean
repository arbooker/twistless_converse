module

public import QuantitativeArithmeticMaassOverlapTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open scoped MatrixGroups

namespace QuantitativeArithmeticMaassHighCuspOverlap

/-! Unverified draft. All actions and labels are the actual integral/projective
actions. Closed horizontal endpoints account for the extra one in the count. -/

/-- An integral modular transformation joining two points of height at least
two must have zero lower-left entry. -/
theorem bottom_left_eq_zero_of_high (A : SL(2,ℤ)) (z : ℍ)
    (hz : 2 ≤ z.im) (hAz : 2 ≤ (A • z).im) : A 1 0 = 0 := by
  by_contra hc
  have hcInt : (1 : ℤ) ≤ (A 1 0)^2 := by
    have hcases : A 1 0 ≤ -1 ∨ 1 ≤ A 1 0 := by omega
    rcases hcases with h | h <;> nlinarith
  have hcReal : (1 : ℝ) ≤ (A 1 0 : ℝ)^2 := by exact_mod_cast hcInt
  have hD : Complex.normSq (denom (A : GL (Fin 2) ℝ) z) =
      ((A 1 0 : ℝ)*z.re + (A 1 1 : ℝ))^2 + ((A 1 0 : ℝ)*z.im)^2 := by
    simp [denom, Complex.normSq, pow_two]
  have hDpos : 0 < Complex.normSq (denom (A : GL (Fin 2) ℝ) z) :=
    normSq_denom_pos _ (ne_of_gt z.im_pos)
  have hDlower : z.im^2 ≤ Complex.normSq (denom (A : GL (Fin 2) ℝ) z) := by
    rw [hD]
    have h := mul_le_mul_of_nonneg_right hcReal (sq_nonneg z.im)
    nlinarith [sq_nonneg ((A 1 0 : ℝ)*z.re + (A 1 1 : ℝ))]
  rw [ModularGroup.im_smul_eq_div_normSq] at hAz
  have h := (le_div_iff₀ hDpos).mp hAz
  nlinarith

/-- Scalar signs are already identified in integralLabel; no factor two is
needed when counting the resulting translations. -/
theorem high_label_is_translation (A : SL(2,ℤ)) (z : ℍ)
    (hz : 2 ≤ z.im) (hAz : 2 ≤ (A • z).im) :
    ∃ n : ℤ, integralLabel A = translationLabel (n:ℚ) :=
  triangular_label A (bottom_left_eq_zero_of_high A z hz hAz)

private theorem translation_label_zero : translationLabel (0:ℚ) = 1 := by
  have hu : upperSL 0 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperSL, AsymptoticFreshCRT.upper]
  simpa only [Int.cast_zero, hu, map_one] using (upper_label 0).symm

/-- The integer part of the real coordinate distinguishes projective labels
whose images of one point all lie above height two. -/
theorem label_eq_of_high_floor_eq (A B : SL(2,ℤ)) (z : ℍ)
    (hA : 2 ≤ (A • z).im) (hB : 2 ≤ (B • z).im)
    (hfloor : Int.floor (A • z).re = Int.floor (B • z).re) :
    integralLabel A = integralLabel B := by
  have hAB : (A*B⁻¹) • (B • z) = A • z := by
    simp only [mul_smul, inv_smul_smul]
  have hABhigh : 2 ≤ ((A*B⁻¹) • (B • z)).im := by
    rw [hAB]
    exact hA
  obtain ⟨n, hn⟩ := high_label_is_translation (A*B⁻¹) (B • z) hB hABhigh
  have he : integralLabel A = translationLabel (n:ℚ) * integralLabel B := by
    have h := congrArg (fun a => a*integralLabel B) hn
    simpa only [map_mul, map_inv, inv_mul_cancel_right] using h
  have hz : A • z = translationLabel (n:ℚ) • (B • z) := by
    rw [← integralLabel_action, he, mul_smul, integralLabel_action]
  have hr : (A • z).re = (B • z).re + (n:ℝ) := by
    rw [hz, translation_re]
  have hn0 : n = 0 := by
    rw [hr, Int.floor_add_intCast] at hfloor
    omega
  simpa only [hn0, Int.cast_zero, translation_label_zero, one_mul] using he

/-- Finite collections of distinct actual integral projective labels have
at most W+1 images in a closed width-W high strip. -/
theorem integral_label_card_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (A : ι → SL(2,ℤ)) (z : ℍ) (l : ℝ) (W : ℕ)
    (hinj : Set.InjOn (fun i => integralLabel (A i)) (S : Set ι))
    (hS : ∀ i ∈ S, 2 ≤ (A i • z).im ∧
      l ≤ (A i • z).re ∧ (A i • z).re ≤ l + (W:ℝ)) :
    S.card ≤ W+1 := by
  classical
  let J : Finset ℤ := Finset.Icc (Int.floor l) (Int.floor l + (W:ℤ))
  let enc : S → J := fun i => ⟨Int.floor (A i.val • z).re, by
    apply Finset.mem_Icc.mpr
    constructor
    · exact Int.floor_mono (hS i.val i.property).2.1
    · simpa only [Int.floor_add_natCast] using
        Int.floor_mono (hS i.val i.property).2.2⟩
  have he : Function.Injective enc := by
    intro i j hij
    apply Subtype.ext
    apply hinj i.property j.property
    apply label_eq_of_high_floor_eq (A i.val) (A j.val) z
      (hS i.val i.property).1 (hS j.val j.property).1
    exact congrArg Subtype.val hij
  have hcard : Fintype.card J = W+1 := by
    simp only [Fintype.card_coe, J, Int.card_Icc]
    omega
  have h := Fintype.card_le_of_injective enc he
  rw [hcard] at h
  simpa only [Fintype.card_coe] using h

/-- The uniform overlap bound for the actual projective congruence group.
The initial point may have any height; only its selected images are high. -/
theorem gamma_high_strip_card_bound (N W : ℕ) (S : Finset (gamma N))
    (z : ℍ) (l : ℝ)
    (hS : ∀ g ∈ S, 2 ≤ (g.val • z).im ∧
      l ≤ (g.val • z).re ∧ (g.val • z).re ≤ l + (W:ℝ)) :
    S.card ≤ W+1 := by
  classical
  apply integral_label_card_bound S representative z l W
  · intro g hg h hh he
    apply Subtype.ext
    simpa only [representative_label] using he
  · intro g hg
    have he : representative g • z = g.val • z := by
      rw [← integralLabel_action, representative_label]
    simpa only [he] using hS g hg

/-- Uniform overlap in every integral cusp chart, using the literal
projective congruence action and the same closed-interval boundary count. -/
theorem gamma_cusp_high_strip_card_bound (N W : ℕ) (S : Finset (gamma N))
    (s : SL(2,ℤ)) (z : ℍ) (l : ℝ)
    (hS : ∀ g ∈ S, 2 ≤ (s⁻¹ • (g.val • z)).im ∧
      l ≤ (s⁻¹ • (g.val • z)).re ∧ (s⁻¹ • (g.val • z)).re ≤ l + (W:ℝ)) :
    S.card ≤ W+1 := by
  classical
  apply integral_label_card_bound S (fun g => s⁻¹ * representative g) z l W
  · intro g hg h hh he
    apply Subtype.ext
    have he' : integralLabel (s⁻¹) * g.val = integralLabel (s⁻¹) * h.val := by
      simpa only [map_mul, representative_label] using he
    exact mul_left_cancel he'
  · intro g hg
    have he : representative g • z = g.val • z := by
      rw [← integralLabel_action, representative_label]
    simpa only [mul_smul, he] using hS g hg

/-- The same entry obstruction in a genuine integral cusp chart. -/
theorem conjugate_bottom_left_eq_zero_of_high (s A : SL(2,ℤ)) (z : ℍ)
    (hz : 2 ≤ (s⁻¹ • z).im) (hAz : 2 ≤ (s⁻¹ • (A • z)).im) :
    (s⁻¹ * A * s) 1 0 = 0 := by
  apply bottom_left_eq_zero_of_high (s⁻¹*A*s) (s⁻¹ • z) hz
  simpa only [mul_smul, smul_inv_smul] using hAz

#print axioms bottom_left_eq_zero_of_high
#print axioms high_label_is_translation
#print axioms label_eq_of_high_floor_eq
#print axioms integral_label_card_bound
#print axioms gamma_high_strip_card_bound
#print axioms gamma_cusp_high_strip_card_bound
#print axioms conjugate_bottom_left_eq_zero_of_high
end QuantitativeArithmeticMaassHighCuspOverlap
