module

public import QuantitativeMaassBroadCorrespondenceV1
public import QuantitativeMaassHeckeGrowingErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap

namespace QuantitativeMaass

def upperBroadRemainder (N p : ℕ) [Fact p.Prime]
    (L : ℝ) (hL : 0 < L) (t τ : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,z => if hM : 0 < M.matrix.det then
      radialIntegralRemainder N M.matrix hM (broadTranslatedProfile L hL t τ) z else 0
  | n+1,M,z => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p), upperBroadRemainder N p L hL t τ n (HeckeUpper.left p j M) z

/-- Quantitative broad-packet remainder for every Hecke word degree.
The constant precedes the prime, the degree, width, frequency and translation. -/
theorem upperBroadRemainder_growing_bound (o : ℍ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (S L t τ : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (n : ℕ) (M : HeckeUpper), 0 < M.matrix.det →
      IntegrableOn (upperBroadRemainder N p L (lt_of_lt_of_le zero_lt_one hL) t τ n M)
        (Metric.closedBall o S) ∧
      (∫ z in Metric.closedBall o S,
        ‖upperBroadRemainder N p L (lt_of_lt_of_le zero_lt_one hL) t τ n M z‖) ≤
      (heckeWordErrorGrowth p)^n*(integralMatrixHeight M.matrix)^40*
        (C*(1+|τ|)*Real.sqrt t*L^6*Real.exp (30*S+10*|τ|)) := by
  obtain ⟨C,hC,hbound⟩ := broadTranslatedProfile_remainder_bound o
  refine ⟨C,hC,?_⟩
  intro N p _ _ S L t τ hL hS ht n M hM
  let E := C*(1+|τ|)*Real.sqrt t*L^6*Real.exp (30*S+10*|τ|)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hQ : 0 ≤ heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth; positivity
  induction n generalizing M with
  | zero =>
    simp only [upperBroadRemainder, dite_eq_left hM, pow_zero, one_mul]
    have hh := hbound N M.matrix hM S L t τ hL hS ht
    refine ⟨hh.1, hh.2.trans_eq ?_⟩
    ring
  | succ n ih =>
    let F (j : Option (ZMod p)) := upperBroadRemainder N p L
      (lt_of_lt_of_le zero_lt_one hL) t τ n (HeckeUpper.left p j M)
    have hi (j : Option (ZMod p)) : IntegrableOn (F j) (Metric.closedBall o S) :=
      (ih _ (heckeUpper_left_det_pos p j M hM)).1
    have hsum : IntegrableOn (fun z => ∑ j : Option (ZMod p), ‖F j z‖)
        (Metric.closedBall o S) :=
      integrable_finsetSum Finset.univ (fun j _ => (hi j).norm)
    refine ⟨(integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul _, ?_⟩
    have hfin (j : Option (ZMod p)) :
        (∫ z in Metric.closedBall o S, ‖F j z‖) ≤
          (heckeWordErrorGrowth p)^n*((9*(p:ℝ))^40*(integralMatrixHeight M.matrix)^40)*E := by
      apply (ih _ (heckeUpper_left_det_pos p j M hM)).2.trans
      have hh := pow_le_pow_left₀ (le_trans zero_le_one (integralMatrixHeight_bounds _).1)
        (heckeUpper_left_height p j M) 40
      rw [mul_pow] at hh
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (pow_nonneg hQ _)) hE
    calc
      _ ≤ α*(∑ j : Option (ZMod p), ∫ z in Metric.closedBall o S, ‖F j z‖) := by
        change (∫ z in Metric.closedBall o S, ‖(α:ℂ)*∑ j : Option (ZMod p), F j z‖) ≤ _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left _ hα
        rw [← integral_finsetSum Finset.univ (fun j _ => (hi j).norm)]
        apply integral_mono (integrable_finsetSum Finset.univ (fun j _ => hi j)).norm hsum
        intro z
        exact norm_sum_le _ _
      _ ≤ α*(∑ _j : Option (ZMod p),
          (heckeWordErrorGrowth p)^n*((9*(p:ℝ))^40*(integralMatrixHeight M.matrix)^40)*E) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hfin j)) hα
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, ZMod.card,
          Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
        rw [pow_succ (heckeWordErrorGrowth p) n]
        unfold heckeWordErrorGrowth
        dsimp only [α, E]
        ring

#print axioms upperBroadRemainder_growing_bound

end QuantitativeMaass
