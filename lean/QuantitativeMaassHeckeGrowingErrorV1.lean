module

public import QuantitativeMaassHeckeWordRemainderV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Explicit exponential cost per Hecke letter in the nonscalar estimate. -/
def heckeWordErrorGrowth (p : ℕ) : ℝ :=
  (Real.sqrt (p:ℝ))⁻¹*((p:ℝ)+1)*(9*(p:ℝ))^40

/-- A uniform estimate for every finite Hecke degree, with no fixed-degree
limit or assumed trace bound. It retains the square-root spectral saving. -/
theorem upperWindowRemainder_growing_bound
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      ∀ (n : ℕ) (M : HeckeUpper),0<M.matrix.det →
      (∫ z in Metric.closedBall o L,‖upperWindowRemainder N p K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) n M z‖)≤
        (heckeWordErrorGrowth p)^n*(integralMatrixHeight M.matrix)^40*
          (C*Real.sqrt t*ε^2*Real.exp (A*R+30*L)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowIntegralRemainder_uniform_height_bound K he hc o
  refine ⟨A,C,hA,hC,?_⟩
  intro N p _ _ L R ε t hR hL hε hε1 ht n M hM
  let E := C*Real.sqrt t*ε^2*Real.exp (A*R+30*L)
  have hE : 0≤E := by dsimp only [E];positivity
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  have hα : 0≤α := by dsimp only [α];positivity
  have hQ : 0≤heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth;positivity
  change _≤(heckeWordErrorGrowth p)^n*(integralMatrixHeight M.matrix)^40*E
  induction n generalizing M with
  | zero =>
    simp only [upperWindowRemainder,dite_eq_left hM,pow_zero,one_mul]
    have hh := (hbound N M.matrix hM L R ε t hR hL hε hε1 ht).2
    convert hh using 1
    dsimp only [E]
    ac_rfl
  | succ n ih =>
    let F (j : Option (ZMod p)) := upperWindowRemainder N p K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) n (HeckeUpper.left p j M)
    have hi (j : Option (ZMod p)) : IntegrableOn (F j) (Metric.closedBall o L) :=
      (upperWindowRemainder_continuous N p K he hc R _ _ _ n _
        (heckeUpper_left_det_pos p j M hM)).continuousOn.integrableOn_compact (isCompact_closedBall o L)
    have hsum : IntegrableOn (fun z => ∑ j : Option (ZMod p),‖F j z‖) (Metric.closedBall o L) :=
      integrable_finsetSum Finset.univ (fun j _ => (hi j).norm)
    have hfin (j : Option (ZMod p)) :
        (∫ z in Metric.closedBall o L,‖F j z‖)≤
        (heckeWordErrorGrowth p)^n*((9*(p:ℝ))^40*(integralMatrixHeight M.matrix)^40)*E := by
      apply (ih _ (heckeUpper_left_det_pos p j M hM)).trans
      have hh := pow_le_pow_left₀ (le_trans zero_le_one (integralMatrixHeight_bounds _).1)
        (heckeUpper_left_height p j M) 40
      rw [mul_pow] at hh
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (pow_nonneg hQ _)) hE
    calc
      _ ≤ α*(∑ j : Option (ZMod p),∫ z in Metric.closedBall o L,‖F j z‖) := by
        change (∫ z in Metric.closedBall o L,‖(α:ℂ)*∑ j : Option (ZMod p),F j z‖)≤_
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα]
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left _ hα
        rw [←integral_finsetSum Finset.univ (fun j _ => (hi j).norm)]
        apply integral_mono (integrable_finsetSum Finset.univ (fun j _ => hi j)).norm hsum
        intro z
        exact norm_sum_le _ _
      _ ≤ α*(∑ _j : Option (ZMod p),
          (heckeWordErrorGrowth p)^n*((9*(p:ℝ))^40*(integralMatrixHeight M.matrix)^40)*E) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hfin j)) hα
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,ZMod.card,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
        rw [pow_succ (heckeWordErrorGrowth p) n]
        unfold heckeWordErrorGrowth
        dsimp only [α]
        ac_rfl

#print axioms upperWindowRemainder_growing_bound

end QuantitativeMaass
