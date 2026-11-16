module

public import QuantitativeMaassCrossUniformCostV1
public import QuantitativeMaassExpressionGrowthBaseV1
public import QuantitativeMaassStrongMomentScheduleV1
public import QuantitativeMaassReflectionOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open scoped Topology
namespace QuantitativeMaass.CrossCompactBranch

theorem reflected_ball_I (K : Set ℍ) (R : ℝ)
    (hK : K ⊆ Metric.closedBall I R) :
    (fun x : ℍ => J • x) '' K ⊆ Metric.closedBall I R := by
  have hI : J • (I:ℍ) = I := by
    apply UpperHalfPlane.ext
    simp only [coe_J_smul,coe_I,Complex.conj_I,neg_neg]
  rintro _ ⟨x,hx,rfl⟩
  change dist (J • x) I ≤ R
  rw [←hI,reflection_dist]
  exact hK hx

/-- The actual localization and extra input corner preserve the degree
and strong-scale cost bounds used in the geometric remainder estimate.
This applies to both the ordinary and reflected compact regions. -/
theorem scheduled_localExpression_growth (N : ℕ) (E : ℕ → Expression)
    (hE : ExponentialExpressionGrowth E)
    (K L : ℝ → Set ℍ) (hK : ∀ t, IsCompact (K t)) (hL : ∀ t, IsCompact (L t))
    (b₁ b₂ : ℝ → ℍ → ℂ) (hb₁ : ∀ t, Measurable (b₁ t)) (hb₂ : ∀ t, Measurable (b₂ t))
    (hbound₁ : ∀ t x, ‖b₁ t x‖ ≤ 1) (hbound₂ : ∀ t x, ‖b₂ t x‖ ≤ 1)
    (hball : ∀ᶠ t in atTop,
      K t ⊆ Metric.closedBall I (4*Strong.strongScale t) ∧
      L t ⊆ Metric.closedBall I (4*Strong.strongScale t)) :
    let F := fun t => composeExpression
      (localExpression N (K t) (L t) (hK t) (hL t) (b₁ t) (b₂ t) (hb₁ t) (hb₂ t)
        1 1 zero_le_one zero_le_one (hbound₁ t) (hbound₂ t) (E (growingLVDegree t)))
      [corner (L t) (hL t).measurableSet]
    ∃ G H : ℝ, 0 ≤ G ∧ 4 ≤ H ∧ ∀ᶠ t in atTop,
      expressionBound (F t) ≤ Real.exp (G*(growingLVDegree t:ℝ)+H*Strong.strongScale t) ∧
      ExpressionMatrixBound (F t) (Real.exp (G*(growingLVDegree t:ℝ)+H*Strong.strongScale t)) := by
  intro F
  obtain ⟨D,hD,hEc⟩ := hE
  obtain ⟨C,hC,hlocal⟩ := localExpression_uniform_exponent I
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  let G := 2*C*D
  let H := 9*C+1
  refine ⟨G,H,by dsimp only [G]; positivity,by dsimp only [H]; linarith,?_⟩
  filter_upwards [hball,Strong.strongScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))]
    with t ht hs
  let m := growingLVDegree t
  let s := Strong.strongScale t
  let X := D*((m:ℝ)+1)
  let Y := C*(4*s+4*s+X+1)
  have hm : (1:ℝ) ≤ m := by exact_mod_cast growingLVDegree_pos t
  have hs0 : 0 ≤ s := sq_nonneg _
  have hX : 0 ≤ X := mul_nonneg hD (by positivity)
  have hh := hlocal N (K t) (L t) (hK t) (hL t) (b₁ t) (b₂ t) (hb₁ t) (hb₂ t)
    (hbound₁ t) (hbound₂ t) (E m) (4*s) (4*s) X (by positivity) (by positivity)
    hX ht.1 ht.2 (hEc m).1 (hEc m).2
  have hY : Y ≤ G*(m:ℝ)+9*C*s := by
    have hm' : (m:ℝ)+1 ≤ 2*(m:ℝ) := by linarith
    have hh₁ := mul_le_mul_of_nonneg_left hm' (mul_nonneg hC0 hD)
    have hh₂ := mul_le_mul_of_nonneg_left hs hC0
    dsimp only [Y,X,G,s] at *
    nlinarith only [hh₁,hh₂]
  have hY' : Y ≤ G*(m:ℝ)+H*s := by dsimp only [H]; linarith
  have hi : 1+Y ≤ G*(m:ℝ)+H*s := by dsimp only [H,s]; linarith
  constructor
  · change expressionBound (composeExpression _ [corner (L t) (hL t).measurableSet]) ≤ _
    rw [expressionBound_compose]
    simp only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,corner,add_zero,mul_one]
    exact hh.1.trans (Real.exp_le_exp.mpr hY')
  · have hc := expressionMatrixBound_singleton_one (corner (L t) (hL t).measurableSet) rfl
    apply (hh.2.compose hc zero_le_one).mono
    calc
      _ = 2*Real.exp Y := by dsimp only [Y]; ring
      _ ≤ Real.exp 1*Real.exp Y := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (1+Y) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hi

#print axioms reflected_ball_I
#print axioms scheduled_localExpression_growth

end QuantitativeMaass.CrossCompactBranch
