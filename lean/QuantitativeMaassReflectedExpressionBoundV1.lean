module

public import QuantitativeMaassConcreteExpressionWindowV1
public import QuantitativeMaassCylinderReflectedFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

private theorem reflected_cutoff_branch_integral (S B : Set ℍ) (hS : MeasurableSet S)
    (hSB : S⊆B) (a u : ℍ→ℂ) :
    (∫ x in B,(S.indicator a x*u x).re)=∫ x in S,(a x*u x).re := by
  have he : (fun x => (S.indicator a x*u x).re)=S.indicator (fun x => (a x*u x).re) := by
    funext x
    classical
    by_cases hx : x∈S <;> simp [hx]
  rw [he,integral_indicator hS,Measure.restrict_restrict hS,inter_eq_left.mpr hSB]

theorem concrete_reflected_branch_window_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (b : Branch) (M : IntegerMatrix2)
      (_hM : IntegerAction b.label M) (_hpos : 0<M.det)
      (S : Set ℍ) (_hS : MeasurableSet S) (L R ε t : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t → S⊆Metric.closedBall o L →
      |∫ x in S,(cylinderInputBranchCoefficient b (J•x)*radialPoincareKernel 0
        (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•(J•x))).re| ≤
        (b.bound*(integralMatrixHeight M)^40)*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_reflected_branch_uniform_height K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro b M hM hpos S hS L R ε t hR hL hε hε1 ht hSB
  let a := S.indicator (fun x => cylinderInputBranchCoefficient b (J•x))
  have hba (z : ℍ) : ‖a z‖≤b.bound :=
    (norm_indicator_le_norm_self _ z).trans (cylinderInputBranchCoefficient_bound b (J•z))
  have hh := hbound M hpos L R ε t hR hL hε hε1 ht a b.bound b.bound_nonneg
    (Eventually.of_forall hba)
  have hact (x : ℍ) : positiveIntegralGL M hpos•x=b.label•x := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional,hM.2]
  change |∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
    (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x
      (positiveIntegralGL M hpos•(J•x))).re|≤_ at hh
  simp only [hact] at hh
  rw [reflected_cutoff_branch_integral S _ hS hSB] at hh
  exact hh

/-- Uniform reflected finite-expression bound, with no diagonal main term.
The bound remains quantitative when the list and its matrix heights grow. -/
theorem concrete_reflected_expression_window_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (E : Expression) (B : ℝ),0≤B →
      ExpressionMatrixBound E B → ∀ (S : Set ℍ) (_hS : MeasurableSet S)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t → S⊆Metric.closedBall o L →
      |(E.map (fun b => ∫ x in S,(cylinderInputBranchCoefficient b (J•x)*radialPoincareKernel 0
        (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•(J•x))).re)).sum|≤
      expressionBound E*(1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := concrete_reflected_branch_window_bound K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro E B hB hE S hS L R ε t hR hL hε hε1 ht hSB
  let f := fun b : Branch => ∫ x in S,(cylinderInputBranchCoefficient b (J•x)*radialPoincareKernel 0
    (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•(J•x))).re
  let Z := (1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)
  have hb (b : Branch) (hb : b∈E) : |f b|≤b.bound*Z := by
    have hb0 := b.bound_nonneg
    obtain ⟨M,hM,hMB⟩ := hE b hb
    obtain ⟨hpos,_⟩ := integerAction_positive_real hM
    have hh := hbound b M hM hpos S hS L R ε t hR hL hε hε1 ht hSB
    have hp := pow_le_pow_left₀ (zero_le_one.trans (integralMatrixHeight_bounds M).1)
      (integralMatrixHeight_le_of_entry_bound hMB) 40
    apply hh.trans
    calc
      _ = (integralMatrixHeight M)^40*(b.bound*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) := by ring
      _ ≤ (1+4*B)^40*(b.bound*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by dsimp only [Z]; ring
  have hl : ∀ F : Expression,(∀ b∈F,b∈E) → |(F.map f).sum|≤expressionBound F*Z := by
    intro F
    induction F with
    | nil => intro _;simp [expressionBound]
    | cons b F ih =>
      intro hf
      have hb' := hb b (hf b List.mem_cons_self)
      have ht' := ih (fun c hc => hf c (List.mem_cons_of_mem b hc))
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans ((add_le_add hb' ht').trans_eq (by
        simp only [expressionBound,List.map_cons,List.sum_cons]
        ring))
  convert hl E (fun _ h => h) using 1
  dsimp only [Z]
  ring

#print axioms concrete_reflected_branch_window_bound
#print axioms concrete_reflected_expression_window_bound

end QuantitativeMaass
