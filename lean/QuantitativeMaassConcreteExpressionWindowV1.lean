module

public import QuantitativeMaassConcreteBranchWindowV1
public import QuantitativeHolomorphicMatrixExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

/-- Actual matrix entry bounds control the height in the geometric kernel
estimate, with no choice of an unrelated projective representative. -/
theorem integralMatrixHeight_le_of_entry_bound {M : IntegerMatrix2} {B : ℝ}
    (hM : MatrixEntryBound M B) : integralMatrixHeight M≤1+4*B := by
  unfold integralMatrixHeight
  linarith [hM 0 0,hM 0 1,hM 1 0,hM 1 1]

/-- The concrete kernel remainder of an arbitrary finite expression has
an explicit coefficient-mass and matrix-height bound. The constants are
independent of the expression, its length, and the moving window. -/
theorem concrete_expression_window_regular_error (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (E : Expression) (B : ℝ),0≤B →
      ExpressionMatrixBound E B → ∀ (S : Set ℍ) (_hS : MeasurableSet S)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      S⊆Metric.closedBall o L → (∀ᵐ z ∂volume.restrict S,z∈strip) →
      |(E.map (fun b => (∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•x)).re)-
        (∫ x in S,(matrix (regular b x) 1 1*
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re))).sum|≤
      expressionBound E*(1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := concrete_branch_window_regular_error K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro E B hB hE S hS L R ε t hR hL hε hε1 ht hSB hstrip
  have hb (b : Branch) (hb : b∈E) :
      |(∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•x)).re)-
        (∫ x in S,(matrix (regular b x) 1 1*
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re)|≤
      b.bound*((1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) := by
    obtain ⟨M,hM,hMB⟩ := hE b hb
    obtain ⟨hpos,_⟩ := integerAction_positive_real hM
    have hh := hbound b M hM hpos S hS L R ε t hR hL hε hε1 ht hSB hstrip
    apply hh.trans
    have hbb : 0≤b.bound := b.bound_nonneg
    have hp := pow_le_pow_left₀ (zero_le_one.trans (integralMatrixHeight_bounds M).1)
      (integralMatrixHeight_le_of_entry_bound hMB) 40
    calc
      _ = (integralMatrixHeight M)^40*(b.bound*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) := by ring
      _ ≤ (1+4*B)^40*(b.bound*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by ring
  have hl : ∀ (F : Expression), (∀ b∈F,b∈E) →
      |(F.map (fun b => (∫ x in S,(cylinderInputBranchCoefficient b x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t) x (b.label•x)).re)-
        (∫ x in S,(matrix (regular b x) 1 1*
          windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re))).sum|≤
      expressionBound F*((1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L)) := by
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
  ring

#print axioms integralMatrixHeight_le_of_entry_bound
#print axioms concrete_expression_window_regular_error
end QuantitativeMaass
