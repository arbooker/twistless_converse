module

public import QuantitativeEulerEndpointReplacementGramExpressionV1
public import QuantitativeEulerEndpointPhysicalGramV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticFiniteBranch QuantitativeHolomorphic
open QuantitativeEulerEndpointPhysicalGram
open scoped Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem combined_mass (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression) :
    expressionBound (combinedGramExpression E F a u)=
      (∑ i,(‖a‖*(expressionBound (E i)*expressionBound u))^2)+
      ∑ i,(‖a‖*(expressionBound (F i)*expressionBound u))^2 := by
  simp only [combinedGramExpression,expressionBound_append,gramExpression,
    expressionBound_sumExpressions,expressionBound_compose,expressionBound_adjoint,
    expressionBound_scale,←pow_two]

/-- Row count enters mass, while the common reconstruction is paid only
quadratically in each Gram. The original normalization may be retained. -/
theorem combined_mass_le (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression)
    {B U : ℝ} (ha : ‖a‖≤1) (hE : ∀ i,expressionBound (E i)≤B)
    (hF : ∀ i,expressionBound (F i)≤B) (hB : 0≤B)
    (hu : expressionBound u≤U) :
    expressionBound (combinedGramExpression E F a u)≤
      ((Fintype.card ι:ℝ)+(Fintype.card κ:ℝ))*(B*U)^2 := by
  have hh (e : Expression) (he : expressionBound e≤B) :
      (‖a‖*(expressionBound e*expressionBound u))^2≤(B*U)^2 := by
    have hm := mul_le_mul he hu (expressionBound_nonneg u) hB
    have hn : ‖a‖*(expressionBound e*expressionBound u)≤B*U := by
      calc
        _ ≤ 1*(B*U) := mul_le_mul ha hm
          (mul_nonneg (expressionBound_nonneg _) (expressionBound_nonneg _)) zero_le_one
        _ = _ := one_mul _
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg a)
      (mul_nonneg (expressionBound_nonneg e) (expressionBound_nonneg u))) hn 2
  rw [combined_mass]
  have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh (E i) (hE i))
  have hf := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh (F i) (hF i))
  have h := add_le_add he hf
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,add_mul] using h

theorem scaled_composed_gram_matrix (E : ι → Expression) (a : ℂ) (u : Expression)
    {B U : ℝ} (hB : 0≤B) (hU : 0≤U)
    (hE : ∀ i,ExpressionMatrixBound (E i) B)
    (hu : ExpressionMatrixBound u U) :
    ExpressionMatrixBound (gramExpression (fun i => scaleExpression a (composeExpression (E i) u)))
      (8*B^2*U^2) := by
  apply expressionMatrixBound_sum
  intro i _
  have hd := ((hE i).compose hu hU).scale a
  have hs := hd.adjoint.compose hd (by positivity)
  convert hs using 1
  ring

theorem combined_matrix (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression)
    {B U : ℝ} (hB : 0≤B) (hU : 0≤U)
    (hE : ∀ i,ExpressionMatrixBound (E i) B) (hF : ∀ i,ExpressionMatrixBound (F i) B)
    (hu : ExpressionMatrixBound u U) :
    ExpressionMatrixBound (combinedGramExpression E F a u) (8*B^2*U^2) := by
  exact ((scaled_composed_gram_matrix E a u hB hU hE hu).append
    (scaled_composed_gram_matrix F a u hB hU hF hu)).mono (max_le le_rfl le_rfl)

theorem scaled_gram_sum_support {𝔄 : Type*} [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄]
    (P : 𝔄) (hP : IsStarProjection P) (R : ι → 𝔄) (a : ℂ) (U : 𝔄) (hU : U*P=U) :
    let G := ∑ i,star (a • (R i*U))*(a • (R i*U))
    P*G=G ∧ G*P=G := by
  apply sum_supported P
  intro i
  apply gram_supported P hP
  rw [smul_mul_assoc,mul_assoc,hU]

theorem regular_combined_support (E : ι → Expression) (F : κ → Expression) (a : ℂ)
    (u : Expression) (x : UpperHalfPlane) (P : RegularSpace →L[ℂ] RegularSpace)
    (hP : IsStarProjection P) (hu : regularSum u x*P=regularSum u x) :
    let G := regularSum (combinedGramExpression E F a u) x
    P*G=G ∧ G*P=G := by
  rw [regular_combinedGramExpression]
  have he := scaled_gram_sum_support P hP (fun i => regularSum (E i) x) a (regularSum u x) hu
  have hf := scaled_gram_sum_support P hP (fun i => regularSum (F i) x) a (regularSum u x) hu
  exact ⟨(mul_add _ _ _).trans (congrArg₂ (·+·) he.1 hf.1),
    (add_mul _ _ _).trans (congrArg₂ (·+·) he.2 hf.2)⟩

theorem physical_combined_support (E : ι → Expression) (F : κ → Expression) (a : ℂ)
    (u : Expression) (m : ℕ)
    (P : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hP : IsStarProjection P) (hu : holomorphicSum u m*P=holomorphicSum u m) :
    let G := holomorphicSum (combinedGramExpression E F a u) m
    P*G=G ∧ G*P=G := by
  rw [holomorphic_combinedGramExpression]
  have he := scaled_gram_sum_support P hP (fun i => holomorphicSum (E i) m) a (holomorphicSum u m) hu
  have hf := scaled_gram_sum_support P hP (fun i => holomorphicSum (F i) m) a (holomorphicSum u m) hu
  exact ⟨(mul_add _ _ _).trans (congrArg₂ (·+·) he.1 hf.1),
    (add_mul _ _ _).trans (congrArg₂ (·+·) he.2 hf.2)⟩

#print axioms combined_mass_le
#print axioms combined_matrix
#print axioms regular_combined_support
#print axioms physical_combined_support
end QuantitativeEulerEndpointPrepared
