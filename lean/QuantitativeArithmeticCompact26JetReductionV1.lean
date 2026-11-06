module
public import SmallLevelTwentySixGermDAGSourceDefinitionV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section

/-! Reuse the zeroth-order source system at every Taylor order.

For a word or Taylor row, the differentiated term is its derivative rate to
the required power times (the anchor minus the base row). Other row types
have no differentiated term. Thus higher-order rows require only the base
rows, coordinate relabeling, rational rescaling, and finite arithmetic.
-/

namespace QuantitativeArithmeticCompact26JetReduction
open SmallLevelTwentySixGermSources

def anchor (v : Fin 780 → ℂ) : GridSource → ℂ
  | .word i => v (gridGroupIndex i)
  | .taylor i => gridSample (gridTaylorQ i) (gridTaylorT i) v
  | _ => 0

def derivativeRate : GridSource → ℚ
  | .word i => gridGroupDerivative i
  | .taylor i => taylorDerivative i
  | _ => 0

def tail (X Y Z W η σ₂ σ₁₃ a b : ℂ) (v : Fin 780 → ℂ) : GridSource → ℂ
  | .word i => anchor v (.word i) - laurentRows X Y Z W η σ₂ σ₁₃ a b v (.word i)
  | .taylor i => anchor v (.taylor i) - laurentRows X Y Z W η σ₂ σ₁₃ a b v (.taylor i)
  | _ => 0

theorem slope_eq_rate_mul_tail (n : ℕ) (X Y Z W η σ₂ σ₁₃ a b : ℂ)
    (v : Fin 780 → ℂ) (i : GridSource) :
    laurentSlopeRows n X Y Z W η σ₂ σ₁₃ v i =
      (derivativeRate i : ℂ)^n * tail X Y Z W η σ₂ σ₁₃ a b v i := by
  cases i <;> simp only [laurentSlopeRows, derivativeRate, tail, anchor,
    laurentRows, mul_zero] <;> ring

/-- This identity is uniform in the Taylor order and the source type. It
reduces all higher-order complex identities to the zeroth-order system. -/
theorem jet_eq_base_sub_tails (n : ℕ) (X Y Z W η σ₂ σ₁₃ a b : ℂ)
    (v : ℕ → Fin 780 → ℂ) (i : GridSource) :
    laurentJetRow n X Y Z W η σ₂ σ₁₃ a b v i =
      laurentRows (X/2^n) (Y/3^n) (Z/13^n) (W/5^n) η σ₂ σ₁₃ a b (v n) i -
      ∑ h ∈ Finset.range n,
        (derivativeRate i : ℂ)^(n-h) *
          tail (X/2^n) (Y/3^n) (Z/13^n) (W/5^n) η σ₂ σ₁₃ a b (v h) i /
            ((n-h).factorial : ℂ) := by
  unfold laurentJetRow
  simp_rw [slope_eq_rate_mul_tail (a := a) (b := b)]

/-- The two distinguished coordinates occupy the first six slots across the
three layers; all other base coordinates translate by 318 per layer. -/
def layerIndex (n j : ℕ) : ℕ :=
  if j < 2 then 2*n+j else 318*n+j

theorem sourceCoordinate_eq_layerIndex (n : ℕ) (j : Fin 780) :
    SmallLevelTwentySixGermDAG.sourceCoordinate n j =
      layerIndex n (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j) := by
  unfold SmallLevelTwentySixGermDAG.sourceCoordinate layerIndex
  split_ifs <;> omega

#print axioms slope_eq_rate_mul_tail
#print axioms jet_eq_base_sub_tails
#print axioms sourceCoordinate_eq_layerIndex
end QuantitativeArithmeticCompact26JetReduction
