module

public import QuantitativeArithmeticRetainedFiniteTailV1
public import QuantitativeArithmeticRetainedFiniteMassV1
public import AsymptoticFiniteNeumannPerturbationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteExpressions
open UpperHalfPlane ContinuousLinearMap AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators (lowConstant terminalConstant)

/-- Effective two-cutoff error; valid without commuting operators. -/
theorem neumann_error_rate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (K K' B B' : E →L[ℂ] E) {C a b : ℝ}
    (hK : ‖K‖≤1/2) (hK' : ‖K'‖≤1/2) (hB : ‖B‖≤C)
    (hk : ‖K-K'‖≤a) (hb : ‖B-B'‖≤b) (n : ℕ) :
    ‖AsymptoticReconstruction.finiteLow K' B' n-AsymptoticReconstruction.low K B‖≤
      (n:ℝ)*b+(n:ℝ)^2*a*C+2*C*(1/2:ℝ)^n := by
  have ha : 0≤a := (norm_nonneg _).trans hk
  have hdiff := AsymptoticReconstruction.finiteLow_difference_norm_le K' K B' B
    (hK'.trans (by norm_num)) (hK.trans (by norm_num)) n
  have hk' : ‖K'-K‖≤a := by simpa only [norm_sub_rev] using hk
  have hb' : ‖B'-B‖≤b := by simpa only [norm_sub_rev] using hb
  have hfinite : ‖AsymptoticReconstruction.finiteLow K' B' n-
      AsymptoticReconstruction.finiteLow K B n‖≤(n:ℝ)*b+(n:ℝ)^2*a*C := by
    apply hdiff.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg _))
      (mul_le_mul (mul_le_mul_of_nonneg_left hk' (sq_nonneg _)) hB
        (norm_nonneg _) (mul_nonneg (sq_nonneg _) ha))
  have htail := AsymptoticReconstruction.finiteLow_error K B hK (by norm_num) hB n
  have he : C*(1/2:ℝ)^n/(1-1/2)=2*C*(1/2:ℝ)^n := by ring
  rw [he] at htail
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfinite htail)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime)

/-- A shared explicit error schedule for both realizations. -/
def neumannError (P : Parameters A) (t n J : ℕ) : ℝ :=
  ((n:ℝ)*terminalTailConstant A P+(n:ℝ)^2*(P.ρ^(t-1)*lowTailConstant A)*
    (1+terminalConstant A P))/(J:ℝ)+2*(1+terminalConstant A P)*(1/2:ℝ)^n

theorem holomorphic_neumann_rate (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (hc : P.ρ^(t-1)*lowConstant A P≤1/2)
    (n J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖AsymptoticReconstruction.finiteLow
      (holomorphicSum (lowExpression A hS hN P χ β t (symmetricFolds J)) m)
      (1+holomorphicSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) m) n-
      AsymptoticReconstruction.low
        (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m)
        (1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m)‖≤neumannError A P t n J := by
  have ht1 : 1≤t := by omega
  have hb : ‖(1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m)-
      (1+holomorphicSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) m)‖≤
      terminalTailConstant A P/(J:ℝ) := by
    simpa only [add_sub_add_left_eq_sub] using terminal_holomorphic_error A hS hN P χ β hχ ht J hJ m
  have hh := neumann_error_rate
    (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m)
    (holomorphicSum (lowExpression A hS hN P χ β t (symmetricFolds J)) m)
    (1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m)
    (1+holomorphicSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) m)
    ((QuantitativeArithmeticRetainedCertificateOperators.low_norm_le A hS hN P χ β hχ hβ ht1 m).trans hc)
    ((low_holomorphic_norm_le A hS hN P χ β hχ hβ ht1 _ m).trans hc)
    ((norm_add_le _ _).trans (add_le_add norm_id_le
      (QuantitativeArithmeticRetainedCertificateOperators.terminal_norm_le A hS hN P χ β hχ hβ ht m)))
    (low_holomorphic_error A hS hN P χ β hχ ht1 J hJ m) hb n
  convert hh using 1
  dsimp only [neumannError]
  ring

theorem regular_neumann_rate (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (hc : P.ρ^(t-1)*lowConstant A P≤1/2)
    (n J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖AsymptoticReconstruction.finiteLow
      (regularSum (lowExpression A hS hN P χ β t (symmetricFolds J)) z)
      (1+regularSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) z) n-
      AsymptoticReconstruction.low
        (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z)
        (1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z)‖≤neumannError A P t n J := by
  have ht1 : 1≤t := by omega
  have hb : ‖(1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z)-
      (1+regularSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) z)‖≤
      terminalTailConstant A P/(J:ℝ) := by
    simpa only [add_sub_add_left_eq_sub] using terminal_regular_error A hS hN P χ β hχ ht J hJ z
  have hh := neumann_error_rate
    (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z)
    (regularSum (lowExpression A hS hN P χ β t (symmetricFolds J)) z)
    (1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z)
    (1+regularSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) z)
    ((QuantitativeArithmeticRetainedRegularOperators.low_norm_le A hS hN P χ β hχ hβ ht1 z).trans hc)
    ((low_regular_norm_le A hS hN P χ β hχ hβ ht1 _ z).trans hc)
    ((norm_add_le _ _).trans (add_le_add norm_id_le
      (QuantitativeArithmeticRetainedRegularOperators.terminal_norm_le A hS hN P χ β hχ hβ ht z)))
    (low_regular_error A hS hN P χ β hχ ht1 J hJ z) hb n
  convert hh using 1
  dsimp only [neumannError]
  ring

#print axioms neumann_error_rate
#print axioms holomorphic_neumann_rate
#print axioms regular_neumann_rate
end QuantitativeArithmeticRetainedFiniteExpressions
