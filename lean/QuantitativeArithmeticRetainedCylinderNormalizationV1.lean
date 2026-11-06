module

public import QuantitativeArithmeticRetainedCylinderExtensionV1
public import QuantitativeHolomorphicGramV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedCylinderNormalization
open ContinuousLinearMap QuantitativeHolomorphic
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
open QuantitativeArithmeticRetainedCylinderExtension

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

def bound (P : Parameters A) : ℝ := 2*(1+terminalConstant A P)

theorem bound_one_le (P : Parameters A) : 1≤bound A P := by
  have hT : 0≤terminalConstant A P := by
    unfold terminalConstant
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _)
    cases i with
    | inl i => dsimp only [rowTerminalCost,primitiveTerminalCost]; positivity
    | inr i => dsimp only [rowTerminalCost]; positivity
  dsimp only [bound]
  linarith

def gramLower (P : Parameters A) : ℝ := (bound A P)⁻¹^2

theorem gramLower_pos (P : Parameters A) : 0<gramLower A P :=
  sq_pos_of_pos (inv_pos.mpr (zero_lt_one.trans_le (bound_one_le A P)))

theorem gramLower_le_one (P : Parameters A) : gramLower A P≤1 := by
  have hB := bound_one_le A P
  simpa only [one_pow,gramLower] using pow_le_pow_left₀
    (inv_nonneg.mpr (zero_le_one.trans hB)) (inv_le_one_of_one_le₀ hB) 2

variable (hS : ∀p∈S,p.Prime)

def reconstruction (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :=
  (AsymptoticCylinder.inclusion P.epsilon_pos).comp (extension A hS hN P χ β ht m)

def scaled (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :=
  (bound A P)⁻¹ • reconstruction A hS hN P χ β ht m

theorem scaled_bounds (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1/2) :
    ‖scaled A hS hN P χ β ht m‖≤1 ∧ ∀v,
      gramLower A P*‖v‖^2≤‖scaled A hS hN P χ β ht m v‖^2 := by
  apply scaled_reconstruction_bounds _ (zero_lt_one.trans_le (bound_one_le A P))
  · apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul (AsymptoticCylinder.inclusion_norm_le P.epsilon_pos)
      (extension_norm_le A hS hN P χ β hχ hβ ht m hK)
      (norm_nonneg (extension A hS hN P χ β ht m)) zero_le_one).trans_eq (one_mul _)
  · exact extension_inclusion_norm_ge A hS hN P χ β ht m (hK.trans (by norm_num))

def normalized (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :=
  normalizedReconstruction (scaled A hS hN P χ β ht m)

theorem normalized_norm (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1/2)
    (v : AsymptoticCylinderTerminal.Space P.ε) :
    ‖normalized A hS hN P χ β ht m v‖=‖v‖ :=
  normalizedReconstruction_norm _ (gramLower_pos A P)
    (scaled_bounds A hS hN P χ β hχ hβ ht m hK).2 v

theorem polynomial_error (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1/2) (n : ℕ) :
    ‖polynomialNormalizedReconstruction (scaled A hS hN P χ β ht m) n-
      normalized A hS hN P χ β ht m‖≤
      (1-gramLower A P)^(2^n)/Real.sqrt (gramLower A P) :=
  polynomialNormalizedReconstruction_error _ (gramLower_pos A P) (gramLower_le_one A P)
    (scaled_bounds A hS hN P χ β hχ hβ ht m hK).2
    (scaled_bounds A hS hN P χ β hχ hβ ht m hK).1 n

#print axioms scaled_bounds
#print axioms normalized_norm
#print axioms polynomial_error
end QuantitativeArithmeticRetainedCylinderNormalization
