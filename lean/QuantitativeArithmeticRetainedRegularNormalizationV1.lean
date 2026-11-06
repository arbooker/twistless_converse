module

public import QuantitativeArithmeticRetainedCylinderNormalizationV1
public import QuantitativeArithmeticRetainedRegularExtensionV1
public import AsymptoticRegularInclusionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedRegularNormalization
open UpperHalfPlane ContinuousLinearMap QuantitativeHolomorphic
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedRegularOperators
open QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedCylinderNormalization (bound bound_one_le gramLower gramLower_pos gramLower_le_one)
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime)

/-- The same extra capped weight as in the physical cylinder realization. -/
def reconstruction (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :=
  (AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp (extension A hS hN P χ β ht z)

theorem reconstruction_terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1)
    (g : TerminalSpace A P z) :
    highProjection A P z (reconstruction A hS hN P χ β ht z g)=(g:Space) := by
  change AsymptoticOrbitDiagonal.corner (highStrip P.ε) z
    (AsymptoticRegularInclusion.inclusion P.epsilon_pos z (extension A hS hN P χ β ht z g))=_
  rw [AsymptoticRegularInclusion.corner_inclusion P.epsilon_pos (highStrip P.ε) (fun _ hz => hz.2)]
  exact extension_terminal A hS hN P χ β ht z hK g

theorem reconstruction_norm_ge (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1)
    (g : TerminalSpace A P z) : ‖g‖≤‖reconstruction A hS hN P χ β ht z g‖ := by
  calc
    ‖g‖=‖highProjection A P z (reconstruction A hS hN P χ β ht z g)‖ := by
      rw [reconstruction_terminal A hS hN P χ β ht z hK g]
      rfl
    _ ≤ ‖reconstruction A hS hN P χ β ht z g‖ := by
      simpa only [one_mul] using (highProjection A P z).le_of_opNorm_le
        (AsymptoticOrbitRegion.corner_norm_le (G:=AsymptoticRationalGroup.Group) (highStrip P.ε) z) _

def scaled (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :=
  (bound A P)⁻¹ • reconstruction A hS hN P χ β ht z

theorem scaled_bounds (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1/2) :
    ‖scaled A hS hN P χ β ht z‖≤1 ∧ ∀v,
      gramLower A P*‖v‖^2≤‖scaled A hS hN P χ β ht z v‖^2 := by
  apply scaled_reconstruction_bounds _ (zero_lt_one.trans_le (bound_one_le A P))
  · apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z)
      (extension_norm_le A hS hN P χ β hχ hβ ht z hK)
      (norm_nonneg (extension A hS hN P χ β ht z)) zero_le_one).trans_eq (one_mul _)
  · exact reconstruction_norm_ge A hS hN P χ β ht z (hK.trans (by norm_num))

def normalized (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :=
  normalizedReconstruction (scaled A hS hN P χ β ht z)

theorem normalized_norm (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1/2)
    (v : TerminalSpace A P z) :
    ‖normalized A hS hN P χ β ht z v‖=‖v‖ :=
  normalizedReconstruction_norm _ (gramLower_pos A P)
    (scaled_bounds A hS hN P χ β hχ hβ ht z hK).2 v

theorem polynomial_error (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1/2) (n : ℕ) :
    ‖polynomialNormalizedReconstruction (scaled A hS hN P χ β ht z) n-
      normalized A hS hN P χ β ht z‖≤
      (1-gramLower A P)^(2^n)/Real.sqrt (gramLower A P) :=
  polynomialNormalizedReconstruction_error _ (gramLower_pos A P) (gramLower_le_one A P)
    (scaled_bounds A hS hN P χ β hχ hβ ht z hK).2
    (scaled_bounds A hS hN P χ β hχ hβ ht z hK).1 n

#print axioms reconstruction_terminal
#print axioms reconstruction_norm_ge
#print axioms scaled_bounds
#print axioms normalized_norm
#print axioms polynomial_error
end QuantitativeArithmeticRetainedRegularNormalization
