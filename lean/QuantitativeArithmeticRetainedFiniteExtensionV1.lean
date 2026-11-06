module

public import QuantitativeArithmeticRetainedFiniteRateV1
public import QuantitativeArithmeticRetainedRegularExtensionV1
public import QuantitativeArithmeticRetainedTerminalExtensionV1
public import AsymptoticFiniteBranchReconstructionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteExpressions
open UpperHalfPlane ContinuousLinearMap AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators (lowConstant terminalConstant)
open AsymptoticCertificateOperators (highStrip highStrip_measurable)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime)

/-- The actual mixed extension approximant, including terminal restriction. -/
def fullExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) : Expression :=
  composeExpression (neumannExpression (lowExpression A hS hN P χ β t I)
    ([identity]++terminalExpression A hS hN P χ β ht I) n)
    [corner (highStrip P.ε) (highStrip_measurable P.ε)]

theorem holomorphic_fullExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    holomorphicSum (fullExpression A hS hN P χ β ht n I) m=
      (AsymptoticReconstruction.finiteLow
        (holomorphicSum (lowExpression A hS hN P χ β t I) m)
        (1+holomorphicSum (terminalExpression A hS hN P χ β ht I) m) n).comp
        (QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P) := by
  rw [fullExpression,holomorphicSum_compose,holomorphicSum_neumann,holomorphicSum_append]
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,holomorphic_identity,holomorphic_corner]
  rfl

theorem regular_fullExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    regularSum (fullExpression A hS hN P χ β ht n I) z=
      (AsymptoticReconstruction.finiteLow
        (regularSum (lowExpression A hS hN P χ β t I) z)
        (1+regularSum (terminalExpression A hS hN P χ β ht I) z) n).comp
        (QuantitativeArithmeticRetainedRegularExtension.highProjection A P z) := by
  rw [fullExpression,regularSum_compose,regularSum_neumann,regularSum_append]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,regular_identity,regular_corner]
  rfl

/-- The full finite reconstruction has a uniform coefficient-mass bound. -/
theorem fullExpression_mass (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (hc : P.ρ^(t-1)*lowConstant A P≤1/2)
    (n : ℕ) (I : Finset ℤ) :
    expressionBound (fullExpression A hS hN P χ β ht n I)≤2*(1+terminalConstant A P) := by
  have hK := (low_mass A hS hN P χ β hχ hβ (by omega : 1≤t) I).trans hc
  have hT := terminal_mass A hS hN P χ β hχ hβ ht I
  have hgeom : (∑ j∈Finset.range n,
      expressionBound (lowExpression A hS hN P χ β t I)^j)≤2 := by
    apply le_trans _ (QuantitativeHolomorphic.half_geometric_sum_le_two n)
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (expressionBound_nonneg _) hK j)
  rw [fullExpression,QuantitativeHolomorphic.expressionBound_compose,
    QuantitativeHolomorphic.expressionBound_neumann,QuantitativeHolomorphic.expressionBound_append]
  have hid : expressionBound [identity]=1 := by simp [expressionBound,identity]
  have hcorner : expressionBound [corner (highStrip P.ε) (highStrip_measurable P.ε)]=1 := by
    simp [expressionBound,corner]
  rw [hid,hcorner,mul_one]
  exact mul_le_mul hgeom (add_le_add le_rfl hT)
    (add_nonneg zero_le_one (expressionBound_nonneg _)) (by norm_num)

/-- Quantified approximation of the original extension on its genuine terminal space. -/
theorem holomorphic_extension_rate (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (hc : P.ρ^(t-1)*lowConstant A P≤1/2)
    (n J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖(holomorphicSum (fullExpression A hS hN P χ β ht n (symmetricFolds J)) m).comp
        (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL-
      QuantitativeArithmeticRetainedTerminalExtension.extension A hS hN P χ β ht m‖≤neumannError A P t n J := by
  have he : (QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P).comp (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL=(QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL := by
    apply ContinuousLinearMap.ext
    intro g
    exact (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property
  have hinc : ‖(QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simp
  rw [holomorphic_fullExpression,ContinuousLinearMap.comp_assoc,he,QuantitativeArithmeticRetainedTerminalExtension.extension]
  change ‖(AsymptoticReconstruction.finiteLow
      (holomorphicSum (lowExpression A hS hN P χ β t (symmetricFolds J)) m)
      (1+holomorphicSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) m) n).comp
      (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL-
    AsymptoticReconstruction.low (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m)
      ((1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m).comp (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL)‖≤_
  have hcomp : AsymptoticReconstruction.low (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m)
      ((1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m).comp (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL)=
    (AsymptoticReconstruction.low (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m)
      (1+QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m)).comp (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL := by
    simp only [AsymptoticReconstruction.low,ContinuousLinearMap.comp_assoc]
  rw [hcomp,← ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hinc (norm_nonneg _)).trans
  rw [mul_one]
  exact holomorphic_neumann_rate A hS hN P χ β hχ hβ ht hc n J hJ m

/-- Quantified approximation of the original extension on its genuine terminal space. -/
theorem regular_extension_rate (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (hc : P.ρ^(t-1)*lowConstant A P≤1/2)
    (n J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖(regularSum (fullExpression A hS hN P χ β ht n (symmetricFolds J)) z).comp
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL-
      QuantitativeArithmeticRetainedRegularExtension.extension A hS hN P χ β ht z‖≤neumannError A P t n J := by
  have he : (QuantitativeArithmeticRetainedRegularExtension.highProjection A P z).comp (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL=(QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL := by
    apply ContinuousLinearMap.ext
    intro g
    exact (AsymptoticOrbitRegion.mem_space _ _ _).mp g.property
  have hinc : ‖(QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simp
  rw [regular_fullExpression,ContinuousLinearMap.comp_assoc,he,QuantitativeArithmeticRetainedRegularExtension.extension]
  change ‖(AsymptoticReconstruction.finiteLow
      (regularSum (lowExpression A hS hN P χ β t (symmetricFolds J)) z)
      (1+regularSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) z) n).comp
      (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL-
    AsymptoticReconstruction.low (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z)
      ((1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z).comp (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL)‖≤_
  have hcomp : AsymptoticReconstruction.low (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z)
      ((1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z).comp (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL)=
    (AsymptoticReconstruction.low (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z)
      (1+QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z)).comp (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL := by
    simp only [AsymptoticReconstruction.low,ContinuousLinearMap.comp_assoc]
  rw [hcomp,← ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hinc (norm_nonneg _)).trans
  rw [mul_one]
  exact regular_neumann_rate A hS hN P χ β hχ hβ ht hc n J hJ z

#print axioms fullExpression_mass
#print axioms holomorphic_extension_rate
#print axioms regular_extension_rate
end QuantitativeArithmeticRetainedFiniteExpressions
