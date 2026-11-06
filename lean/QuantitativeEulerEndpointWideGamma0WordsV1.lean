module

public import QuantitativeEulerEndpointGamma0WordsV1
public import QuantitativeEulerEndpointWideControlAlgebraV1


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix CongruenceSubgroup QuantitativeArithmetic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open scoped Classical MatrixGroups

/-- Every fixed element of the actual Gamma0 subgroup has the original-row
estimate after every fixed projective right label. Closure induction only
combines the proved generator estimates; no scalar-law premise is used. -/
theorem wide_gamma0_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈Gamma0 N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P γ g B K := by
  have hc : γ∈Subgroup.closure (observedGenerators N : Set SL(2,ℤ)) := by
    rwa [observedGenerators_closure]
  have hall : ∀ g : G, ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P γ g B K := by
    apply Subgroup.closure_induction (p := fun γ _ =>
      ∀ g : G, ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P γ g B K) ?_ ?_ ?_ ?_ hc
    · intro a ha g
      exact wide_observed_generator_original_control P a ha g
    · intro g
      exact ⟨1,le_refl _,0,le_refl _,wide_original_control_one P g⟩
    · intro a b _ha _hb ia ib g
      obtain ⟨B₁,hB₁,K₁,hK₁,h₁⟩ := ia (integralLabel b*g)
      obtain ⟨B₂,_hB₂,K₂,hK₂,h₂⟩ := ib g
      refine ⟨max B₁ B₂,hB₁.trans (le_max_left _ _),2*(K₁+K₂),
        mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂),?_⟩
      exact wide_original_control_mul a b g
        (wide_original_control_mono h₁ (le_max_left _ _) (le_refl _))
        (wide_original_control_mono h₂ (le_max_right _ _) (le_refl _))
    · intro a _ha ia g
      obtain ⟨B,hB,K,hK,hh⟩ := ia (integralLabel a⁻¹*g)
      exact ⟨B,hB,K,hK,wide_original_control_inverse a g hh⟩
  exact hall g

theorem wide_gamma0_finite_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ι : Type*} [Fintype ι] (γ : ι → SL(2,ℤ)) (hγ : ∀ i, γ i∈Gamma0 N) (g : ι → G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∀ i, WideOriginalControl P (γ i) (g i) B K := by
  have h (i : ι) : ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideOriginalControl P (γ i) (g i) B K :=
    wide_gamma0_original_control P (γ i) (hγ i) (g i)
  exact wide_finite_original_control P γ g h

#print axioms wide_gamma0_original_control
#print axioms wide_gamma0_finite_original_control
end QuantitativeEulerEndpointPrepared
