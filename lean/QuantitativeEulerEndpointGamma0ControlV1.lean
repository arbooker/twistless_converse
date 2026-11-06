module

public import QuantitativeEulerEndpointOriginalControlV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open scoped Classical MatrixGroups

theorem original_control_mono {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} {P : Prepared N excluded threshold}
    {γ : SL(2,ℤ)} {g : G} {B K B' K' : ℝ}
    (h : OriginalControl P γ g B K) (hB : B≤B') (hK : K≤K') :
    OriginalControl P γ g B' K' := by
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := h C (hB.trans hBC) q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  exact (hqbound w hw hs hε hY hre hlo him t x v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
      (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)))

theorem finite_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ι : Type*} [Fintype ι] (γ : ι → SL(2,ℤ)) (g : ι → G)
    (h : ∀ i, ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ OriginalControl P (γ i) (g i) B K) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∀ i, OriginalControl P (γ i) (g i) B K := by
  choose B hB K hK hc using h
  let B₀ := 1+∑ i, B i
  let K₀ := ∑ i, K i
  have hBn (i : ι) : 0≤B i := zero_le_one.trans (hB i)
  have hB₀ : 1≤B₀ := by
    dsimp only [B₀]
    linarith [Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset ι)) => hBn i)]
  have hBB (i : ι) : B i≤B₀ := by
    have hi := Finset.single_le_sum (fun j _ => hBn j) (Finset.mem_univ i)
    dsimp only [B₀]
    linarith
  have hKK (i : ι) : K i≤K₀ :=
    Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  exact ⟨B₀,hB₀,K₀,Finset.sum_nonneg (fun i _ => hK i),
    fun i => original_control_mono (hc i) (hBB i) (hKK i)⟩

theorem observed_generator_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈observedGenerators N) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ OriginalControl P γ g B K := by
  rcases Finset.mem_union.mp hγ with hgen | hobs
  · have hg : γ∈Gamma1 N := by
      rw [←generators_closure]
      exact Subgroup.subset_closure hgen
    exact gamma1_original_control P γ hg g
  · obtain ⟨a,_ha,rfl⟩ := Finset.mem_image.mp hobs
    exact observed_matrix_original_control P a g

/-- One pair of constants controls the actual finite Gamma0 generating
set after any fixed finite family of projective right labels. The generating
set is exactly the one in observedGenerators_closure. -/
theorem observed_generators_common_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (g : ↥(observedGenerators N) → G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ γ : ↥(observedGenerators N), OriginalControl P γ.val (g γ) B K := by
  have h (γ : ↥(observedGenerators N)) :
      ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ OriginalControl P γ.val (g γ) B K :=
    observed_generator_original_control P γ.val γ.property (g γ)
  exact finite_original_control P (ι := ↥(observedGenerators N))
    (fun γ : ↥(observedGenerators N) => γ.val) g h

#print axioms finite_original_control
#print axioms observed_generator_original_control
#print axioms observed_generators_common_control
end QuantitativeEulerEndpointPrepared
