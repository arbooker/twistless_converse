module

public import QuantitativeEulerEndpointInitialCompositionV1
public import QuantitativeEulerEndpointInitialSharpenV1
public import QuantitativeEulerEndpointSupportOperationsV1
public import QuantitativeEulerEndpointSharpenControlledV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialActual
open ContinuousLinearMap QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointBernstein AsymptoticSubgroupSupport
open AsymptoticRegularTrace MeasureTheory Polynomial
open scoped lp

variable {G α ι : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α] [Fintype ι]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h)) (hcB : ∀ i, Covariant (B i))
  (C : ι → ℝ) (hC : ∀ i x, ‖B i x‖≤C i) (a : ι → ℝ) (ha : ∀ i, 0<a i)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "m" => QuantitativeEulerEndpointInitialWeighted.effort C a
local notation "F₀" => filter hact s hs p hp B hmB hcB C hC a m

local notation "D" => gram hact s hs p hp B hmB hcB C hC
local notation "G₀" => QuantitativeEulerEndpointInitialWeighted.energy D C a

include ha in
/-- A single composed polynomial initializes the actual source. The
bounds include the inner low-pass degree as well as outer sharpening. -/
theorem exists_initial_polynomial (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) {J : ℕ} (hJ : 0<J) :
    ∃ q : ℝ[X], q.natDegree≤(16*J^5+1)*(2*m) ∧
      (∑ i∈q.support, |q.coeff i|)≤
        ((((16*J^5+1)*(2*m):ℕ):ℝ)+1)*((((16*J^5:ℕ):ℝ)+2)*3^(16*J^5))*
          2^((2*m)*(16*J^5+1)) ∧
      0≤aeval G₀ q ∧ aeval G₀ q≤1 ∧
      τ (aeval G₀ q-(aeval G₀ q)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, (∀ i x, B i x*ρ E x=0) → aeval G₀ q*E=E) ∧
      (∀ i x, 4*‖B i x*ρ (aeval G₀ q) x*star (B i x)‖≤a i) ∧
      (∀ S : Subgroup G,
        (∀ x, Supported S (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)) →
        (∀ i x, Supported S (B i x)) → ∀ x, Supported S (ρ (aeval G₀ q) x)) := by
  obtain ⟨z,hdeg,hmass,hz0,hz1,hdef,hfixed,hbudget,hsupport⟩ :=
    exists_sharpened_initial hact s hs p hp B hmB hcB C hC a ha τ hτ hJ
  let q := z.comp (QuantitativeEulerEndpointInitialPower.powerPolynomial (2*m))
  have he : aeval G₀ q=aeval F₀ z := by
    dsimp only [q]
    rw [aeval_comp,← QuantitativeEulerEndpointInitialPower.powerFilter_aeval]
    rfl
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (QuantitativeEulerEndpointInitialPower.composed_degree z (2*m)).trans
      (Nat.mul_le_mul_right _ hdeg)
  · apply (QuantitativeEulerEndpointInitialPower.composed_mass z (2*m)).trans
    have hd : (((z.natDegree*(2*m):ℕ):ℝ)+1)≤((((16*J^5+1)*(2*m):ℕ):ℝ)+1) := by
      exact_mod_cast Nat.succ_le_succ (Nat.mul_le_mul_right (2*m) hdeg)
    have hp : (2:ℝ)^((2*m)*z.natDegree)≤2^((2*m)*(16*J^5+1)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (2*m) hdeg)
    exact mul_le_mul (mul_le_mul hd hmass
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)) hp
      (pow_nonneg (by norm_num) _) (by positivity)
  · rw [he]; exact hz0
  · rw [he]
    exact hz1.trans (filter_order hact s hs p hp B hmB hcB C hC a ha m).2
  · rw [he]; exact hdef
  · rw [he]; exact hfixed
  · rw [he]; exact hbudget
  · rw [he]; exact hsupport

#print axioms exists_initial_polynomial
end QuantitativeEulerEndpointInitialActual
