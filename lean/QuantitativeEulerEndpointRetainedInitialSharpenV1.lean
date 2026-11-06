module

public import QuantitativeEulerEndpointInitialSharpenV1
public import QuantitativeEulerEndpointRetainedSharpeningV1
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

include ha in
/-- One actual initialized source has all detector budgets, arbitrarily
small trace defect, exact fixed solutions, and inherited fresh-prime support.
The displayed degree and coefficient bounds concern the outer sharpening;
the inner power degree is explicitly 2*effort(C,a). -/
theorem exists_sharpened_initial_scalar (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) {J : ℕ} (hJ : 0<J) :
    ∃ z : ℝ[X], z.natDegree≤16*J^5+1 ∧
      (∑ i∈z.support, |z.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      ScalarSharpening z ∧
      0≤aeval F₀ z ∧ aeval F₀ z≤F₀ ∧
      τ (aeval F₀ z-(aeval F₀ z)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, (∀ i x, B i x*ρ E x=0) → aeval F₀ z*E=E) ∧
      (∀ i x, 4*‖B i x*ρ (aeval F₀ z) x*star (B i x)‖≤a i) ∧
      (∀ S : Subgroup G,
        (∀ x, Supported S (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)) →
        (∀ i x, Supported S (B i x)) → ∀ x, Supported S (ρ (aeval F₀ z) x)) := by
  have ho := filter_order hact s hs p hp B hmB hcB C hC a ha m
  obtain ⟨z,hdeg,hmass,hscalar,hz0,hz1,hdef⟩ :=
    exists_controlled_operator_sharpening_scalar τ hτ F₀ ho.1 ho.2 hJ
  refine ⟨z,hdeg,hmass,hscalar,hz0,hz1,hdef,?_,?_,?_⟩
  · intro E hBE
    exact polynomial_preserves_fixed F₀ E
      (filter_fixed hact s hs p hp B hmB hcB C hC a E hBE m) z hscalar.2.1
  · intro i x
    have hF0x : 0≤ρ (aeval F₀ z) x :=
      (pointwise_le_iff hact s hs p hp 0 (aeval F₀ z)).mpr hz0 x
    have hFx : ρ (aeval F₀ z) x≤ρ F₀ x :=
      (pointwise_le_iff hact s hs p hp (aeval F₀ z) F₀).mpr hz1 x
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (star_right_conjugate_le_conjugate hFx (B i x))
      (star_right_conjugate_nonneg hF0x (B i x))
    exact (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤4)).trans
      (filter_detector_budget hact s hs p hp B hmB hcB C hC a ha m
        (QuantitativeEulerEndpointInitialWeighted.effort_budget C a) i x)
  · intro S hP hB
    apply QuantitativeEulerEndpointSupportAlgebra.polynomial_supported hact s hs p hp S hP F₀
    exact QuantitativeEulerEndpointSupportAlgebra.actual_initial_supported
      hact s hs p hp S hP B hmB hcB C hC hB a m

#print axioms exists_sharpened_initial_scalar
end QuantitativeEulerEndpointInitialActual
