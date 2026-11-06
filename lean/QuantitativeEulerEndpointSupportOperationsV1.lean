module

public import QuantitativeEulerEndpointSupportAlgebraV1
public import QuantitativeEulerEndpointInitialActualV1
public import QuantitativeEulerEndpointSoftUpdateV1
public import QuantitativeEulerEndpointNormalizedRowsV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSupportAlgebra
open QuantitativeEulerEndpointSubcorner AsymptoticSubgroupSupport
open QuantitativeEulerEndpointSubcornerSourceGram QuantitativeEulerEndpointInitialPower
open MeasureTheory Polynomial
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (S : Subgroup G)
  (hP : ∀ x, Supported S (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x))
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

include hP in
/-- The entire actual update followed by any real sharpening polynomial
retains every subgroup support shared by the incoming source and block Gram. -/
theorem update_polynomial_supported (A F : 𝔄)
    (hA : ∀ x, Supported S (ρ A x)) (hF : ∀ x, Supported S (ρ F x))
    (L : ℕ) (z : ℝ[X]) :
    ∀ x, Supported S (ρ (aeval (QuantitativeEulerEndpointSoftUpdate.update A (A*F*A) L) z) x) := by
  let T : Subalgebra ℝ 𝔄 := (algebra hact s hs p hp S hP).toSubalgebra.restrictScalars ℝ
  have ha : A∈T := hA
  have hf : F∈T := hF
  have hc := T.mul_mem (T.mul_mem ha hf) ha
  have hu : QuantitativeEulerEndpointSoftUpdate.update A (A*F*A) L∈T :=
    T.sub_mem ha (T.mul_mem (T.mul_mem ha (T.sub_mem T.one_mem
      (T.pow_mem (T.sub_mem T.one_mem hc) L))) ha)
  exact polynomial_supported hact s hs p hp S hP _ hu z

include hP in
theorem weighted_initial_supported {ι : Type*} [Fintype ι] (D : ι → 𝔄)
    (hD : ∀ i x, Supported S (ρ (D i) x)) (C a : ι → ℝ) (m : ℕ) :
    ∀ x, Supported S (ρ (QuantitativeEulerEndpointInitialWeighted.initial D C a m) x) := by
  let T : Subalgebra ℝ 𝔄 := (algebra hact s hs p hp S hP).toSubalgebra.restrictScalars ℝ
  have hg : QuantitativeEulerEndpointInitialWeighted.energy D C a∈T := by
    apply T.smul_mem
    apply T.sum_mem
    intro i _
    exact T.smul_mem (hD i) _
  simpa only [QuantitativeEulerEndpointInitialWeighted.initial,powerFilter_aeval] using
    polynomial_supported hact s hs p hp S hP _ hg (powerPolynomial (2*m))

variable {ι : Type*} (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => AsymptoticRegularTrace.matrix (B i x) g h))
  (hcB : ∀ i, AsymptoticRegularTrace.Covariant (B i)) (C : ι → ℝ)
  (hC : ∀ i x, ‖B i x‖≤C i) (hB : ∀ i x, Supported S (B i x))

include hP hB in
theorem initial_gram_supported (i : ι) (x : α) :
    Supported S (ρ (QuantitativeEulerEndpointInitialActual.gram hact s hs p hp B hmB hcB C hC i) x) := by
  have hr := supported_comp S _ _ (hB i x) (hP x)
  exact supported_comp S _ _ (supported_adjoint S _ hr) hr

include hP hB in
theorem actual_initial_supported [Fintype ι] (a : ι → ℝ) (m : ℕ) :
    ∀ x, Supported S (ρ (QuantitativeEulerEndpointInitialActual.filter hact s hs p hp B hmB hcB C hC a m) x) :=
  weighted_initial_supported hact s hs p hp S hP _
    (initial_gram_supported hact s hs p hp S hP B hmB hcB C hC hB) C a m

include hP in
theorem normalized_rows_supported
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℕ → ℝ)
    (hB : ∀ i x, Supported S (B i x)) (n i : ℕ) (x : α) :
    Supported S (QuantitativeEulerEndpointNormalizedRows.row hact s hs p B C n i x) :=
  supported_smul S _ (supported_comp S _ _ (hB i x) (hP x)) _

include hP in
theorem block_gram_supported
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmB : ∀ i g h, Measurable (fun x => AsymptoticRegularTrace.matrix (B i x) g h))
    (hcB : ∀ i, AsymptoticRegularTrace.Covariant (B i)) (C : ℕ → ℝ)
    (hC : ∀ i x, ‖B i x‖≤C i)
    (hsource : ∀ i x, B i x*QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x=B i x)
    (hB : ∀ i x, Supported S (B i x)) (n : ℕ) :
    ∀ x, Supported S (ρ (QuantitativeEulerEndpointBlockGram.gramSum hact s hs p hp B hmB hcB C hC hsource n) x) := by
  let T : Subalgebra ℝ 𝔄 := (algebra hact s hs p hp S hP).toSubalgebra.restrictScalars ℝ
  change QuantitativeEulerEndpointBlockGram.gramSum hact s hs p hp B hmB hcB C hC hsource n∈T
  apply T.sum_mem
  intro i _ x
  exact supported_comp S _ _ (supported_adjoint S _ (hB i x)) (hB i x)

#print axioms update_polynomial_supported
#print axioms weighted_initial_supported
#print axioms initial_gram_supported
#print axioms actual_initial_supported
#print axioms normalized_rows_supported
#print axioms block_gram_supported
end QuantitativeEulerEndpointSupportAlgebra
