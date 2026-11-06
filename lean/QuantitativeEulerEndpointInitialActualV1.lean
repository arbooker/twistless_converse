module

public import QuantitativeEulerEndpointInitialWeightedV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialActual
open ContinuousLinearMap QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointSubcornerSourceGram QuantitativeEulerEndpointCornerCut
open QuantitativeEulerEndpointInitialPower QuantitativeEulerEndpointInitialSandwich
open AsymptoticRegularTrace MeasureTheory
open scoped lp

variable {G α ι : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h)) (hcB : ∀ i, Covariant (B i))
  (C : ι → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "P" => QuantitativeSpectralRegularAlgebra.representation G α hact s hs p

def residual (i : ι) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := B i x*P x

include hmB in
theorem residual_measurable (i : ι) :
    ∀ g h, Measurable (fun x => matrix (residual hact s hs p B i x) g h) :=
  matrix_comp_measurable _ _ (hmB i)
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs p)

include hcB in
theorem residual_covariant (i : ι) : Covariant (residual hact s hs p B i) :=
  covariant_comp _ _ (hcB i)
    (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs p)

include hp hC in
theorem residual_norm (i : ι) (x : α) : ‖residual hact s hs p B i x‖≤C i := by
  have hP := QuantitativeEulerEndpointBlockGram.projection_family hact s hs p hp x
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hP.nonneg).mpr hP.le_one
  exact (norm_mul_le_of_le (hC i x) hn).trans_eq (mul_one _)

include hp in
theorem residual_source (i : ι) (x : α) :
    residual hact s hs p B i x*P x=residual hact s hs p B i x := by
  rw [residual,mul_assoc,
    (QuantitativeEulerEndpointBlockGram.projection_family hact s hs p hp x).isIdempotentElem.eq]

local notation "R" => residual hact s hs p B
local notation "hmR" => residual_measurable hact s hs p B hmB
local notation "hcR" => residual_covariant hact s hs p B hcB
local notation "hnR" => residual_norm hact s hs p hp B C hC
local notation "hsR" => residual_source hact s hs p hp B

def gram (i : ι) : 𝔄 := gramElement hact s hs p hp (R i) (hmR i) (hcR i) (C i) (hnR i) (hsR i)
local notation "D" => gram hact s hs p hp B hmB hcB C hC

theorem gram_nonneg (i : ι) : 0≤D i :=
  gramElement_nonneg hact s hs p hp (R i) (hmR i) (hcR i) (C i) (hnR i) (hsR i)

theorem gram_norm (i : ι) : ‖D i‖≤(C i)^2 :=
  gramElement_norm_le hact s hs p hp (R i) (hmR i) (hcR i) (C i) (hnR i) (hsR i)

theorem gram_kills (E : 𝔄) (hBE : ∀ i x, B i x*ρ E x=0) (i : ι) : D i*E=0 := by
  apply representation_injective hact s hs p hp
  funext x
  have hPE : P x*ρ E x=ρ E x := congrArg (fun A : 𝔄 => ρ A x) (one_mul E)
  change (star (B i x*P x)*(B i x*P x))*ρ E x=0
  rw [mul_assoc,mul_assoc,hPE,hBE,mul_zero]

variable [Fintype ι]
variable (a : ι → ℝ) (ha : ∀ i, 0<a i)
local notation "hD" => gram_nonneg hact s hs p hp B hmB hcB C hC
local notation "hDn" => gram_norm hact s hs p hp B hmB hcB C hC
local notation "G₀" => QuantitativeEulerEndpointInitialWeighted.energy D C a
local notation "M" => QuantitativeEulerEndpointInitialWeighted.cap C a

def filter (m : ℕ) : 𝔄 := QuantitativeEulerEndpointInitialWeighted.initial D C a m

include ha in
theorem filter_order (m : ℕ) : 0≤filter hact s hs p hp B hmB hcB C hC a m ∧
    filter hact s hs p hp B hmB hcB C hC a m≤1 :=
  QuantitativeEulerEndpointInitialWeighted.initial_order D hD C a hDn ha m

theorem filter_fixed (E : 𝔄) (hBE : ∀ i x, B i x*ρ E x=0) (m : ℕ) :
    filter hact s hs p hp B hmB hcB C hC a m*E=E :=
  QuantitativeEulerEndpointInitialWeighted.initial_fixed D C a E
    (gram_kills hact s hs p hp B hmB hcB C hC E hBE) m

include ha in
/-- Simultaneous bounds for the ORIGINAL external detectors, with no
right-support premise on those detectors. -/
theorem filter_detector_bound (m : ℕ) (i : ι) (x : α) :
    ‖B i x*ρ (filter hact s hs p hp B hmB hcB C hC a m) x*star (B i x)‖≤
      (M*a i)/(((2*m:ℕ):ℝ)+1) := by
  let X := powerFilter G₀ m
  have horder := QuantitativeEulerEndpointInitialWeighted.energy_order D hD C a hDn ha
  have hX := IsSelfAdjoint.of_nonneg (powerFilter_order G₀ horder.1 horder.2 m).1
  have he : filter hact s hs p hp B hmB hcB C hC a m=X^2 := by
    dsimp only [filter,QuantitativeEulerEndpointInitialWeighted.initial,X,powerFilter]
    rw [← pow_mul]
    congr 1
    omega
  rw [he]
  have hPF : P x*ρ (X^2) x=ρ (X^2) x := congrArg (fun A : 𝔄 => ρ A x) (one_mul (X^2))
  have hFP : ρ (X^2) x*P x=ρ (X^2) x := congrArg (fun A : 𝔄 => ρ A x) (mul_one (X^2))
  have hP := (QuantitativeEulerEndpointBlockGram.projection_family hact s hs p hp x).isSelfAdjoint.star_eq
  have hrestrict : (R i x)*ρ (X^2) x*star (R i x)=B i x*ρ (X^2) x*star (B i x) := by
    change (B i x*P x)*ρ (X^2) x*star (B i x*P x)=_
    rw [star_mul,hP,mul_assoc (B i x) (P x) (ρ (X^2) x),hPF,
      ← mul_assoc (B i x*ρ (X^2) x) (P x) (star (B i x)),mul_assoc (B i x) (ρ (X^2) x) (P x),hFP]
  rw [← hrestrict]
  exact (actual_detector_norm_le hact s hs p hp (R i) (hmR i) (hcR i)
    (C i) (hnR i) (hsR i) X hX x).trans
    (QuantitativeEulerEndpointInitialWeighted.component_sandwich_norm D hD C a hDn ha m i)

include ha in
theorem filter_detector_budget (m : ℕ) (hm : 4*M≤((2*m:ℕ):ℝ)+1) (i : ι) (x : α) :
    4*‖B i x*ρ (filter hact s hs p hp B hmB hcB C hC a m) x*star (B i x)‖≤a i := by
  have hbound := filter_detector_bound hact s hs p hp B hmB hcB C hC a ha m i x
  have hden : (0:ℝ)<((2*m:ℕ):ℝ)+1 := by positivity
  have hbudget : 4*((M*a i)/(((2*m:ℕ):ℝ)+1))≤a i := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hm (ha i).le]
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num)).trans hbudget

#print axioms gram_kills
#print axioms filter_order
#print axioms filter_fixed
#print axioms filter_detector_bound
#print axioms filter_detector_budget
end QuantitativeEulerEndpointInitialActual
