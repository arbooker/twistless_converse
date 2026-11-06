module

public import QuantitativeEulerEndpointWeightedExpressionV1
public import QuantitativeEulerEndpointWideInitializerV1
public import QuantitativeEulerEndpointBaselineRowExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane MeasureTheory AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointWeightedExpression
open scoped Classical

theorem restricted_gram_eq {A κ : Type*} [Ring A] [StarRing A] [Fintype κ]
    (B : κ → A) (D P : A) (h : star D*D=∑ j,star (B j)*B j) :
    (∑ j,star (B j*P)*(B j*P))=star (D*P)*(D*P) := by
  calc
    _ = star P*(∑ j,star (B j)*B j)*P := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [star_mul]
      simp only [mul_assoc]
    _ = _ := by rw [←h,star_mul]; simp only [mul_assoc]

variable (N : ℕ) [NeZero N] (sector : Sector N)
  {ι : Type*} [Fintype ι] (regions : ι → Set ℍ) (hs : ∀ i, IsCompact (regions i))
  {ε : ℝ} (hε : 0<ε) (H : ℝ) (t : ι → ℕ)
  (R Y Hobs : ι → ℝ) (hY : ∀ i, 0<Y i)
  (hre : ∀ i z, z∈regions i → |z.re|≤R i)
  (hlo : ∀ i z, z∈regions i → Y i≤z.im)
  (hhi : ∀ i z, z∈regions i → z.im≤Hobs i)
  (a : ι → ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "C" => fun i => wideDetectorBound N sector (R i) (Y i) (Hobs i) (t i)
local notation "M" => QuantitativeEulerEndpointInitialWeighted.cap C a
local notation "G₀" => QuantitativeEulerEndpointWideInitializer.energy N sector regions hs hε H t R Y Hobs hY hre hlo hhi a
local notation "P" => fun x : Base => regularSum (unitExpression ε H) x

theorem energy_representation (x : Base) :
    ρ G₀ x=M⁻¹ • ∑ i,(a i)⁻¹ •
      (star (newBaselineDetector N sector (hs i) hε (t i) x*P x)*
        (newBaselineDetector N sector (hs i) hε (t i) x*P x)) := by
  simp only [QuantitativeEulerEndpointWideInitializer.energy,
    QuantitativeEulerEndpointInitialWeighted.energy,QuantitativeEulerEndpointInitialWeighted.total,
    map_smul,map_sum,Pi.smul_apply,Finset.sum_apply,QuantitativeEulerEndpointInitialActual.gram,
    QuantitativeEulerEndpointSubcornerSourceGram.representation_gramElement,unit_regular]
  rfl

theorem regular_initial_energy (E : ι → NewBaselineIndex N → Expression)
    (hE : ∀ i j,∀ x : Base,regularSum (E i j) x=newBaselineRows N sector (hs i) hε (t i) x j)
    (x : Base) :
    regularSum (weightedGram (unitExpression ε H) E (fun i => (a i)⁻¹) M⁻¹) x=ρ G₀ x := by
  rw [regular_weightedGram,energy_representation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [hE]
  exact restricted_gram_eq _ _ _ (QuantitativeEulerEndpointBaselineInitializer.detector_gram N sector (hs i) hε (t i) x)

#print axioms restricted_gram_eq
#print axioms energy_representation
#print axioms regular_initial_energy
end QuantitativeEulerEndpointInitialExpression
