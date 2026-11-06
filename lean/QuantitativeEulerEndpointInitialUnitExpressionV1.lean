module

public import QuantitativeEulerEndpointDetectorExpressionMassV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane MeasureTheory AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointWeightedExpression
open scoped Classical

variable (N : ℕ) [NeZero N] (sector : Sector N)
  {ι : Type*} [Fintype ι]

variable (regions : ι → Set ℍ) (hs : ∀ i, IsCompact (regions i))
  {ε : ℝ} (hε : 0<ε) (H : ℝ) (t : ι → ℕ)
  (R Y Hobs : ι → ℝ) (hY : ∀ i, 0<Y i)
  (hre : ∀ i z, z∈regions i → |z.re|≤R i)
  (hlo : ∀ i z, z∈regions i → Y i≤z.im)
  (hhi : ∀ i z, z∈regions i → z.im≤Hobs i)
  (a : ι → ℝ) (ha : ∀ i, 0<a i)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "C" => fun i => wideDetectorBound N sector (R i) (Y i) (Hobs i) (t i)
local notation "M" => QuantitativeEulerEndpointInitialWeighted.cap C a
local notation "G₀" => QuantitativeEulerEndpointWideInitializer.energy N sector regions hs hε H t R Y Hobs hY hre hlo hhi a

include ha in
/-- Finite expression for the ACTUAL simultaneous initial energy, with
coefficient mass at most one, explicit matrix height and original physical realization. -/
theorem exists_initial_energy_unit_expression :
    ∃ E : Expression, (∀ x : Base,regularSum E x=ρ G₀ x) ∧
      (∀ m,holomorphicSum E m=holomorphicSum (originalEnergyExpression N sector regions hs hε H t R Y Hobs a) m) ∧
      expressionBound E≤1 ∧
      ExpressionMatrixBound E (8*(rowMatrixHeight N R Y Hobs)^2) := by
  choose E hE using fun i => exists_baseline_expressions (hs i) hε (hY i) (hre i) (hlo i) (hhi i) N sector (t i)
  let e := weightedGram (unitExpression ε H) E (fun i => (a i)⁻¹) M⁻¹
  refine ⟨e,?_,?_,?_,?_⟩
  · exact regular_initial_energy N sector regions hs hε H t R Y Hobs hY hre hlo hhi a E (fun i j => (hE i j).1)
  · intro m
    have hphysical (i j) := (hE i j).2.1 m
    simp only [e,originalEnergyExpression,holomorphic_weightedGram,hphysical]
  · exact normalized_initial_mass_le_one N sector t R Y Hobs a ha
      (unitExpression ε H) (le_of_eq (unit_mass ε H)) E (fun i j => (hE i j).2.2.1)
  · apply weighted_matrix (rowMatrixHeight_nonneg N R Y Hobs) (unit_matrix ε H)
    intro i j
    apply ((hE i j).2.2.2).mono
    have hj : baselineMatrixHeight N (R i) (Y i) (Hobs i) j≤
        ∑ k : NewBaselineIndex N,baselineMatrixHeight N (R i) (Y i) (Hobs i) k :=
      Finset.single_le_sum (f:=fun k : NewBaselineIndex N => baselineMatrixHeight N (R i) (Y i) (Hobs i) k)
        (fun k _ => by unfold baselineMatrixHeight; positivity) (Finset.mem_univ j)
    apply hj.trans
    exact Finset.single_le_sum (f:=fun k : ι => ∑ j : NewBaselineIndex N,baselineMatrixHeight N (R k) (Y k) (Hobs k) j)
      (fun k _ => Finset.sum_nonneg (fun j _ => by unfold baselineMatrixHeight; positivity)) (Finset.mem_univ i)

#print axioms exists_initial_energy_unit_expression
end QuantitativeEulerEndpointInitialExpression
