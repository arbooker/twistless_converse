module

public import QuantitativeEulerEndpointBaselineInitializerV1
public import QuantitativeEulerEndpointWideBaselineBoundsV1
public import QuantitativeEulerEndpointBandCornerV1
public import QuantitativeEulerEndpointInitialFullPolynomialV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointWideInitializer
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns Polynomial
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointSubcorner AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped Classical

variable (N : ℕ) [NeZero N] (sector : Sector N)
  {ι : Type*} [Fintype ι] (regions : ι → Set ℍ) (hs : ∀ i, IsCompact (regions i))
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
local notation "𝔄" => Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "ρ" => representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)
local notation "B" => QuantitativeEulerEndpointBaselineInitializer.rows N sector regions hs hε t
local notation "C" => fun i => wideDetectorBound N sector (R i) (Y i) (Hobs i) (t i)
local notation "hmB" => QuantitativeEulerEndpointBaselineInitializer.rows_measurable N sector regions hs hε t
local notation "hcB" => QuantitativeEulerEndpointBaselineInitializer.rows_covariant N sector regions hs hε t
local notation "hC" => fun i x => newBaselineDetector_wide_norm (hs i) hε (hY i) (hre i) (hlo i) (hhi i) N sector (t i) x
local notation "m" => QuantitativeEulerEndpointInitialWeighted.effort C a

def energy : 𝔄 := QuantitativeEulerEndpointInitialWeighted.energy
  (QuantitativeEulerEndpointInitialActual.gram action_measurable s₀ (region_measurable hs₀) p hp B hmB hcB C hC) C a

include ha in
/-- One explicitly bounded polynomial initializes every observation-region
budget simultaneously, fixes original baseline solutions, and retains every
prepared good prime. No initial detector budget is assumed. The initializer uses explicit
wide-rectangle detector bounds, not compactness-selected constants. -/
theorem exists_initial {excluded : Finset ℕ} {threshold : ℕ}
    (P : QuantitativeEulerDensityGenerators.Prepared N excluded threshold)
    (hex : baselineDenominators N⊆excluded) {J : ℕ} (hJ : 0<J) :
    ∃ q : ℝ[X], q.natDegree≤(16*J^5+1)*(2*m) ∧
      (∑ i∈q.support, |q.coeff i|)≤
        ((((16*J^5+1)*(2*m):ℕ):ℝ)+1)*((((16*J^5:ℕ):ℝ)+2)*3^(16*J^5))*2^((2*m)*(16*J^5+1)) ∧
      let F₀ := aeval (energy N sector regions hs hε H t R Y Hobs hY hre hlo hhi a) q
      0≤F₀ ∧ F₀≤1 ∧ τ (F₀-F₀^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, (∀ i j x, newBaselineRows N sector (hs i) hε (t i) x j*ρ E x=0) → F₀*E=E) ∧
      (∀ i x, 4*‖newBaselineDetector N sector (hs i) hε (t i) x*ρ F₀ x*
        star (newBaselineDetector N sector (hs i) hε (t i) x)‖≤a i) ∧
      (∀ r : EligiblePrime N, P.Good r.val → ∀ x, Supported (integralGroup r.val) (ρ F₀ x)) := by
  obtain ⟨q,hdeg,hmass,hq0,hq1,hdef,hfixed,hbudget,hsupport⟩ :=
    QuantitativeEulerEndpointInitialActual.exists_initial_polynomial
      action_measurable s₀ (region_measurable hs₀) p hp B hmB hcB C hC a ha τ
      (rootedTrace_mono action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)) hJ
  refine ⟨q,hdeg,hmass,hq0,hq1,hdef,?_,hbudget,?_⟩
  · intro E hE
    apply hfixed E
    intro i x
    exact QuantitativeEulerEndpointBaselineInitializer.detector_kills_of_rows
      N sector (hs i) hε (t i) (fun y => ρ E y) (hE i) x
  · intro r hr
    let : Fact r.val.Prime := ⟨r.property.1⟩
    exact hsupport (integralGroup r.val)
      (QuantitativeEulerEndpointBandCorner.projection_supported hε H (integralGroup r.val))
      (QuantitativeEulerEndpointBaselineInitializer.rows_supported
        N sector regions hs hε t r.val r.property.2 P hex hr)

#print axioms exists_initial
end QuantitativeEulerEndpointWideInitializer
