module

public import QuantitativeEulerEndpointInitialSharpenV1
public import QuantitativeEulerEndpointRegularBaseV1
public import QuantitativeEulerEndpointNewBaselineV1
public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBaselineInitializer
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack AsymptoticPolarIsometry
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointSubcorner AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped Classical

variable (N : ℕ) [NeZero N] (sector : Sector N)

def detectorBound {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖*
    ∑ i, newBaselineRowBound N sector hs hε t i

theorem detector_norm {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) : ‖newBaselineDetector N sector hs hε t x‖≤detectorBound N sector hs hε t := by
  rw [newBaselineDetector,absolute_opNorm]
  exact stack_norm_le _ _ (newBaselineRowBound_nonneg N sector hs hε t)
    (newBaselineRows_norm N sector hs hε t x)

/-- The apparent square root in the detector disappears from its Gram:
initialization is polynomial in finitely many original row operators. -/
theorem detector_gram {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) :
    star (newBaselineDetector N sector hs hε t x)*newBaselineDetector N sector hs hε t x=
      ∑ i, star (newBaselineRows N sector hs hε t x i)*newBaselineRows N sector hs hε t x i := by
  exact (absolute_gram _).trans (stack_gram _)

theorem detector_kills_of_rows {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (E : ℍ → Space →L[ℂ] Space)
    (hE : ∀ i x, newBaselineRows N sector hs hε t x i*E x=0) (x : ℍ) :
    newBaselineDetector N sector hs hε t x*E x=0 := by
  apply ContinuousLinearMap.ext
  intro v
  change newBaselineDetector N sector hs hε t x (E x v)=0
  apply norm_eq_zero.mp
  rw [newBaselineDetector,← absolute_norm]
  have he : stack (newBaselineRows N sector hs hε t x) (E x v)=0 := by
    ext i : 1
    exact congrArg (fun T : Space →L[ℂ] Space => T v) (hE i x)
  rw [he,norm_zero]

variable {ι : Type*} (regions : ι → Set ℍ) (hs : ∀ i, IsCompact (regions i))
  {ε : ℝ} (hε : 0<ε) (t : ι → ℕ)

def rows (i : ι) (x : Base) : Space →L[ℂ] Space := newBaselineDetector N sector (hs i) hε (t i) x

def bounds (i : ι) : ℝ := detectorBound N sector (hs i) hε (t i)

theorem rows_measurable (i : ι) : ∀ g h, Measurable (fun x => matrix (rows N sector regions hs hε t i x) g h) := by
  obtain ⟨_,_,_,hm,_⟩ := newBaselineDetector_regular N sector (hs i) hε (t i)
  exact hm

theorem rows_covariant (i : ι) : Covariant (rows N sector regions hs hε t i) := by
  obtain ⟨_,_,_,_,hc⟩ := newBaselineDetector_regular N sector (hs i) hε (t i)
  exact hc

theorem rows_norm (i : ι) (x : Base) : ‖rows N sector regions hs hε t i x‖≤bounds N sector regions hs hε t i :=
  detector_norm N sector (hs i) hε (t i) x

theorem rows_supported (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N)
    {excluded : Finset ℕ} {threshold : ℕ} (P : QuantitativeEulerDensityGenerators.Prepared N excluded threshold)
    (hex : baselineDenominators N⊆excluded) (hq : P.Good q) (i : ι) (x : Base) :
    Supported (integralGroup q) (rows N sector regions hs hε t i x) :=
  newBaselineDetector_supported N sector q hqN (good_prime_avoids_baseline P hex q hq) (hs i) hε (t i) x

variable [Fintype ι]
variable {s₀ : Set ℍ} (hs₀ : IsCompact s₀) (p : Corner hs₀) (hp : IsStarProjection p)
  (a : ι → ℝ) (ha : ∀ i, 0<a i)
local notation "𝔄" => Subcorner action_measurable (region s₀) (region_measurable hs₀) p hp
local notation "ρ" => representation action_measurable (region s₀) (region_measurable hs₀) p hp
local notation "B" => rows N sector regions hs hε t
local notation "C" => bounds N sector regions hs hε t
local notation "hmB" => rows_measurable N sector regions hs hε t
local notation "hcB" => rows_covariant N sector regions hs hε t
local notation "hC" => rows_norm N sector regions hs hε t
local notation "m" => QuantitativeEulerEndpointInitialWeighted.effort C a

def initial : 𝔄 := QuantitativeEulerEndpointInitialActual.filter
  action_measurable (region s₀) (region_measurable hs₀) p hp B hmB hcB C hC a m

include ha in
theorem initial_order : 0 ≤ initial N sector regions hs hε t hs₀ p hp a ∧
    initial N sector regions hs hε t hs₀ p hp a≤1 :=
  QuantitativeEulerEndpointInitialActual.filter_order
    action_measurable (region s₀) (region_measurable hs₀) p hp B hmB hcB C hC a ha m

include ha in
theorem initial_detector_budget (i : ι) (x : ℍ) :
    4*‖newBaselineDetector N sector (hs i) hε (t i) x*
      ρ (initial N sector regions hs hε t hs₀ p hp a) x*
      star (newBaselineDetector N sector (hs i) hε (t i) x)‖≤a i :=
  QuantitativeEulerEndpointInitialActual.filter_detector_budget
    action_measurable (region s₀) (region_measurable hs₀) p hp B hmB hcB C hC a ha m
    (QuantitativeEulerEndpointInitialWeighted.effort_budget C a) i x

theorem initial_fixed (E : 𝔄)
    (hE : ∀ i j x, newBaselineRows N sector (hs i) hε (t i) x j*ρ E x=0) :
    initial N sector regions hs hε t hs₀ p hp a*E=E := by
  apply QuantitativeEulerEndpointInitialActual.filter_fixed
  intro i x
  exact detector_kills_of_rows N sector (hs i) hε (t i) (fun y => ρ E y) (hE i) x

#print axioms detector_norm
#print axioms detector_gram
#print axioms detector_kills_of_rows
#print axioms rows_supported
#print axioms initial_order
#print axioms initial_detector_budget
#print axioms initial_fixed
end QuantitativeEulerEndpointBaselineInitializer
