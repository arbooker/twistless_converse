module

public import QuantitativeEulerEndpointControlledIterationV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointControlledIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointSubcorner
open scoped ENNReal

/-- The exact soft coefficient loses at most the determinant ratio and
exponential attenuation in addition to the original prime product. -/
theorem coefficient_bounds {r θ e : ℝ} (hr0 : 0≤r) (hr1 : r≤1)
    (hθ0 : 0≤θ) (hθ1 : θ≤1) (he0 : 0≤e) (_he1 : e≤1) :
    0≤1-(1-e)*(1-r)*(1-θ) ∧
      1-(1-e)*(1-r)*(1-θ)≤r+θ+e := by
  have hfirst : (1-e)*(1-r)≤1 :=
    (mul_le_mul_of_nonneg_right (show 1-e≤1 by linarith) (sub_nonneg.mpr hr1)).trans (by linarith)
  have hsecond : (1-e)*(1-r)*(1-θ)≤1 :=
    (mul_le_mul_of_nonneg_right hfirst (sub_nonneg.mpr hθ1)).trans (by linarith)
  refine ⟨by linarith,?_⟩
  nlinarith [mul_nonneg hr0 hθ0, mul_nonneg hr0 he0,
    mul_nonneg (mul_nonneg he0 hθ0) (sub_nonneg.mpr hr1)]

theorem positive_part_step {x y a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (h : y≤a*x+b) : max 0 y≤a*max 0 x+b := by
  apply max_le
  · exact add_nonneg (mul_nonneg ha (le_max_left _ _)) hb
  · exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha) le_rfl)

variable (N : ℕ) (hN : 0<N) (w : ℂ) {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)

/-- A checked actual polynomial step gives a recurrence for nonnegative
excess, without assuming its signed trace lies above the comparison target. -/
theorem step_positive_excess (b : Packet N hN w hε) (hb : Scalars N hN w hε b)
    (A : 𝔄) (z : ℝ[X]) (target : ℝ) (hz : Step N hN w hε H b target A z)
    {D : ℝ} (hD : 0≤D) (hdef : τ (A-A^2)≤D) :
    max 0 (τ (next N hN w hε H b A z)-target)≤
      ((b.primes.map primeFactor).prod+theta N hN w hε b+
        Real.exp (-(b.steps:ℝ)*(b.d^2/32)))*max 0 (τ A-target)+
      (4+2*(b.steps:ℝ))*D+(measure s₀).toReal*(Real.log 2/Real.log (b.K/(2*b.d^2))) := by
  rcases hb with ⟨_hc,hd,_hK,hcut,_hnorm,hθ0,hθ1,_hJ⟩
  have he0 : 0≤Real.exp (-(b.steps:ℝ)*(b.d^2/32)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(b.steps:ℝ)*(b.d^2/32))≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity))
  have hcoef := coefficient_bounds (primeProduct_nonneg b.primes)
    (QuantitativeEulerEndpointPacketSoftUpdate.primeProduct_le_one b.primes) hθ0 hθ1 he0 he1
  have hlog : 0<Real.log (b.K/(2*b.d^2)) :=
    Real.log_pos ((one_lt_div (by positivity : 0<2*b.d^2)).mpr hcut)
  have hη : 0≤Real.log 2/Real.log (b.K/(2*b.d^2)) :=
    div_nonneg (Real.log_nonneg (by norm_num)) hlog.le
  have hmult : 0≤4+2*(b.steps:ℝ) := by positivity
  have herror : 0≤(4+2*(b.steps:ℝ))*D+(measure s₀).toReal*(Real.log 2/Real.log (b.K/(2*b.d^2))) :=
    add_nonneg (mul_nonneg hmult hD) (mul_nonneg ENNReal.toReal_nonneg hη)
  have hrec := hz.2.2.2.2.2.2
  have hrec' := hrec.trans (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hdef hmult)) le_rfl)
  have hpos := positive_part_step hcoef.1 herror (by simpa only [add_assoc] using hrec')
  exact hpos.trans (by
    have hh := mul_le_mul_of_nonneg_right hcoef.2 (le_max_left 0 (τ A-target))
    linarith)

#print axioms coefficient_bounds
#print axioms positive_part_step
#print axioms step_positive_excess
end QuantitativeEulerEndpointControlledIteration
