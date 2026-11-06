module

public import QuantitativeEulerEndpointControlledStepExcessV1
public import QuantitativeEulerEndpointFiniteScheduleV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointControlledIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace Polynomial Finset
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlocks
open scoped ENNReal

variable (N : ℕ) (hN : 0<N) (w : ℂ) {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)

def incomingSharpness (J₀ : ℕ) (b : ℕ → Packet N hN w hε) : ℕ → ℕ
  | 0 => J₀
  | j+1 => (b j).J

/-- Incoming trace defects are discharged by the initializer and the
previous block's sharpening, including the first and final steps. -/
theorem incoming_defect_bound (n J₀ : ℕ) (b : ℕ → Packet N hN w hε) (target : ℝ)
    (F : ℕ → 𝔄) (z : ℕ → ℝ[X])
    (hinit : τ (F 0-(F 0)^2)≤4*τ 1/(J₀:ℝ))
    (hsteps : ∀ j, j<n → Step N hN w hε H (b j) target (F j) (z j) ∧
      F (j+1)=next N hN w hε H (b j) (F j) (z j)) :
    ∀ j, j≤n → τ (F j-(F j)^2)≤4*τ 1/(incomingSharpness N hN w hε J₀ b j:ℝ) := by
  intro j hj
  cases j with
  | zero => exact hinit
  | succ j =>
    obtain ⟨hs,he⟩ := hsteps j (by omega)
    rw [he]
    exact hs.2.2.2.2.1

/-- Endpoint decay for the actual constructed sequence, conditional only
on explicit scalar bounds for prime loss, threshold regularization and
sharpening effort. The signed excess is replaced by its positive part. -/
theorem finite_iteration_bound (n J₀ : ℕ) (b : ℕ → Packet N hN w hε) (target : ℝ)
    (F : ℕ → 𝔄) (z : ℕ → ℝ[X])
    (hb : ∀ j, j<n → Scalars N hN w hε (b j))
    (hinit : τ (F 0-(F 0)^2)≤4*τ 1/(J₀:ℝ))
    (hsteps : ∀ j, j<n → Step N hN w hε H (b j) target (F j) (z j) ∧
      F (j+1)=next N hN w hε H (b j) (F j) (z j))
    (bad : ℕ → ℝ) {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hbad : ∀ j, 0≤bad j) (hbudget : (∑ j∈range n, bad j)≤C)
    (hrelative : ∀ j, j<n → ((b j).primes.map primeFactor).prod+
      theta N hN w hε (b j)+Real.exp (-((b j).steps:ℝ)*((b j).d^2/32))≤
      Real.exp (bad j)/4+A*blockRelativeLoss n j)
    (hadditive : ∀ j, j<n →
      (4+2*((b j).steps:ℝ))*(4*τ 1/(incomingSharpness N hN w hε J₀ b j:ℝ))+
        (measure s₀).toReal*(Real.log 2/Real.log ((b j).K/(2*(b j).d^2)))≤B*blockAdditiveLoss n j) :
    max 0 (τ (F n)-target)≤
      Real.exp (C+4*A)*(max 0 (τ (F 0)-target)+4*B)/(4:ℝ)^n := by
  have hτ1 : 0≤τ 1 := by
    simpa only [map_zero] using
      rootedTrace_mono action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)
        (show (0:𝔄)≤1 by simpa only [star_one,mul_one] using star_mul_self_nonneg (1:𝔄))
  apply finite_schedule_endpoint n (fun j => max 0 (τ (F j)-target)) bad hA hB
    (fun _ _ => le_max_left _ _) hbad hbudget
  intro j hj
  obtain ⟨hs,he⟩ := hsteps j hj
  have hD : 0≤4*τ 1/(incomingSharpness N hN w hε J₀ b j:ℝ) := by positivity
  have hrec := step_positive_excess N hN w hε H (b j) (hb j hj) (F j) (z j) target hs hD
    (incoming_defect_bound N hN w hε H n J₀ b target F z hinit hsteps j (by omega))
  rw [←he] at hrec
  exact hrec.trans (by
    have hh := add_le_add
      (mul_le_mul_of_nonneg_right (hrelative j hj) (le_max_left 0 (τ (F j)-target))) (hadditive j hj)
    simpa only [add_assoc] using hh)

#print axioms incoming_defect_bound
#print axioms finite_iteration_bound
end QuantitativeEulerEndpointControlledIteration
