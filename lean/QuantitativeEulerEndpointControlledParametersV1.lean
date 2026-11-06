module

public import QuantitativeEulerEndpointControlledIterationBoundV1
public import QuantitativeEulerEndpointExponentialParametersV1
public import QuantitativeEulerEndpointLocalEffortV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointControlledParameters
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointControlledIteration QuantitativeEulerEndpointBlocks
open QuantitativeEulerEndpointExponentialParameters
open scoped ENNReal

variable (N : ℕ) (hN : 0<N) (w : ℂ) {ε : ℝ} (hε : 0<ε)

def logCost (b : Packet N hN w hε) : ℝ := Real.log (2/(factor N hN w hε b*b.c)^2)
def effort (n j : ℕ) (b : ℕ → Packet N hN w hε) : ℝ :=
  QuantitativeEulerEndpointLocalEffort.effort n j (logCost N hN w hε (b j))
def scheduled (n : ℕ) (D : ℝ) (b : ℕ → Packet N hN w hε) (j : ℕ) : Packet N hN w hε :=
  { b j with
    d := cut (effort N hN w hε n j b)
    K := 2
    steps := power (effort N hN w hε n j b)
    J := sharpness D (effort N hN w hε n (j+1) b) }
def initialSharpness (n : ℕ) (D : ℝ) (b : ℕ → Packet N hN w hε) : ℕ :=
  sharpness D (effort N hN w hε n 0 b)

theorem logCost_nonneg (b : Packet N hN w hε) (hc : 0<b.c)
    (hu : factor N hN w hε b*b.c≤1) : 0≤logCost N hN w hε b := by
  have hf : 0<factor N hN w hε b := QuantitativeEulerEndpointBlockNormalization.factor_pos _ _
  have hu0 : 0<factor N hN w hε b*b.c := mul_pos hf hc
  apply Real.log_nonneg
  apply (one_le_div (sq_pos_of_pos hu0)).mpr
  nlinarith

theorem relative_le_one (n j : ℕ) (hj : j≤n) : blockRelativeLoss n j≤1 := by
  apply (div_le_one (by positivity : 0<(2:ℝ)^n)).mpr
  exact pow_le_pow_right₀ (by norm_num) hj

theorem additive_le_relative (n j : ℕ) : blockAdditiveLoss n j≤blockRelativeLoss n j := by
  unfold blockAdditiveLoss blockEffort blockRelativeLoss
  calc
    _ ≤ 1/(2:ℝ)^n := one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n j))
    _ ≤ _ := div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)

theorem scheduled_theta (n j : ℕ) (D : ℝ) (b : ℕ → Packet N hN w hε) :
    theta N hN w hε (scheduled N hN w hε n D b j)=
      logCost N hN w hε (b j)/effort N hN w hε n j b := by
  change Real.log (2/(factor N hN w hε (b j)*(b j).c)^2)/
    Real.log (2/(2*(cut (effort N hN w hε n j b))^2))=_
  rw [cut_log]
  rfl

theorem scheduled_scalars (n j : ℕ) (hj : j≤n) (D : ℝ) (b : ℕ → Packet N hN w hε)
    (hc : 0<(b j).c) (hu : factor N hN w hε (b j)*(b j).c≤1) :
    Scalars N hN w hε (scheduled N hN w hε n D b j) := by
  have hM := logCost_nonneg N hN w hε (b j) hc hu
  have hE := QuantitativeEulerEndpointLocalEffort.effort_pos n j hM
  have hcuts := cut_conditions hE
  refine ⟨hc,cut_pos _,by norm_num [scheduled],hcuts.1,hcuts.2,?_,?_,sharpness_pos _ _⟩
  · rw [scheduled_theta]
    exact div_nonneg hM hE.le
  · rw [scheduled_theta]
    exact (QuantitativeEulerEndpointLocalEffort.effort_ratio n j hj hM).trans (relative_le_one n j hj)

/-- Both relative losses are controlled by the explicit finite-horizon
schedule, using the actual normalized threshold of this packet. -/
theorem scheduled_relative (n j : ℕ) (hj : j≤n) (D : ℝ) (b : ℕ → Packet N hN w hε)
    (hc : 0<(b j).c) (hu : factor N hN w hε (b j)*(b j).c≤1) :
    theta N hN w hε (scheduled N hN w hε n D b j)+
      Real.exp (-((scheduled N hN w hε n D b j).steps:ℝ)*
        ((scheduled N hN w hε n D b j).d^2/32))≤2*blockRelativeLoss n j := by
  have hM := logCost_nonneg N hN w hε (b j) hc hu
  have hE := QuantitativeEulerEndpointLocalEffort.effort_pos n j hM
  have hθ := QuantitativeEulerEndpointLocalEffort.effort_ratio n j hj hM
  have hatt := (attenuation hE).trans
    ((QuantitativeEulerEndpointLocalEffort.effort_inverse n j hj hM).trans (additive_le_relative n j))
  rw [scheduled_theta]
  change logCost N hN w hε (b j)/effort N hN w hε n j b+
    Real.exp (-(power (effort N hN w hε n j b):ℝ)*((cut (effort N hN w hε n j b))^2/32))≤_
  dsimp only [effort]
  linarith

theorem incoming_sharpness (n j : ℕ) (D : ℝ) (b : ℕ → Packet N hN w hε) :
    incomingSharpness N hN w hε (initialSharpness N hN w hε n D b) (scheduled N hN w hε n D b) j=
      sharpness D (effort N hN w hε n j b) := by
  cases j <;> rfl

/-- The previous block's chosen sharpening pays the next block's actual
amplification. The determinant error is paid by the same effort. -/
theorem scheduled_additive (n j : ℕ) (hj : j≤n) (D : ℝ) (hD : 0≤D) (b : ℕ → Packet N hN w hε)
    (hc : 0<(b j).c) (hu : factor N hN w hε (b j)*(b j).c≤1)
    {T area : ℝ} (hT : T≤D) (harea : area≤D) :
    let bs := scheduled N hN w hε n D b
    (4+2*((bs j).steps:ℝ))*(4*T/(incomingSharpness N hN w hε (initialSharpness N hN w hε n D b) bs j:ℝ))+
      area*(Real.log 2/Real.log ((bs j).K/(2*(bs j).d^2)))≤
      (1+D*Real.log 2)*blockAdditiveLoss n j := by
  dsimp only
  rw [incoming_sharpness]
  change (4+2*(power (effort N hN w hε n j b):ℝ))*(4*T/(sharpness D (effort N hN w hε n j b):ℝ))+
    area*(Real.log 2/Real.log (2/(2*(cut (effort N hN w hε n j b))^2)))≤_
  rw [cut_log]
  have hM := logCost_nonneg N hN w hε (b j) hc hu
  have hE := QuantitativeEulerEndpointLocalEffort.effort_pos n j hM
  have hs := sharpness_error hD hE hT
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have ha := mul_le_mul_of_nonneg_right harea (div_nonneg hlog hE.le)
  have hi := mul_le_mul_of_nonneg_left
    (QuantitativeEulerEndpointLocalEffort.effort_inverse n j hj hM)
    (show 0≤1+D*Real.log 2 by positivity)
  have he : (1+D*Real.log 2)*(1/effort N hN w hε n j b)=
    1/effort N hN w hε n j b+D*(Real.log 2/effort N hN w hε n j b) := by ring
  dsimp only [effort] at he ⊢
  rw [he] at hi
  linarith

#print axioms scheduled_scalars
#print axioms scheduled_relative
#print axioms incoming_sharpness
#print axioms scheduled_additive
end QuantitativeEulerEndpointControlledParameters
