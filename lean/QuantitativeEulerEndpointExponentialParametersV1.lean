module

public import QuantitativeEulerEndpointBlockScheduleV1
public import QuantitativeEulerEndpointInitialEffortV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointExponentialParameters

def cut (E : ℝ) : ℝ := Real.exp (-E/2)
def power (E : ℝ) : ℕ := ⌈32*E*Real.exp E⌉₊
def sharpness (D E : ℝ) : ℕ := ⌈4*D*(4+2*(power E:ℝ))*E⌉₊+1

theorem cut_pos (E : ℝ) : 0<cut E := Real.exp_pos _

theorem cut_sq (E : ℝ) : (cut E)^2=Real.exp (-E) := by
  rw [cut,pow_two,←Real.exp_add]
  congr 1
  ring

theorem cut_log (E : ℝ) : Real.log (2/(2*(cut E)^2))=E := by
  rw [cut_sq]
  have he : (2:ℝ)/(2*Real.exp (-E))=Real.exp E := by
    rw [Real.exp_neg]
    field_simp
  rw [he,Real.log_exp]

theorem cut_conditions {E : ℝ} (hE : 0<E) :
    2*(cut E)^2<2 ∧ 1+(cut E)^2≤2 := by
  have hh : Real.exp (-E)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hE)
  rw [cut_sq]
  constructor <;> linarith

theorem attenuation {E : ℝ} (hE : 0<E) :
    Real.exp (-(power E:ℝ)*((cut E)^2/32))≤1/E := by
  have hpow : 32*E*Real.exp E≤(power E:ℝ) := Nat.le_ceil _
  have hc : 0≤(cut E)^2/32 := by positivity
  have hh := mul_le_mul_of_nonneg_right hpow hc
  have hid : (32*E*Real.exp E)*((cut E)^2/32)=E := by
    rw [cut_sq,Real.exp_neg]
    field_simp
  rw [hid] at hh
  have hfirst : Real.exp (-(power E:ℝ)*((cut E)^2/32))≤Real.exp (-E) :=
    Real.exp_le_exp.mpr (by nlinarith only [hh])
  have hlast : Real.exp (-E)≤1/E := by
    rw [Real.exp_neg,one_div]
    apply inv_anti₀ hE
    linarith [Real.add_one_le_exp E]
  exact hfirst.trans hlast

theorem power_upper {E : ℝ} (hE : 0≤E) : (power E:ℝ)≤32*E*Real.exp E+1 :=
  (Nat.ceil_lt_add_one (show 0≤32*E*Real.exp E by positivity)).le

theorem sharpness_pos (D E : ℝ) : 0<sharpness D E := Nat.succ_pos _

theorem sharpness_lower (D E : ℝ) :
    4*D*(4+2*(power E:ℝ))*E≤(sharpness D E:ℝ) := by
  have hh := Nat.le_ceil (4*D*(4+2*(power E:ℝ))*E)
  dsimp only [sharpness]
  push_cast
  linarith

theorem sharpness_upper {D E : ℝ} (hD : 0≤D) (hE : 0≤E) :
    (sharpness D E:ℝ)≤4*D*(4+2*(32*E*Real.exp E+1))*E+2 := by
  have hceil := Nat.ceil_lt_add_one (show 0≤4*D*(4+2*(power E:ℝ))*E by positivity)
  have hc : 4+2*(power E:ℝ)≤4+2*(32*E*Real.exp E+1) := by linarith [power_upper hE]
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (show 0≤4*D by positivity)) hE
  dsimp only [sharpness]
  push_cast
  linarith

/-- Choose the PREVIOUS sharpening degree from the next block's power.
This pays the actual propagated trace defect at the same 1/E scale. -/
theorem sharpness_error {D E T : ℝ} (_hD : 0≤D) (hE : 0<E) (hT : T≤D) :
    (4+2*(power E:ℝ))*(4*T/(sharpness D E:ℝ))≤1/E := by
  have hJ : 0<(sharpness D E:ℝ) := by exact_mod_cast sharpness_pos D E
  apply (le_div_iff₀ hE).mpr
  have hh := sharpness_lower D E
  have hm := mul_le_mul_of_nonneg_left hT
    (show 0≤4*(4+2*(power E:ℝ))*E by positivity)
  calc
    _ = ((4+2*(power E:ℝ))*(4*T)*E)/(sharpness D E:ℝ) := by ring
    _ ≤ 1 := (div_le_iff₀ hJ).mpr (by nlinarith only [hh,hm])

#print axioms cut_log
#print axioms cut_conditions
#print axioms attenuation
#print axioms power_upper
#print axioms sharpness_upper
#print axioms sharpness_error
end QuantitativeEulerEndpointExponentialParameters
