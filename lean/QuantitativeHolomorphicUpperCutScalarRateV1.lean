module

public import QuantitativeHolomorphicCutoffScalarBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open AsymptoticCylinderModeComparison AsymptoticFourierNorm AsymptoticCylinder

def upperMassCoefficient (t : ℕ) (scale : ℝ) : ℝ := 2*(2*t+1:ℝ)*Real.log 2/scale

theorem upperMassCoefficient_nonneg (t : ℕ) {scale : ℝ} (hs : 0<scale) :
    0≤upperMassCoefficient t scale := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold upperMassCoefficient
  positivity

theorem scheduled_upper_mass (h t : ℕ) {s : ℝ} (hs : 0≤s) :
    massBound (2*h) t (4*Real.pi) (Real.exp (16*s))/(2*h+2:ℝ)≤
      upperMassCoefficient t (4*Real.pi)*Real.exp (-16*s)+2/(2*h+2:ℝ) := by
  have hE : 1≤Real.exp (16*s) := Real.one_le_exp (by positivity)
  have hlog : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcut : Real.log 2≤(4*Real.pi)*Real.exp (16*s)/2 := by nlinarith [Real.two_le_pi]
  apply (normalized_massBound_le h t (by positivity) (Real.exp_pos _) hcut).trans_eq
  unfold upperMassCoefficient
  rw [show -16*s=-(16*s) by ring,Real.exp_neg]
  field_simp

def upperHeightCoefficient (M A : ℝ) : ℝ := 2*Real.sqrt (1+M)*Real.sqrt A+A

def upperWeightCoefficient (M : ℝ) : ℝ := 2*Real.sqrt (1+M)*Real.sqrt 2+2

theorem upperCutError_split {B M A b s k r : ℝ} (hB : 0≤B) (hM : 0≤M)
    (hA : 0≤A) (hb : 0≤b) (hs : 1≤s) (hk : 1≤k)
    (hB2 : B^2≤b*s^4) (hr : r≤A*Real.exp (-16*s)+2/k) :
    upperCutError (B^2*(1+M)) B 1 r≤
      (24*b*upperHeightCoefficient M A)*Real.exp (-3*s)+
      (b*upperWeightCoefficient M*s^4)*(Real.sqrt k)⁻¹ := by
  let z := (Real.sqrt k)⁻¹
  have hk0 : 0<k := by linarith
  have hz : 0≤z := by dsimp [z]; positivity
  have hz1 : z≤1 := by
    have hh : 1≤Real.sqrt k := (Real.le_sqrt (by norm_num) hk0.le).mpr (by simpa using hk)
    exact inv_le_one_of_one_le₀ hh
  have hz2 : z^2=1/k := by dsimp [z]; rw [inv_pow,Real.sq_sqrt hk0.le,one_div]
  have hE8sq : (Real.exp (-8*s))^2=Real.exp (-16*s) := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  have hu : 0≤Real.sqrt A*Real.exp (-8*s) := by positivity
  have hv : 0≤Real.sqrt 2*z := by positivity
  have hroot : Real.sqrt r≤Real.sqrt A*Real.exp (-8*s)+Real.sqrt 2*z := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hsA := Real.sq_sqrt hA
    have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have heq : (Real.sqrt A*Real.exp (-8*s))^2+(Real.sqrt 2*z)^2=A*Real.exp (-16*s)+2/k := by
      rw [mul_pow,mul_pow,hsA,hs2,hE8sq,hz2]
      ring
    nlinarith [mul_nonneg hu hv]
  have hE8 : Real.exp (-8*s)≤Real.exp (-4*s) := Real.exp_le_exp.mpr (by linarith)
  have hE16 : Real.exp (-16*s)≤Real.exp (-4*s) := Real.exp_le_exp.mpr (by linarith)
  have hr' : r≤A*Real.exp (-4*s)+2*z := by
    have he := mul_le_mul_of_nonneg_left hE16 hA
    have hrz : r≤A*Real.exp (-16*s)+2*z^2 := by
      rw [hz2]
      convert hr using 1
      ring
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have hroot' : Real.sqrt r≤Real.sqrt A*Real.exp (-4*s)+Real.sqrt 2*z := by
    have he := mul_le_mul_of_nonneg_left hE8 (Real.sqrt_nonneg A)
    linarith
  have hfactor : upperCutError (B^2*(1+M)) B 1 r=
      B^2*(2*Real.sqrt (1+M)*Real.sqrt r+r) := by
    unfold upperCutError
    rw [Real.sqrt_mul (sq_nonneg B),Real.sqrt_mul (sq_nonneg B),Real.sqrt_sq hB]
    ring
  have hU : 0≤upperHeightCoefficient M A := by unfold upperHeightCoefficient; positivity
  have hV : 0≤upperWeightCoefficient M := by unfold upperWeightCoefficient; positivity
  have hbracket : 2*Real.sqrt (1+M)*Real.sqrt r+r≤
      upperHeightCoefficient M A*Real.exp (-4*s)+upperWeightCoefficient M*z := by
    have hm := mul_le_mul_of_nonneg_left hroot' (by positivity : 0≤2*Real.sqrt (1+M))
    unfold upperHeightCoefficient upperWeightCoefficient
    nlinarith only [hm,hr']
  rw [hfactor]
  apply (mul_le_mul_of_nonneg_left hbracket (sq_nonneg B)).trans
  apply (mul_le_mul_of_nonneg_right hB2 (by positivity)).trans
  have hdecay := quartic_exp_decay (by linarith : 0≤s)
  have hm := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hb hU)
  dsimp only [z]
  nlinarith only [hm]

#print axioms upperCutError_split
#print axioms scheduled_upper_mass

end QuantitativeHolomorphic.Schedule
