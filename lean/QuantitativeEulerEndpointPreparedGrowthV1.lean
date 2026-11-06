module

public import QuantitativeEulerEndpointObservationEnvelopeV1
public import QuantitativeEulerEndpointWideLogV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointNormalizedThreshold
open scoped Classical MatrixGroups

theorem wide_geometry_transport_bound (Bg D H G C X Y V : ℝ)
    (hV : 4≤V) (hBg0 : 0≤Bg) (hBg : Bg≤V) (hD0 : 0≤D) (hD : D≤V)
    (hH0 : 0≤H) (hH : H≤V) (hG0 : 0≤G) (hG : G≤V)
    (hC0 : 0≤C) (hC : C≤V) (hX0 : 0≤X) (hX : X≤V)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤V) :
    let R := Bg*(D*H+2+1)/min 1 Y
    let L := (2*G*C)*X^4
    wideDistortion L R R≤V^26 := by
  intro R L
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hV3 : 3≤V := by linarith
  have hmin : 0<min 1 Y := lt_min (by norm_num) hY
  have hDH : D*H≤V^2 := by nlinarith [mul_le_mul hD hH hH0 hV0]
  have htwo : (2:ℝ)≤V^2 := by nlinarith
  have hsum : D*H+2+1≤V^3 := two_height_sum_bound hV3 2 hDH htwo
  have hR0 : 0≤R := by dsimp only [R]; positivity
  have hR : R≤V^5 := by
    dsimp only [R]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (V*V^3)*V := mul_le_mul
        (mul_le_mul hBg hsum (by positivity) hV0) hYinv (inv_nonneg.mpr hmin.le) (by positivity)
      _ = _ := by ring
  have hL0 : 0≤L := by dsimp only [L]; positivity
  have hL : L≤V^7 := by
    dsimp only [L]
    calc
      _ ≤ (V*V*V)*V^4 := mul_le_mul
        (mul_le_mul (mul_le_mul (show (2:ℝ)≤V by linarith) hG hG0 hV0) hC hC0 (by positivity))
        (pow_le_pow_left₀ hX0 hX 4) (by positivity) (by positivity)
      _ = _ := by ring
  exact wideDistortion_power_bound hV3 7 5 hL0 hL hR0 hR hR0 hR

/-- Quantitative logarithmic normalization for the exact prepared
geometry, conditional only on elementary bounds for its explicit data. -/
theorem prepared_geometry_log_bound (N : ℕ) (w : ℂ)
    (Bg D H G C X Y V O Kobs : ℝ) (t : ℕ) (l : List (EligiblePrime N))
    (hV : 4≤V) (hBg0 : 0≤Bg) (hBg : Bg≤V) (hD0 : 0≤D) (hD : D≤V)
    (hH0 : 0≤H) (hH : H≤V) (hG0 : 0≤G) (hG : G≤V)
    (hC0 : 0≤C) (hC : C≤V) (hX0 : 0≤X) (hX : X≤V)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤V)
    (hN : (N:ℝ)≤V) (hw : ‖w‖≤V) (hq : ∀ p∈l, (p.val:ℝ)≤V) (hlen : (l.length:ℝ)≤V)
    (hO0 : 0≤O) (hO : O≤V^(7+72*t)) (hK0 : 0≤Kobs) (hK : Kobs≤V) :
    let R := Bg*(D*H+2+1)/min 1 Y
    let Z := Y/wideDistortion Bg 2 (D*H)
    let L := (2*G*C)*X^4
    let height := L*(R+R+1)/min 1 Z
    let low := Z/wideDistortion L R R
    let A := O*(Kobs*((wideDistortion L R R)^t)^2)
    Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor
      (wideSequenceBound N w (height+1) low height t l) l.length*threshold A)^2)≤
      Real.log 4+Real.log 3+2*Real.log (1+(72*9^t)^2)+
        ((8+124*(t:ℝ))+2*(1+2*(9+10*t)))*36*Real.log V := by
  intro R Z L height low A
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hVU : V≤V^36 := by simpa only [pow_one] using pow_le_pow_right₀ hV1 (by norm_num : 1≤36)
  have hU : 1≤V^36 := one_le_pow₀ hV1
  obtain ⟨hh0,hh,hl,hlmin⟩ := wide_geometry_envelope Bg D H G C X Y V
    hV hBg0 hBg hD0 hD hH0 hH hG0 hG hC0 hC hX0 hX hY hYinv
  have hd : wideDistortion L R R≤V^26 := wide_geometry_transport_bound Bg D H G C X Y V
    hV hBg0 hBg hD0 hD hH0 hH hG0 hG hC0 hC hX0 hX hY hYinv
  have hd0 := (wideDistortion_pos L R R).le
  have hA0 : 0≤A := by dsimp only [A]; positivity
  have hA : A≤V^(8+124*t) := by
    dsimp only [A]
    calc
      _ ≤ V^(7+72*t)*(V*((V^26)^t)^2) := mul_le_mul hO
        (mul_le_mul hK (pow_le_pow_left₀ (pow_nonneg hd0 t) (pow_le_pow_left₀ hd0 hd t) 2)
          (by positivity) hV0) (by positivity) (by positivity)
      _ = _ := by simp only [←pow_mul]; rw [←pow_succ',←pow_add]; congr 1; omega
  have hAU : A≤(V^36)^(8+124*t) := hA.trans (pow_le_pow_left₀ hV0 hVU _)
  have hlog := wide_normalization_log N w (height+1) low height (V^36) A t (8+124*t) l
    hU (hN.trans hVU) (fun p hp => (hq p hp).trans hVU) (hw.trans hVU)
    (by linarith) hh hh0 (by linarith) hl hlmin (hlen.trans hVU) hA0 hAU
  rw [Real.log_pow] at hlog
  push_cast at hlog
  convert hlog using 1
  ring

#print axioms wide_geometry_transport_bound
#print axioms prepared_geometry_log_bound
end QuantitativeEulerEndpointPrepared
