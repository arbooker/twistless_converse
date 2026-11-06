module

public import QuantitativeEulerEndpointWideGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared

 theorem two_height_sum_bound {V x y : ℝ} (hV : 3≤V) (r : ℕ)
    (hx : x≤V^r) (hy : y≤V^r) : x+y+1≤V^(r+1) := by
  have hV1 : 1≤V := by linarith
  have hp : 1≤V^r := one_le_pow₀ hV1
  have hh := mul_le_mul_of_nonneg_right hV (show 0≤V^r by positivity)
  rw [pow_succ]
  nlinarith only [hx,hy,hp,hh]

theorem wideDistortion_power_bound {V B R H : ℝ} (hV : 3≤V) (b r : ℕ)
    (hB0 : 0≤B) (hB : B≤V^b) (hR0 : 0≤R) (hR : R≤V^r)
    (hH0 : 0≤H) (hH : H≤V^r) :
    wideDistortion B R H≤V^(2*(b+r+1)) := by
  have hV1 : 1≤V := by linarith
  have hprod : B*(H+R+1)≤V^(b+r+1) := by
    calc
      _ ≤ V^b*V^(r+1) := mul_le_mul hB (two_height_sum_bound hV r hH hR) (by positivity) (by positivity)
      _ = _ := by rw [←pow_add]; congr 1
  apply max_le (one_le_pow₀ hV1)
  calc
    _ ≤ (V^(b+r+1))^2 := pow_le_pow_left₀ (by positivity) hprod 2
    _ = _ := by rw [←pow_mul]; congr 1; omega

theorem inv_min_power_bound {x V : ℝ} (hV : 1≤V) (r : ℕ)
    (hx : x⁻¹≤V^r) : (min 1 x)⁻¹≤V^r := by
  by_cases hh : x≤1
  · rwa [min_eq_right hh]
  · rw [min_eq_left (le_of_not_ge hh),inv_one]
    exact one_le_pow₀ hV

/-- The exact rectangles used by the actual initialized iteration admit
one polynomial envelope. V bounds all fixed data, the common height and
this block's prime cutoff. In particular, the reciprocal small height
costs only a fixed power of V. -/
theorem wide_geometry_envelope (Bg D H G C X Y V : ℝ)
    (hV : 4≤V) (hBg0 : 0≤Bg) (hBg : Bg≤V) (hD0 : 0≤D) (hD : D≤V)
    (hH0 : 0≤H) (hH : H≤V) (hG0 : 0≤G) (hG : G≤V)
    (hC0 : 0≤C) (hC : C≤V) (hX0 : 0≤X) (hX : X≤V)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤V) :
    let R := Bg*(D*H+2+1)/min 1 Y
    let Z := Y/wideDistortion Bg 2 (D*H)
    let L := (2*G*C)*X^4
    let height := L*(R+R+1)/min 1 Z
    let low := Z/wideDistortion L R R
    0≤height ∧ height+1≤V^36 ∧ 0<low ∧ (min 1 low)⁻¹≤V^36 := by
  intro R Z L height low
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hV3 : 3≤V := by linarith
  have hmin : 0<min 1 Y := lt_min (by norm_num) hY
  have hYinv' : Y⁻¹≤V := (inv_le_inv₀ hY hmin).mpr (min_le_right _ _) |>.trans hYinv
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
  have hfirst : wideDistortion Bg 2 (D*H)≤V^8 :=
    wideDistortion_power_bound hV3 1 2 hBg0 (by simpa only [pow_one] using hBg)
      (by norm_num) htwo (mul_nonneg hD0 hH0) hDH
  have hZ : 0<Z := div_pos hY (wideDistortion_pos _ _ _)
  have hZinv : Z⁻¹≤V^9 := by
    dsimp only [Z]
    rw [inv_div,div_eq_mul_inv]
    calc
      _ ≤ V^8*V := mul_le_mul hfirst hYinv' (inv_nonneg.mpr hY.le) (by positivity)
      _ = _ := by ring
  have hminZ := inv_min_power_bound hV1 9 hZinv
  have hL0 : 0≤L := by dsimp only [L]; positivity
  have hL : L≤V^7 := by
    dsimp only [L]
    calc
      _ ≤ (V*V*V)*V^4 := mul_le_mul
        (mul_le_mul (mul_le_mul (show (2:ℝ)≤V by linarith) hG hG0 hV0) hC hC0 (by positivity))
        (pow_le_pow_left₀ hX0 hX 4) (by positivity) (by positivity)
      _ = _ := by ring
  have hRsum : R+R+1≤V^6 := two_height_sum_bound hV3 5 hR hR
  have hh0 : 0≤height := by dsimp only [height]; positivity
  have hh : height≤V^22 := by
    dsimp only [height]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (V^7*V^6)*V^9 := mul_le_mul
        (mul_le_mul hL hRsum (by positivity) (by positivity)) hminZ
        (inv_nonneg.mpr (lt_min (by norm_num) hZ).le) (by positivity)
      _ = _ := by ring
  have hsecond : wideDistortion L R R≤V^26 :=
    wideDistortion_power_bound hV3 7 5 hL0 hL hR0 hR hR0 hR
  have hlow : 0<low := div_pos hZ (wideDistortion_pos _ _ _)
  have hlowinv : low⁻¹≤V^35 := by
    dsimp only [low]
    rw [inv_div,div_eq_mul_inv]
    calc
      _ ≤ V^26*V^9 := mul_le_mul hsecond hZinv (inv_nonneg.mpr hZ.le) (by positivity)
      _ = _ := by ring
  refine ⟨hh0,?_,hlow,?_⟩
  · have hh23 : height+1≤V^23 := by
      have ht := two_height_sum_bound hV3 22 hh (show (0:ℝ)≤V^22 by positivity)
      simpa only [add_zero] using ht
    exact hh23.trans (pow_le_pow_right₀ hV1 (by norm_num))
  · exact (inv_min_power_bound hV1 35 hlowinv).trans (pow_le_pow_right₀ hV1 (by norm_num))

#print axioms wide_geometry_envelope
end QuantitativeEulerEndpointPrepared
