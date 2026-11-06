module

public import QuantitativeHolomorphicGrowingFilterHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

theorem normalizedLength_growth {R a b u : ℝ} (hR : 0≤R) (ha : 0≤a)
    (_hb : 0≤b) (hu : 1≤u) (n : ℕ) (hRE : R≤Real.exp (a*u^2))
    (hn : (4:ℝ)^n≤b*u) :
    R*(3+R^2)^(4^n)≤Real.exp ((a+b*(4+2*a))*u^3) := by
  have hu2 : 1≤u^2 := by nlinarith
  have hu23 : u^2≤u^3 := by nlinarith [mul_nonneg (by nlinarith : 0≤u-1) (sq_nonneg u)]
  have hE : 1≤Real.exp ((2*a)*u^2) := Real.one_le_exp (by positivity)
  have hR2 : R^2≤Real.exp ((2*a)*u^2) := by
    have hm := mul_self_le_mul_self hR hRE
    calc
      _ ≤ Real.exp (a*u^2)*Real.exp (a*u^2) := by nlinarith only [hm]
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hbase : 3+R^2≤Real.exp ((4+2*a)*u^2) :=
    (show 3+R^2≤4*Real.exp ((2*a)*u^2) by linarith).trans
      (constant_mul_exp_le (by norm_num) hu2)
  have hn' : ((4^n:ℕ):ℝ)≤b*u := by exact_mod_cast hn
  have hp : (3+R^2)^(4^n)≤Real.exp (b*(4+2*a)*u^3) := by
    apply (pow_le_pow_left₀ (by positivity) hbase (4^n)).trans
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hn' (by positivity : 0≤(4+2*a)*u^2)
    nlinarith only [hm]
  have hr : R≤Real.exp (a*u^3) := hRE.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu23 ha))
  apply (mul_le_mul hr hp (by positivity) (Real.exp_nonneg _)).trans_eq
  rw [←Real.exp_add]
  congr 1
  ring

theorem scalarFilter_growth {V S a b C s : ℝ} (hV0 : 0≤V) (hS0 : 0≤S)
    (ha : 0≤a) (hb : 0≤b) (hC : 0≤C) (hs : 1≤s) (d : ℕ)
    (hd : (d:ℝ)≤Real.exp (C*s^2)) (hV : V≤Real.exp (a*s^12))
    (hS : S≤Real.exp (b*s^2)) :
    V^2*(1+S*V^2)^d≤Real.exp (Real.exp ((14+4*a+b+C)*s^2)) := by
  let u := s^12
  have hu : 1≤u := by dsimp [u]; simpa using (pow_le_pow_right₀ hs (by norm_num : 0≤12))
  have hs212 : s^2≤u := pow_le_pow_right₀ hs (by norm_num)
  have hSE : S≤Real.exp (b*u) := hS.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs212 hb))
  have hV2 : V^2≤Real.exp ((2*a)*u) := by
    have hm := mul_self_le_mul_self hV0 hV
    calc
      _ ≤ Real.exp (a*u)*Real.exp (a*u) := by nlinarith only [hm]
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hprod : S*V^2≤Real.exp ((b+2*a)*u) := by
    apply (mul_le_mul hSE hV2 (sq_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [←Real.exp_add]
    congr 1
    ring
  have hE : 1≤Real.exp ((b+2*a)*u) := Real.one_le_exp (by positivity)
  have hbase : 1+S*V^2≤Real.exp ((2+b+2*a)*u) := by
    apply (show 1+S*V^2≤2*Real.exp ((b+2*a)*u) by linarith).trans
    convert constant_mul_exp_le (c:=2) (a:=b+2*a) (by norm_num) hu using 1
    congr 1
    ring
  have hp : (1+S*V^2)^d≤Real.exp ((d:ℝ)*((2+b+2*a)*u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hbase d
  apply (mul_le_mul hV2 hp (by positivity) (Real.exp_nonneg _)).trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hEC : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
  have hc : 2*a+(d:ℝ)*(2+b+2*a)≤(2+4*a+b)*Real.exp (C*s^2) := by
    have h1 := mul_le_mul_of_nonneg_left hEC (by positivity : 0≤2*a)
    have h2 := mul_le_mul_of_nonneg_right hd (by positivity : 0≤2+b+2*a)
    nlinarith only [h1,h2]
  have hh := mul_le_mul_of_nonneg_right hc (by positivity : 0≤u)
  have he := polynomial_mul_exp_quadratic_le 12 (b:=2+4*a+b) (C:=C) (by positivity) hs
  calc
    _ ≤ (2+4*a+b)*s^12*Real.exp (C*s^2) := by dsimp [u] at hh; nlinarith only [hh]
    _ ≤ _ := by convert he using 1; congr 1; ring

theorem twice_double_exp_le {K s : ℝ} (hK : 0≤K) (hs : 1≤s) :
    2*Real.exp (Real.exp (K*s^2))≤Real.exp (Real.exp ((K+2)*s^2)) := by
  have hs2 : 1≤s^2 := by nlinarith
  have hE : 1≤Real.exp (K*s^2) := Real.one_le_exp (by positivity)
  have h2 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have htop : 1+Real.exp (K*s^2)≤Real.exp ((K+2)*s^2) := by
    apply (show 1+Real.exp (K*s^2)≤2*Real.exp (K*s^2) by linarith).trans
    convert constant_mul_exp_le (c:=2) (a:=K) (by norm_num) hs2 using 1
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)).trans
  rw [←Real.exp_add]
  exact Real.exp_le_exp.mpr htop

#print axioms normalizedLength_growth
#print axioms scalarFilter_growth

end QuantitativeHolomorphic.Schedule
