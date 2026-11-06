module

public import QuantitativeHolomorphicGrowingNormalizedMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

theorem polynomial_mul_exp_quadratic_le (m : ℕ) {b C s : ℝ} (hb : 0≤b) (hs : 1≤s) :
    b*s^m*Real.exp (C*s^2)≤Real.exp ((b+m+C)*s^2) := by
  have hs0 : 0≤s := by linarith
  have hse : s≤Real.exp s := by linarith [Real.add_one_le_exp s]
  have hp : s^m≤Real.exp ((m:ℝ)*s) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hs0 hse m
  have hbE : b≤Real.exp b := by linarith [Real.add_one_le_exp b]
  have hm := mul_le_mul hbE hp (pow_nonneg hs0 _) (Real.exp_nonneg _)
  apply (mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)).trans
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs2 : 1≤s^2 := by nlinarith
  have hss : s≤s^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs2 hb,
    mul_le_mul_of_nonneg_left hss (Nat.cast_nonneg m : (0:ℝ)≤m)]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- Double-exponential height of the literal full filter. The only new
geometric input bounds the sum of actual row heights; reconstruction and
filter powers are calculated from their displayed definitions. -/
theorem quantifiedFilterMatrixHeight_growth (hN : 0<N) (qs : Finset ι) (r : ι → Row N)
    (L U : ℝ) (j J n d : ℕ) {a b C s : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hC : 0≤C) (hs : 1≤s)
    (hd : (d:ℝ)≤Real.exp (C*s^2))
    (hV : normalizedCountMatrixHeight A hN j J n≤Real.exp (a*s^12))
    (hrows : (∑ i∈qs, quantifiedRowHeight hN (r i) L U)≤Real.exp (b*s^2)) :
    quantifiedFilterMatrixHeight A hN qs r L U j J n d≤
      Real.exp (Real.exp ((26+4*a+2*b+C)*s^2)) := by
  let V := normalizedCountMatrixHeight A hN j J n
  let R := ∑ i∈qs, quantifiedRowHeight hN (r i) L U
  let u := s^12
  have hu : 1≤u := by dsimp [u]; simpa using (pow_le_pow_right₀ hs (by norm_num : 0≤12))
  have hs212 : s^2≤u := pow_le_pow_right₀ hs (by norm_num)
  have hR0 : 0≤R := Finset.sum_nonneg (fun i _ => quantifiedRowHeight_nonneg hN (r i) L U)
  have hV0 : 0≤V := by
    have hraw : 0≤rawCountMatrixHeight A hN j J := le_trans zero_le_one (rawCountMatrixHeight_one_le A hN j J)
    dsimp [V,normalizedCountMatrixHeight]
    positivity
  have hRE : R≤Real.exp (b*u) := hrows.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs212 hb))
  have hR2 : R^2≤Real.exp ((2*b)*u) := by
    have h := mul_self_le_mul_self hR0 hRE
    calc
      _ ≤ Real.exp (b*u)*Real.exp (b*u) := by nlinarith only [h]
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hV2 : V^2≤Real.exp ((2*a)*u) := by
    have h := mul_self_le_mul_self hV0 hV
    calc
      _ ≤ Real.exp (a*u)*Real.exp (a*u) := by nlinarith only [h]
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hprod := mul_le_mul hR2 hV2 (sq_nonneg _) (Real.exp_nonneg _)
  have hbase : 8*R^2*V^2≤Real.exp ((8+2*b+2*a)*u) := by
    have hh : 8*R^2*V^2≤8*Real.exp ((2*b+2*a)*u) := by
      have hm := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤8)
      rw [←Real.exp_add] at hm
      calc
        _ = 8*(R^2*V^2) := by ring
        _ ≤ 8*Real.exp (2*b*u+2*a*u) := hm
        _ = _ := by congr 1; congr 1; ring
    apply hh.trans
    convert constant_mul_exp_le (c:=8) (a:=2*b+2*a) (by norm_num) hu using 1
    congr 1
    ring
  have hmax : max 1 (8*R^2*V^2)≤Real.exp ((8+2*b+2*a)*u) := by
    apply max_le _ hbase
    apply Real.one_le_exp
    positivity
  have hstep : 2*max 1 (8*R^2*V^2)≤Real.exp ((10+2*b+2*a)*u) := by
    apply (mul_le_mul_of_nonneg_left hmax (by norm_num)).trans
    convert constant_mul_exp_le (c:=2) (a:=8+2*b+2*a) (by norm_num) hu using 1
    congr 1
    ring
  have hpower : (2*max 1 (8*R^2*V^2))^d≤Real.exp ((d:ℝ)*((10+2*b+2*a)*u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hstep d
  have hfront : 4*V^2≤Real.exp ((4+2*a)*u) :=
    (mul_le_mul_of_nonneg_left hV2 (by norm_num)).trans (constant_mul_exp_le (by norm_num) hu)
  have hfull := mul_le_mul hfront hpower (by positivity) (Real.exp_nonneg _)
  change 4*V^2*(2*max 1 (8*R^2*V^2))^d≤_
  apply hfull.trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hE : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
  have hcoef : (4+2*a)+(d:ℝ)*(10+2*b+2*a)≤(14+4*a+2*b)*Real.exp (C*s^2) := by
    have h1 := mul_le_mul_of_nonneg_left hE (by positivity : 0≤4+2*a)
    have h2 := mul_le_mul_of_nonneg_right hd (by positivity : 0≤10+2*b+2*a)
    nlinarith only [h1,h2]
  have hfinal := polynomial_mul_exp_quadratic_le 12 (b:=14+4*a+2*b) (C:=C) (by positivity) hs
  have hpre := mul_le_mul_of_nonneg_right hcoef (by positivity : 0≤u)
  calc
    _ ≤ (14+4*a+2*b)*s^12*Real.exp (C*s^2) := by dsimp [u] at hpre; nlinarith only [hpre]
    _ ≤ _ := by convert hfinal using 1; congr 1; ring

#print axioms quantifiedFilterMatrixHeight_growth

end QuantitativeHolomorphic.Schedule
