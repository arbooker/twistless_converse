module

public import QuantitativeEulerEndpointPolynomialCoefficientGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPolynomialGrowth
open Polynomial

/-- Absorb a fixed nonnegative coefficient on a scale at least one. -/
theorem scaled_exp_le {c a R : ℝ} (hc : 0≤c) (hR : 1≤R) :
    c*Real.exp (a*R)≤Real.exp ((c+a)*R) := by
  have hc' : c≤Real.exp (c*R) := by
    have hcr : c≤c*R := by nlinarith
    linarith [Real.add_one_le_exp (c*R)]
  calc
    c*Real.exp (a*R)≤Real.exp (c*R)*Real.exp (a*R) :=
      mul_le_mul_of_nonneg_right hc' (Real.exp_pos _).le
    _=Real.exp ((c+a)*R) := by rw [←Real.exp_add]; congr 1; ring

def initialBaseConstant (A : ℝ) : ℝ := 547+74*A

theorem initial_parameter_product {A R : ℝ} {J m : ℕ}
    (hJ : (J:ℝ)+1≤Real.exp (A*R)) (hm : (m:ℝ)+1≤Real.exp (A*R)) :
    ((J:ℝ)+1)^5*((m:ℝ)+1)≤Real.exp (6*A*R) := by
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(J:ℝ)+1) hJ 5
  have hh := mul_le_mul hpow hm (by positivity) (by positivity)
  apply hh.trans_eq
  rw [←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  norm_num
  ring

theorem initial_coefficient_double_exp {A R : ℝ} {J m : ℕ}
    (hA : 0≤A) (hR : 1≤R)
    (hJ : (J:ℝ)+1≤Real.exp (A*R)) (hm : (m:ℝ)+1≤Real.exp (A*R)) :
    ((((16*J^5+1)*(2*m):ℕ):ℝ)+1)*((((16*J^5:ℕ):ℝ)+2)*3^(16*J^5))*2^((2*m)*(16*J^5+1))≤
      Real.exp (Real.exp (initialBaseConstant A*R)) := by
  apply (initial_coefficient_bound J m).trans
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul_of_nonneg_left (initial_parameter_product hJ hm) (by norm_num : (0:ℝ)≤119)
  have hs := scaled_exp_le (a:=6*A) (by norm_num : (0:ℝ)≤119) hR
  have hc : (119+6*A)*R≤ initialBaseConstant A*R := by
    unfold initialBaseConstant
    nlinarith
  exact (by nlinarith [ht] : 119*((J:ℝ)+1)^5*((m:ℝ)+1)≤119*Real.exp (6*A*R)).trans
    (hs.trans (Real.exp_le_exp.mpr hc))

/-- The exact matrix height of the initial corner polynomial has the same
common double-exponential envelope as its coefficient mass. -/
theorem initial_matrix_double_exp {A R h : ℝ} {J m d : ℕ}
    (hA : 0≤A) (hR : 1≤R) (hh0 : 0≤h)
    (hJ : (J:ℝ)+1≤Real.exp (A*R)) (hm : (m:ℝ)+1≤Real.exp (A*R))
    (hh : h≤Real.exp (A*R)) (hd : d≤(16*J^5+1)*(2*m)) :
    2*(2*max 1 (8*h^2))^d≤Real.exp (Real.exp (initialBaseConstant A*R)) := by
  have hR0 : 0≤R := by linarith
  have he1 : 1≤Real.exp (2*A*R) := Real.one_le_exp_iff.mpr (by positivity)
  have hh2 : h^2≤Real.exp (2*A*R) := by
    have hv := pow_le_pow_left₀ hh0 hh 2
    apply hv.trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hmax : max 1 (8*h^2)≤8*Real.exp (2*A*R) := max_le (by linarith) (by linarith)
  have hbase : 2*max 1 (8*h^2)≤Real.exp ((16+2*A)*R) := by
    have hs := scaled_exp_le (a:=2*A) (by norm_num : (0:ℝ)≤16) hR
    nlinarith [hs]
  have hd' : (d:ℝ)≤34*Real.exp (6*A*R) := by
    have hdc : (d:ℝ)≤(((16*J^5+1)*(2*m):ℕ):ℝ) := by exact_mod_cast hd
    have ht := mul_le_mul_of_nonneg_left (initial_parameter_product hJ hm) (by norm_num : (0:ℝ)≤34)
    nlinarith [initial_degree_bound J m]
  have hp : (2*max 1 (8*h^2))^d≤Real.exp ((d:ℝ)*((16+2*A)*R)) := by
    simpa only [←Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hbase d
  have h2 : (2:ℝ)≤Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hp2 := mul_le_mul h2 hp (by positivity) (Real.exp_pos 2).le
  rw [←Real.exp_add] at hp2
  apply hp2.trans
  apply Real.exp_le_exp.mpr
  have hRe : R≤Real.exp R := by linarith [Real.add_one_le_exp R]
  have hproduct : Real.exp (6*A*R)*R≤Real.exp ((6*A+1)*R) := by
    calc
      Real.exp (6*A*R)*R≤Real.exp (6*A*R)*Real.exp R :=
        mul_le_mul_of_nonneg_left hRe (Real.exp_pos _).le
      _=Real.exp ((6*A+1)*R) := by rw [←Real.exp_add]; congr 1; ring
  have hde := mul_le_mul_of_nonneg_right hd' (show 0≤(16+2*A)*R by positivity)
  have hpe := mul_le_mul_of_nonneg_left hproduct (show 0≤34*(16+2*A) by positivity)
  have he : 1≤Real.exp ((6*A+1)*R) := Real.one_le_exp_iff.mpr (by positivity)
  have hsum : 2+(d:ℝ)*((16+2*A)*R)≤(2+34*(16+2*A))*Real.exp ((6*A+1)*R) := by
    nlinarith only [hde,hpe,he]
  have hs := scaled_exp_le (a:=6*A+1) (show 0≤2+34*(16+2*A) by positivity) hR
  apply hsum.trans (hs.trans_eq _)
  congr 1
  unfold initialBaseConstant
  ring

theorem sharpening_coefficient_double_exp {A R : ℝ} {J : ℕ}
    (hA : 0≤A) (hR : 1≤R) (hJ : (J:ℝ)+1≤Real.exp (A*R)) :
    ((((16*J^5:ℕ):ℝ)+2)*3^(16*J^5))≤Real.exp (Real.exp (initialBaseConstant A*R)) := by
  have hc := coefficient_envelope 0 (16*J^5)
  simp only [Nat.cast_zero,zero_add,one_mul,mul_zero,pow_zero,mul_one] at hc
  apply hc.trans
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(J:ℝ)+1) hJ 5
  have hp' : ((J:ℝ)+1)^5≤Real.exp (5*A*R) := by
    apply hp.trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hJ5 : (J:ℝ)^5≤((J:ℝ)+1)^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  have h1 : (1:ℝ)≤((J:ℝ)+1)^5 := one_le_pow₀ (by have h := Nat.cast_nonneg (α:=ℝ) J; linarith)
  have hsmall : 3*((16*J^5:ℕ):ℝ)+1≤49*Real.exp (5*A*R) := by
    push_cast
    linarith
  have hs := scaled_exp_le (a:=5*A) (by norm_num : (0:ℝ)≤49) hR
  have hlarge : (49+5*A)*R≤ initialBaseConstant A*R := by unfold initialBaseConstant; nlinarith
  exact hsmall.trans (hs.trans (Real.exp_le_exp.mpr hlarge))

#print axioms initial_coefficient_double_exp
#print axioms initial_matrix_double_exp
#print axioms sharpening_coefficient_double_exp
end QuantitativeEulerEndpointPolynomialGrowth
