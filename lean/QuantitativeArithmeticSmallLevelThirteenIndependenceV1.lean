module

public import QuantitativeArithmeticSmallLevelThirteenAnalyticV1
public import Mathlib.NumberTheory.Niven

set_option autoImplicit false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Polynomial

def unit13 : ℝ := (3+Real.sqrt 13)/2
def scaleA : ℝ := (17+4*Real.sqrt 13)/9
def scaleB : ℝ := (7-Real.sqrt 13)/6

private theorem integral_zpow_of_unit {u : ℝ}
    (hu : IsIntegral ℤ u) (hi : IsIntegral ℤ u⁻¹) (n : ℤ) : IsIntegral ℤ (u^n) := by
  cases n with
  | ofNat n => simpa using hu.pow n
  | negSucc n => simpa only [zpow_negSucc,inv_pow] using hi.pow (n+1)

private theorem integral_and_inv_of_zpow {b : ℝ} {r : ℤ} (hr : r≠0)
    (h1 : IsIntegral ℤ (b^r)) (h2 : IsIntegral ℤ (b^(-r))) :
    IsIntegral ℤ b ∧ IsIntegral ℤ b⁻¹ := by
  cases r with
  | ofNat n =>
      have hn : 0<n := by
        apply Nat.pos_of_ne_zero
        intro hn
        apply hr
        simp [hn]
      constructor
      · apply IsIntegral.of_pow hn
        simpa only [Int.ofNat_eq_natCast,zpow_natCast] using h1
      · apply IsIntegral.of_pow hn
        simpa only [Int.ofNat_eq_natCast,zpow_neg,zpow_natCast,inv_pow] using h2
  | negSucc n =>
      constructor
      · apply IsIntegral.of_pow (Nat.succ_pos n)
        simpa only [Int.neg_negSucc,zpow_natCast] using h2
      · apply IsIntegral.of_pow (Nat.succ_pos n)
        simpa only [zpow_negSucc,inv_pow] using h1

theorem unit13_integral : IsIntegral ℤ unit13 := by
  refine ⟨X^2-(C 3*X+C 1),?_,?_⟩
  · apply monic_X_pow_sub
    compute_degree
    norm_num
  · simp only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_add,eval₂_mul,eval₂_C]
    have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
    dsimp [unit13]
    nlinarith

theorem unit13_inv : unit13⁻¹=unit13-3 := by
  have hu : unit13≠0 := by dsimp [unit13]; positivity
  apply mul_left_cancel₀ hu
  rw [mul_inv_cancel₀ hu]
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  dsimp [unit13]
  nlinarith

theorem scaleB_pos : 0<scaleB := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hr := Real.sqrt_nonneg (13:ℝ)
  dsimp [scaleB]
  nlinarith

theorem scaleA_pos : 0<scaleA := by dsimp [scaleA]; positivity

theorem scale_relation : scaleA=unit13^2*scaleB^2 := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hu : unit13*scaleB=(2+Real.sqrt 13)/3 := by
    dsimp [unit13,scaleB]
    nlinarith
  rw [← mul_pow,hu]
  dsimp [scaleA]
  nlinarith

theorem scaleB_trace : scaleB+scaleB⁻¹=(7/3:ℝ) := by
  have hb : scaleB≠0 := scaleB_pos.ne'
  apply mul_right_cancel₀ hb
  rw [add_mul,inv_mul_cancel₀ hb]
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  dsimp [scaleB]
  nlinarith

/-- The two positive hyperbolic eigenvalues are multiplicatively independent.
The proof uses only integrality of a quadratic unit and the nonintegral
rational trace 7/3; no Diophantine approximation or p-adic library is needed. -/
theorem scales_independent (m n : ℤ) (he : scaleA^m*scaleB^n=1) : m=0 ∧ n=0 := by
  have hu0 : unit13≠0 := by dsimp [unit13]; positivity
  have hb0 : scaleB≠0 := scaleB_pos.ne'
  have hi : IsIntegral ℤ unit13⁻¹ := by
    rw [unit13_inv]
    exact unit13_integral.sub (isIntegral_intCast 3)
  have hp (r : ℤ) : IsIntegral ℤ (unit13^r) := integral_zpow_of_unit unit13_integral hi r
  have he' : unit13^(2*m)*scaleB^(2*m+n)=1 := by
    rw [scale_relation,mul_zpow,← zpow_natCast,← zpow_mul,← zpow_natCast,← zpow_mul] at he
    rw [mul_assoc,← zpow_add₀ hb0] at he
    exact he
  have hb : scaleB^(2*m+n)=unit13^(-(2*m)) := by
    apply mul_left_cancel₀ (zpow_ne_zero _ hu0)
    rw [he',← zpow_add₀ hu0]
    simp
  have hbi : scaleB^(-(2*m+n))=unit13^(2*m) := by
    have hh := congrArg Inv.inv hb
    simpa only [← zpow_neg,neg_neg] using hh
  have hr : 2*m+n=0 := by
    by_contra hn
    have h1 : IsIntegral ℤ (scaleB^(2*m+n)) := hb ▸ hp (-(2*m))
    have h2 : IsIntegral ℤ (scaleB^(-(2*m+n))) := hbi ▸ hp (2*m)
    obtain ⟨hB,hBi⟩ := integral_and_inv_of_zpow hn h1 h2
    have ht := hB.add hBi
    obtain ⟨j,hj⟩ := ht.exists_int_iff_exists_rat.mp
      ⟨(7/3:ℚ),by simpa using scaleB_trace⟩
    have hh : (7/3:ℝ)=(j:ℝ) := scaleB_trace.symm.trans hj
    have hj3 : (3:ℝ)*j=7 := by linarith
    have hjZ : (3:ℤ)*j=7 := by exact_mod_cast hj3
    omega
  rw [hr,zpow_zero,mul_one] at he'
  have hu : 1<unit13 := by dsimp [unit13]; have := Real.sqrt_nonneg (13:ℝ); linarith
  have hm := (zpow_eq_one_iff_right₀ (by linarith : 0≤unit13) (ne_of_gt hu)).mp he'
  constructor <;> omega

theorem irrational_scale_logs : Irrational (Real.log scaleA/Real.log scaleB) :=
  irrational_log_ratio_of_independent scaleA_pos scaleB_pos scales_independent

#print axioms scales_independent
#print axioms irrational_scale_logs
end QuantitativeArithmeticSmallLevelThirteen
