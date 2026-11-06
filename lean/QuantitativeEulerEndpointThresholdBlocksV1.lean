module

public import QuantitativeEulerEndpointProductV1
public import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointThresholdBlocks
open Finset

/-- Abstract prefix data, instantiated below by the ACTUAL prepared-prime
Euler products. The one-step lower bound controls threshold overshoot. -/
structure Prefix where
  value : ℕ → ℝ
  zero : value 0=1
  antitone : Antitone value
  step : ∀ n, value n*(1-1/((n:ℝ)+2))≤value (n+1)
  constant : ℝ
  constant_pos : 0<constant
  upper : ∀ n, value n≤constant/Real.log ((n:ℝ)+2)

namespace Prefix
variable (P : Prefix)

theorem lower (n : ℕ) : 1/((n:ℝ)+1)≤P.value n := by
  induction n with
  | zero => simp [P.zero]
  | succ n ih =>
    have hd : 0<(n:ℝ)+1 := by positivity
    have hd2 : 0<(n:ℝ)+2 := by positivity
    have hf : 0≤1-1/((n:ℝ)+2) := by
      have hh := (div_le_one hd2).mpr (show 1≤(n:ℝ)+2 by linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)])
      linarith
    have hh := (mul_le_mul_of_nonneg_right ih hf).trans (P.step n)
    have he : 1/((n:ℝ)+1)*(1-1/((n:ℝ)+2))=1/((n:ℝ)+2) := by field_simp; ring
    rw [he] at hh
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hh

theorem positive (n : ℕ) : 0<P.value n := (by positivity : (0:ℝ)<1/((n:ℝ)+1)).trans_le (P.lower n)

def cap (j : ℕ) : ℕ := ⌈Real.exp (P.constant*(4:ℝ)^j)⌉₊

theorem cap_meets (j : ℕ) : P.value (P.cap j)≤1/(4:ℝ)^j := by
  have hc : Real.exp (P.constant*(4:ℝ)^j)≤(P.cap j:ℝ) := Nat.le_ceil _
  have hlog : 0<Real.log ((P.cap j:ℝ)+2) := Real.log_pos (by linarith [(Nat.cast_nonneg (P.cap j) : (0:ℝ)≤P.cap j)])
  have hcost : P.constant*(4:ℝ)^j≤Real.log ((P.cap j:ℝ)+2) := by
    have hh := Real.log_le_log (Real.exp_pos (P.constant*(4:ℝ)^j)) (hc.trans (show (P.cap j:ℝ)≤(P.cap j:ℝ)+2 by linarith))
    simpa only [Real.log_exp] using hh
  apply (P.upper _).trans
  apply (div_le_iff₀ hlog).mpr
  have hh := mul_le_mul_of_nonneg_left hcost (show 0≤1/(4:ℝ)^j by positivity)
  have he : (1/(4:ℝ)^j)*(P.constant*(4:ℝ)^j)=P.constant := by field_simp
  rw [he] at hh
  exact hh

theorem exists_cutoff (j : ℕ) : ∃ n, P.value n≤1/(4:ℝ)^j := ⟨P.cap j,P.cap_meets j⟩

def cutoff (j : ℕ) : ℕ := Nat.find (P.exists_cutoff j)

theorem cutoff_hits (j : ℕ) : P.value (P.cutoff j)≤1/(4:ℝ)^j := Nat.find_spec (P.exists_cutoff j)

theorem cutoff_le_cap (j : ℕ) : P.cutoff j≤P.cap j := Nat.find_min' _ (P.cap_meets j)

theorem cutoff_before (j m : ℕ) (hm : m<P.cutoff j) : 1/(4:ℝ)^j<P.value m :=
  lt_of_not_ge (Nat.find_min (P.exists_cutoff j) hm)

theorem cutoff_zero : P.cutoff 0=0 := by
  apply (Nat.find_eq_zero _).mpr
  simp [P.zero]

theorem cutoff_mono : Monotone P.cutoff := by
  intro i j hij
  apply Nat.find_min'
  exact (P.cutoff_hits j).trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij))

theorem cutoff_reciprocal (j : ℕ) : 1/((P.cutoff j:ℝ)+1)≤1/(4:ℝ)^j :=
  (P.lower _).trans (P.cutoff_hits j)

theorem cutoff_pos (j : ℕ) (hj : 0<j) : 0<P.cutoff j := by
  by_contra hh
  have hz : P.cutoff j=0 := by omega
  have h := P.cutoff_hits j
  rw [hz,P.zero] at h
  have hp : 1<(4:ℝ)^j := one_lt_pow₀ (by norm_num) (by omega)
  have hi : 1/(4:ℝ)^j<1 := (div_lt_one (by positivity)).mpr hp
  linarith

/-- A single threshold crossing loses at most a geometrically small
factor. It is not charged a fixed constant for every block. -/
theorem cutoff_mass_lower (j : ℕ) (hj : 0<j) :
    (1/(4:ℝ)^j)*(1-1/(4:ℝ)^j)≤P.value (P.cutoff j) := by
  let a := P.cutoff j
  have ha : 0<a := P.cutoff_pos j hj
  have hprev := (P.cutoff_before j (a-1) (by dsimp only [a]; omega)).le
  have hstep := P.step (a-1)
  have he : a-1+1=a := by omega
  rw [he] at hstep
  have hden : ((a-1:ℕ):ℝ)+2=(a:ℝ)+1 := by exact_mod_cast (show a-1+2=a+1 by omega)
  rw [hden] at hstep
  have hrecip : 1/((a:ℝ)+1)≤1/(4:ℝ)^j := P.cutoff_reciprocal j
  have hinv : 1/(4:ℝ)^j≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hf : 0≤1-1/((a:ℝ)+1) := by linarith
  calc
    _ ≤ (1/(4:ℝ)^j)*(1-1/((a:ℝ)+1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ P.value (a-1)*(1-1/((a:ℝ)+1)) := mul_le_mul_of_nonneg_right hprev hf
    _ ≤ _ := hstep

theorem inverse_loss_exp {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) :
    1≤Real.exp (2*x)*(1-x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*x)) (show 0≤1-x by linarith)
  nlinarith [mul_nonneg hx (show 0≤1/2-x by linarith)]

/-- Consecutive absolute-threshold blocks contract by1/4 with a summable
rounding loss2/4^j. The actual bad-prime loss enters only through P.constant. -/
theorem block_ratio (j : ℕ) :
    P.value (P.cutoff (j+1))/P.value (P.cutoff j)≤Real.exp (2/(4:ℝ)^j)/4 := by
  by_cases hj : j=0
  · subst j
    rw [P.cutoff_zero,P.zero,div_one]
    have h := P.cutoff_hits 1
    have he : (1:ℝ)≤Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
    norm_num at h ⊢
    linarith
  · have hjp : 0<j := by omega
    have hlo := P.cutoff_mass_lower j hjp
    have hhi := P.cutoff_hits (j+1)
    have hx : 0≤1/(4:ℝ)^j := by positivity
    have hx1 : 1/(4:ℝ)^j≤1/2 := by
      have hp : (4:ℝ)≤4^j := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) hjp
      apply (div_le_iff₀ (by positivity : 0<(4:ℝ)^j)).mpr
      linarith
    have he := inverse_loss_exp hx hx1
    have hm := mul_le_mul_of_nonneg_left hlo (show 0≤Real.exp (2/(4:ℝ)^j)/4 by positivity)
    have hxmul := mul_le_mul_of_nonneg_left he (show 0≤(1/(4:ℝ)^j)/4 by positivity)
    apply (div_le_iff₀ (P.positive _)).mpr
    have hex : 2*(1/(4:ℝ)^j)=2/(4:ℝ)^j := by ring
    rw [hex] at hxmul
    have hpow : 1/(4:ℝ)^(j+1)=(1/(4:ℝ)^j)/4 := by rw [pow_succ]; field_simp
    rw [hpow] at hhi
    nlinarith only [hm,hxmul,hhi]

theorem cutoff_size (j : ℕ) : (P.cutoff j:ℝ)+1≤3*Real.exp (P.constant*(4:ℝ)^j) := by
  have hc : (P.cutoff j:ℝ)≤(P.cap j:ℝ) := by exact_mod_cast P.cutoff_le_cap j
  have he := Nat.ceil_lt_add_one (Real.exp_pos (P.constant*(4:ℝ)^j)).le
  have hone : 1≤Real.exp (P.constant*(4:ℝ)^j) := Real.one_le_exp_iff.mpr (mul_nonneg P.constant_pos.le (by positivity))
  change (P.cap j:ℝ)<Real.exp (P.constant*(4:ℝ)^j)+1 at he
  linarith

#print axioms lower
#print axioms cap_meets
#print axioms cutoff_mass_lower
#print axioms block_ratio
#print axioms cutoff_size
end Prefix
end QuantitativeEulerEndpointThresholdBlocks
