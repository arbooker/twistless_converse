module

public import QuantitativeMaassMixedWordExpansionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass.MixedExpansion

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

def one : Expression := [⟨1,0,0⟩]
def scale (c : ℝ) : Expression→Expression
  | [] => []
  | u::us => ⟨c*u.coeff,u.degree,u.time⟩::scale c us
def power (E : Expression) : ℕ→Expression
  | 0 => one
  | n+1 => mul E (power E n)

theorem mass_one : mass one=1 := by norm_num [one,mass]
theorem mass_scale (c : ℝ) (E : Expression) : mass (scale c E)=|c| * mass E := by
  induction E with
  | nil => simp only [scale,mass,mul_zero]
  | cons u us ih => simp only [scale,mass,abs_mul,ih,mul_add]
theorem mass_power (E : Expression) (n : ℕ) : mass (power E n)=(mass E)^n := by
  induction n with
  | zero => rw [power,mass_one,pow_zero]
  | succ n ih => rw [power,mass_mul,ih,pow_succ']

theorem bounded_one : Bounded 0 0 one := by
  intro u hu
  simp only [one,List.mem_singleton] at hu
  subst u
  norm_num
theorem bounded_scale {m : ℕ} {R : ℝ} (c : ℝ) (E : Expression)
    (hE : Bounded m R E) : Bounded m R (scale c E) := by
  induction E with
  | nil => intro u hu; exact False.elim (List.not_mem_nil hu)
  | cons u us ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact hE u List.mem_cons_self
    · exact ih (fun w hw => hE w (List.mem_cons_of_mem u hw)) v hv
theorem bounded_power {m : ℕ} {R : ℝ} (E : Expression) (hE : Bounded m R E) (n : ℕ) :
    Bounded (m*n) ((n:ℝ)*R) (power E n) := by
  induction n with
  | zero => simpa only [Nat.mul_zero,Nat.cast_zero,zero_mul,power] using bounded_one
  | succ n ih =>
    have hh := bounded_mul E (power E n) hE ih
    convert hh using 1 <;> simp only [Nat.mul_succ,Nat.cast_add,Nat.cast_one,power] <;> ring

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

theorem eval_one : eval N p hN hpN a b hab one=1 := by
  simp only [one,eval,one_smul,add_zero]
  apply Prod.ext
  · simp only [mixedHeckeSymbol,pow_zero,mul_one,Wave.shiftedQuotientWave_zero]
    rfl
  · funext z
    simp only [mixedHeckeSymbol,pow_zero,zero_mul,Real.cos_zero,one_mul]
    rfl
theorem eval_scale (c : ℝ) (E : Expression) :
    eval N p hN hpN a b hab (scale c E)=c • eval N p hN hpN a b hab E := by
  induction E with
  | nil => simp only [scale,eval,smul_zero]
  | cons u us ih => simp only [scale,eval,ih,smul_add,smul_smul]
theorem eval_power (E : Expression) (n : ℕ) :
    eval N p hN hpN a b hab (power E n)=(eval N p hN hpN a b hab E)^n := by
  induction n with
  | zero => rw [power,eval_one,pow_zero]
  | succ n ih => rw [power,eval_mul,ih,pow_succ']

#print axioms mass_power
#print axioms bounded_power
#print axioms eval_power
end QuantitativeMaass.MixedExpansion
