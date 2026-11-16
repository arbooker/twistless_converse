module

public import QuantitativeMaassMixedHeckePolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass.MixedExpansion

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) :=
  ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) :=
  ContinuousLinearMap.algebra

structure Term where
  coeff : ℝ
  degree : ℕ
  time : ℝ

abbrev Expression := List Term

def mass : Expression→ℝ
  | [] => 0
  | u::us => |u.coeff|+mass us

def eval (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) : Expression→HeckeWavePair N
  | [] => 0
  | u::us => u.coeff • mixedHeckeSymbol N p hN hpN a b hab u.degree u.time+
      eval N p hN hpN a b hab us

def pair (u v : Term) : Expression :=
  [⟨u.coeff*v.coeff/2,u.degree+v.degree,u.time+v.time⟩,
   ⟨u.coeff*v.coeff/2,u.degree+v.degree,u.time-v.time⟩]

def leftMul (u : Term) : Expression→Expression
  | [] => []
  | v::vs => pair u v++leftMul u vs

def mul : Expression→Expression→Expression
  | [],_ => []
  | u::us,vs => leftMul u vs++mul us vs

def Bounded (m : ℕ) (R : ℝ) (E : Expression) : Prop :=
  ∀ u∈E,u.degree≤m ∧ |u.time|≤R

theorem mass_nonneg (E : Expression) : 0≤mass E := by
  induction E with
  | nil => exact le_rfl
  | cons u us ih => exact add_nonneg (abs_nonneg _) ih

theorem mass_append (E F : Expression) : mass (E++F)=mass E+mass F := by
  induction E with
  | nil => simp only [List.nil_append,mass,zero_add]
  | cons u us ih => simp only [List.cons_append,mass,ih,add_assoc]

theorem mass_pair (u v : Term) : mass (pair u v)=|u.coeff| * |v.coeff| := by
  simp only [pair,mass,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

theorem mass_leftMul (u : Term) (F : Expression) : mass (leftMul u F)=|u.coeff| * mass F := by
  induction F with
  | nil => simp only [leftMul,mass,mul_zero]
  | cons v vs ih => rw [leftMul,mass_append,mass_pair,ih,mass,mul_add]

theorem mass_mul (E F : Expression) : mass (mul E F)=mass E*mass F := by
  induction E with
  | nil => simp only [mul,mass,zero_mul]
  | cons u us ih => rw [mul,mass_append,mass_leftMul,ih,mass,add_mul]

theorem bounded_append {m : ℕ} {R : ℝ} {E F : Expression}
    (hE : Bounded m R E) (hF : Bounded m R F) : Bounded m R (E++F) := by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · exact hE u hu
  · exact hF u hu

theorem bounded_pair {m n : ℕ} {R S : ℝ} (u v : Term)
    (hu : u.degree≤m ∧ |u.time|≤R) (hv : v.degree≤n ∧ |v.time|≤S) :
    Bounded (m+n) (R+S) (pair u v) := by
  intro w hw
  simp only [pair,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · exact ⟨Nat.add_le_add hu.1 hv.1,(abs_add_le _ _).trans (add_le_add hu.2 hv.2)⟩
  · exact ⟨Nat.add_le_add hu.1 hv.1,(abs_sub _ _).trans (add_le_add hu.2 hv.2)⟩

theorem bounded_leftMul {m n : ℕ} {R S : ℝ} (u : Term) (F : Expression)
    (hu : u.degree≤m ∧ |u.time|≤R) (hF : Bounded n S F) :
    Bounded (m+n) (R+S) (leftMul u F) := by
  induction F with
  | nil => intro w hw; exact False.elim (List.not_mem_nil hw)
  | cons v vs ih =>
    apply bounded_append
    · exact bounded_pair u v hu (hF v (List.mem_cons_self))
    · exact ih (fun w hw => hF w (List.mem_cons_of_mem v hw))

theorem bounded_mul {m n : ℕ} {R S : ℝ} (E F : Expression)
    (hE : Bounded m R E) (hF : Bounded n S F) :
    Bounded (m+n) (R+S) (mul E F) := by
  induction E with
  | nil => intro w hw; exact False.elim (List.not_mem_nil hw)
  | cons u us ih =>
    apply bounded_append
    · exact bounded_leftMul u F (hE u List.mem_cons_self) hF
    · exact ih (fun w hw => hE w (List.mem_cons_of_mem u hw))

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

theorem eval_append (E F : Expression) :
    eval N p hN hpN a b hab (E++F)=eval N p hN hpN a b hab E+eval N p hN hpN a b hab F := by
  induction E with
  | nil => simp only [List.nil_append,eval,zero_add]
  | cons u us ih => simp only [List.cons_append,eval,ih,add_assoc]

theorem eval_pair (u v : Term) :
    eval N p hN hpN a b hab (pair u v)=
      (u.coeff • mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)*
      (v.coeff • mixedHeckeSymbol N p hN hpN a b hab v.degree v.time) := by
  rw [smul_mul_smul_comm,mixedHeckeSymbol_mul,smul_smul,smul_add]
  simp only [pair,eval,add_zero,div_eq_mul_inv,one_mul]

theorem eval_leftMul (u : Term) (F : Expression) :
    eval N p hN hpN a b hab (leftMul u F)=
      (u.coeff • mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)*eval N p hN hpN a b hab F := by
  induction F with
  | nil => simp only [leftMul,eval,mul_zero]
  | cons v vs ih => rw [leftMul,eval_append,eval_pair,ih,eval,mul_add]

theorem eval_mul (E F : Expression) :
    eval N p hN hpN a b hab (mul E F)=eval N p hN hpN a b hab E*eval N p hN hpN a b hab F := by
  induction E with
  | nil => simp only [mul,eval,zero_mul]
  | cons u us ih => rw [mul,eval_append,eval_leftMul,ih,eval,add_mul]

#print axioms mass_mul
#print axioms bounded_mul
#print axioms eval_mul
end QuantitativeMaass.MixedExpansion
