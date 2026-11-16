module

public import QuantitativeMaassLVFiniteExpansionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass.MixedExpansion
local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

theorem eval_mem (E : Expression) :
    eval N p hN hpN a b hab E∈mixedHeckeSpan N p hN hpN a b hab := by
  induction E with
  | nil => exact Submodule.zero_mem _
  | cons u us ih =>
    exact Submodule.add_mem _ (Submodule.smul_mem _ _
      (mixedHeckeSymbol_mem N p hN hpN a b hab u.degree u.time)) ih

/-- A monomial estimate extends with the proved coefficient mass of the
same finite expansion. Linearity is required only on the actual mixed span. -/
theorem eval_functional_bound (f : HeckeWavePair N→ℝ) (h0 : f 0=0)
    (hadd : ∀ u∈mixedHeckeSpan N p hN hpN a b hab,
      ∀ v∈mixedHeckeSpan N p hN hpN a b hab,f (u+v)=f u+f v)
    (hsmul : ∀ c : ℝ,∀ u∈mixedHeckeSpan N p hN hpN a b hab,f (c • u)=c*f u)
    (E : Expression) (B : ℝ)
    (hB : ∀ u∈E,|f (mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)|≤B) :
    |f (eval N p hN hpN a b hab E)|≤mass E*B := by
  induction E with
  | nil => simp only [eval,h0,abs_zero,mass,zero_mul,le_refl]
  | cons u us ih =>
    have hu := mixedHeckeSymbol_mem N p hN hpN a b hab u.degree u.time
    have he := eval_mem N p hN hpN a b hab us
    rw [eval,hadd _ (Submodule.smul_mem _ _ hu) _ he,hsmul _ _ hu]
    calc
      _ ≤ |u.coeff| * |f (mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)|+
          |f (eval N p hN hpN a b hab us)| := by
        simpa only [abs_mul] using abs_add_le
          (u.coeff*f (mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)) (f (eval N p hN hpN a b hab us))
      _ ≤ |u.coeff| * B+mass us*B := add_le_add
        (mul_le_mul_of_nonneg_left (hB u List.mem_cons_self) (abs_nonneg _))
        (ih (fun v hv => hB v (List.mem_cons_of_mem u hv)))
      _ = _ := by rw [mass,add_mul]

#print axioms eval_mem
#print axioms eval_functional_bound
end QuantitativeMaass.MixedExpansion
