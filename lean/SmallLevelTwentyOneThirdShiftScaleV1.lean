module

public import SmallLevelFiniteShiftBlockV1
public import SmallLevelTwentyOneAugmentedRatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelFiniteShift

def jetScale (t : ℂ) (n : Fin 4) : ℂ :=
  I^n.val * (![1,t,t*(t-1),t*(t-1)*(t-2)] : Fin 4 → ℂ) n

theorem jetScale_binomial (t : ℂ) (n : Fin 4) (a : ℕ) (ha : a<n.val) :
    I^(a+1)*Ring.choose (t-(n.val:ℂ)+((a+1:ℕ):ℂ)) (a+1)*jetScale t (lowerIndex n a)=
      jetScale t n / ((a+1).factorial:ℂ) := by
  have ha3 : a≤2 := by omega
  interval_cases a <;> fin_cases n <;> norm_num at ha
  all_goals
      norm_num [jetScale,lowerIndex,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
        descPochhammer_succ_right] <;> ring_nf <;> norm_num [I_sq,map_ofNat] <;> ring

theorem jetScale_ne_zero (m : ℕ) (hm : 2≤m) (n : Fin 4) : jetScale (1-(m:ℂ)) n≠0 := by
  have h1 : 1-(m:ℂ)≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re,one_re,natCast_re,zero_re] at hh
    have hm' : (2:ℝ)≤m := by exact_mod_cast hm
    linarith
  have h3 : 1-(m:ℂ)-2≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    have hm' : (2:ℝ)≤m := by exact_mod_cast hm
    linarith
  have hm0 : m≠0 := by omega
  fin_cases n <;> simp [jetScale,h1,h3,hm0,I_ne_zero]

theorem primeParameter_candidate_lower (p m n : ℕ) (hp : p≠0) :
    primeParameter p m ((m:ℂ)+1-(n:ℂ))=(p:ℂ)/(p:ℂ)^n := by
  unfold primeParameter
  rw [show (m:ℂ)+1-(n:ℂ)-(m:ℂ)=1-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one,Complex.cpow_natCast]

#print axioms jetScale_binomial
#print axioms jetScale_ne_zero
#print axioms primeParameter_candidate_lower
end SmallLevelTwentyOneKnownWords
