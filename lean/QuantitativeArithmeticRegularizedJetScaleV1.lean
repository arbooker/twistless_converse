module
public import SmallLevelRegularizedShiftBlockV1
public import SmallLevelTwentyOneThirdShiftScaleV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRegularizedJetScale
open Complex SmallLevelFiniteShift
/- Elementary scalar identities isolated from the level-21 row certificates.
   The formulas and proofs follow SmallLevelTwentyOneRegularizedTaylorV1. -/
def weightOneChooseQuot (n : Fin 4) (z : ℂ) : ℂ :=
  (![0,1,(z-3)/2,(z-3)*(z-4)/6] : Fin 4 → ℂ) n

theorem weightOneChoose_factor (n : Fin 4) (hn : n≠0) (z : ℂ) :
    Ring.choose (z-2) n.val=(z-2)*weightOneChooseQuot n z := by
  fin_cases n <;> norm_num at hn
  all_goals
    norm_num [weightOneChooseQuot,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right] <;> ring_nf <;> norm_num [map_ofNat] <;> ring

def regularizedJetScale (n : Fin 4) : ℂ := (![1,I,-I^2,2*I^3] : Fin 4 → ℂ) n

theorem regularizedJetScale_ne_zero (n : Fin 4) : regularizedJetScale n≠0 := by
  fin_cases n <;> norm_num [regularizedJetScale,I_sq,I_ne_zero,pow_succ]

theorem regularizedJetScale_top (n : Fin 4) (hn : n≠0) :
    I^n.val*weightOneChooseQuot n 2=regularizedJetScale n/(n.val.factorial:ℂ) := by
  fin_cases n <;> norm_num at hn
  all_goals norm_num [weightOneChooseQuot,regularizedJetScale,I_sq,pow_succ] <;> ring

theorem regularizedJetScale_lower (n : Fin 4) (a : ℕ) (ha : a<n.val-1) :
    I^(a+1)*Ring.choose (-((n.val:ℂ))+((a+1:ℕ):ℂ)) (a+1)*
      regularizedJetScale (lowerIndex n a)=regularizedJetScale n/((a+1).factorial:ℂ) := by
  have ha2 : a≤1 := by omega
  interval_cases a <;> fin_cases n <;> norm_num at ha
  all_goals norm_num [regularizedJetScale,lowerIndex,Ring.choose_eq_smul,
    ← Polynomial.aeval_eq_smeval,descPochhammer_succ_right,I_sq,pow_succ] <;> ring

#print axioms weightOneChoose_factor
#print axioms regularizedJetScale_ne_zero
#print axioms regularizedJetScale_top
#print axioms regularizedJetScale_lower
end QuantitativeArithmeticRegularizedJetScale
