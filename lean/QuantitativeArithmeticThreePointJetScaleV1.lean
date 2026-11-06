module
public import SmallLevelTwentyOneThirdShiftScaleV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticThreePointJetScale
open Complex SmallLevelFiniteShift

def scale (β : ℂ) (n : Fin 3) : ℂ := SmallLevelTwentyOneKnownWords.jetScale β ⟨n.val,by omega⟩

theorem scale_binomial (β : ℂ) (n : Fin 3) (a : ℕ) (ha : a<n.val) :
    I^(a+1)*Ring.choose (β-(n.val:ℂ)+((a+1:ℕ):ℂ)) (a+1)*scale β (lowerIndex n a)=
      scale β n/((a+1).factorial:ℂ) := by
  exact SmallLevelTwentyOneKnownWords.jetScale_binomial β ⟨n.val,by omega⟩ a ha

theorem scale_ne_zero (β : ℂ) (h0 : β≠0) (h1 : β-1≠0) (n : Fin 3) : scale β n≠0 := by
  fin_cases n <;> simp [scale,SmallLevelTwentyOneKnownWords.jetScale,I_ne_zero,h0,h1]

def normalize (β : ℂ) (v : Fin 3 × Fin 1050 → ℂ) (j : Fin 3 × Fin 1050) : ℂ :=
  (scale β j.1)⁻¹*v j

theorem normalize_cancel (β : ℂ) (h0 : β≠0) (h1 : β-1≠0) (v : Fin 3 × Fin 1050 → ℂ) (n : Fin 3) :
    scale β n • (fun j => normalize β v (n,j))=(fun j => v (n,j)) := by
  funext j
  simp [normalize,Pi.smul_apply,smul_eq_mul,scale_ne_zero β h0 h1 n]

theorem normalize_top (β : ℂ) (v : Fin 3 × Fin 1050 → ℂ) (j : Fin 1050) : normalize β v (0,j)=v (0,j) := by
  simp [normalize,scale,SmallLevelTwentyOneKnownWords.jetScale]

#print axioms scale_binomial
#print axioms normalize_cancel
end QuantitativeArithmeticThreePointJetScale
