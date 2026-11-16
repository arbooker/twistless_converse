module

public import QuantitativeMaassCyclicPowerFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [Ring 𝔄]

/-- A polynomial with no ambient identity term after sandwiching. This
recurrence permits trace transport out of an infinite ambient space into
the finite terminal corner. -/
def powerSandwichCoefficient (F G : 𝔄) : ℕ→𝔄
  | 0 => 0
  | n+1 => powerSandwichCoefficient F G n+F-powerSandwichCoefficient F G n*G*F

theorem powerSandwichCoefficient_mul (F G : 𝔄) (m : ℕ) :
    powerSandwichCoefficient F G m*G=1-(1-F*G)^m := by
  induction m with
  | zero => simp [powerSandwichCoefficient]
  | succ m ih =>
    rw [powerSandwichCoefficient,pow_succ]
    calc
      _ = (powerSandwichCoefficient F G m*G)+F*G-
          (powerSandwichCoefficient F G m*G)*(F*G) := by noncomm_ring
      _ = _ := by rw [ih]; noncomm_ring

/-- The identity is required only in the target algebra; the map from the
terminal corner may be nonunital. -/
theorem powerSandwichCoefficient_rep {𝔅 : Type*} [Ring 𝔅]
    (r : 𝔄→ₙ+*𝔅) (F G : 𝔄) (W V : 𝔅) (hG : r G=V*W) (m : ℕ) :
    W*r (powerSandwichCoefficient F G m)*V=1-(1-W*r F*V)^m := by
  induction m with
  | zero => simp [powerSandwichCoefficient]
  | succ m ih =>
    rw [powerSandwichCoefficient,map_sub,map_add,map_mul,map_mul,hG,pow_succ]
    calc
      _ = (W*r (powerSandwichCoefficient F G m)*V)+(W*r F*V)-
          (W*r (powerSandwichCoefficient F G m)*V)*(W*r F*V) := by noncomm_ring
      _ = _ := by rw [ih]; noncomm_ring

#print axioms powerSandwichCoefficient_mul
#print axioms powerSandwichCoefficient_rep
end QuantitativeMaass
