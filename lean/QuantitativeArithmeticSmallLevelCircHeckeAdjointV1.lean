module

public import QuantitativeArithmeticSmallLevelCircPrimeFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm

/-- Global Fricke exchanges the two diagonal correspondences, including
ramified primes, on the full modular space. -/
theorem dilationTrace_fricke_upper (N p : ℕ) [NeZero N]
    (hN : 0 < N) (hp : 0 < p) (k : ℤ) (f : ModularForm (level N) k) :
    dilationTrace N p hp k (frickeOperator N hN k f) =
      frickeOperator N hN k (upperTrace N p hp k f) := by
  let g : ModularForm (level N) k := ModularForm.mcast rfl
    (ModularForm.translate f (frickeReal N hN)) (fricke_inverse_normalizes N hN).symm
  have hg : (g : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] frickeReal N hN := rfl
  have he := translateTrace_intertwine k (frickeReal N hN) (dilationReal p hp)
    (upperDilationReal p hp) (fricke_inverse_normalizes N hN)
    (fricke_dilation_upper N p hN hp) f g hg
  rw [← dilationTrace_eq_translateTrace N p hp k] at he
  have hu : translateTrace (level N) k (upperDilationReal p hp) f = upperTrace N p hp k f := rfl
  rw [hu] at he
  have hf : frickeOperator N hN k f = (N : ℂ)^(1-(k : ℂ)/2) • g := rfl
  rw [hf, map_smul]
  apply DFunLike.coe_injective
  change (N : ℂ)^(1-(k : ℂ)/2) • (dilationTrace N p hp k g : ℍ → ℂ) =
    (N : ℂ)^(1-(k : ℂ)/2) • ((upperTrace N p hp k f : ℍ → ℂ) ∣[k] frickeReal N hN)
  rw [he]

theorem frickeOperator_involutive (N k : ℕ) (hN : 0 < N) (hk : Even k) :
    Function.Involutive (frickeOperator N hN (k : ℤ)) := by
  intro f
  apply DFunLike.coe_injective
  rw [frickeOperator_coe, frickeOperator_coe, fricke_slash_involutive N hN k hk]

end QuantitativeArithmeticSmallLevelCirc.ModularHecke

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp

/-- On Mcirc even the ramified upper and lower Hecke correspondences
coincide. This derives their equality from the two genuine trace kernels. -/
theorem dilationTrace_eq_primeHecke (N p k : ℕ) [NeZero N] (hN : 0 < N)
    (hp : p.Prime) (hk : Even k) (F : ModularForm (level N) (k : ℤ))
    (hF : F ∈ space N hN k) :
    ModularHecke.dilationTrace N p hp.pos (k : ℤ) F =
      ModularHecke.primeHecke N p hp (k : ℤ) F := by
  by_cases hpN : p ∣ N
  · have hc := primeHecke_fricke_circ N k hN hk F hF p hp
    simp only [ModularHecke.primeHecke, hpN, ite_true] at hc ⊢
    have hh := ModularHecke.dilationTrace_fricke_upper N p hN hp.pos (k : ℤ)
      (ModularHecke.frickeOperator N hN (k : ℤ) F)
    rw [ModularHecke.frickeOperator_involutive N k hN hk F, hc,
      ModularHecke.frickeOperator_involutive N k hN hk] at hh
    exact hh
  · simp only [ModularHecke.primeHecke, hpN, ite_false]

#print axioms ModularHecke.dilationTrace_fricke_upper
#print axioms ModularHecke.frickeOperator_involutive
#print axioms dilationTrace_eq_primeHecke
end QuantitativeArithmeticSmallLevelCirc
