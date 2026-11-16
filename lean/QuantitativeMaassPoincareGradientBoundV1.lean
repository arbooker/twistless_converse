module

public import QuantitativeMaassPoincareGradientSumV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Actual hyperbolic gradient covariance for a congruence pullback. -/
theorem upperEnergy_congruence_pullback (N : ℕ) (u : SmoothUpperSeed)
    (g : gamma N) (z : ℍ) :
    (hyperbolicEnergy (u.toFun ∘ integralCuspChart (representative g))
      (u.toFun ∘ integralCuspChart (representative g)) (z.re,z.im)).re=
      (upperEnergy u.toFun u.toFun (g•z)).re := by
  rw [hyperbolicEnergy_integralCuspChart (representative g) u.smooth u.smooth z.im_pos]
  have he := congruence_pullback_cartesian N (hyperbolicEnergy u.toFun u.toFun)
    g (z.re,z.im) z.im_pos
  rw [cartesianLift_positive _ z.im_pos] at he
  exact congrArg Complex.re he.symm

/-- One compact orbit-overlap bound controls the actual periodized gradient. -/
theorem compact_poincare_gradient_square_bound (N : ℕ) (K : Set ℍ) (hK : IsCompact K) :
    ∃ M : ℕ,∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K → ∀ z : ℍ,
      (upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re≤
        (M:ℝ)*∑' g : gamma N,(upperEnergy u.toFun u.toFun (g•z)).re := by
  classical
  obtain ⟨M,hM⟩ := compact_poincare_derivative_sum N K hK
  refine ⟨M,?_⟩
  intro u hu z
  obtain ⟨S,hcard,hd,hout⟩ := hM u hu (z.re,z.im) z.im_pos
  have hcart : cartesianLift (z.re,z.im)=z := by
    rw [cartesianLift_positive _ z.im_pos]
    rfl
  have heout (g : gamma N) (hg : g∉S) : upperEnergy u.toFun u.toFun (g•z)=0 := by
    by_contra hn
    rw [hcart] at hout
    exact hout g hg (hu (upperEnergy_support_right _ _ hn))
  rw [tsum_eq_sum (fun g hg => by rw [heout g hg]; rfl)]
  have hnorm (a : gamma N → ℂ) : ‖∑ g∈S,a g‖^2≤(M:ℝ)*∑ g∈S,‖a g‖^2 := by
    calc
      _ ≤ (∑ g∈S,‖a g‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (S.card:ℝ)*∑ g∈S,‖a g‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  let v := fun g : gamma N => u.toFun ∘ integralCuspChart (representative g)
  change (hyperbolicEnergy _ _ (z.re,z.im)).re≤_
  rw [hyperbolicEnergy_self_eq]
  change z.im^2*(‖dir e₁ (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2+
    ‖dir e₂ (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2)≤_
  rw [hd e₁,hd e₂]
  calc
    _ ≤ z.im^2*((M:ℝ)*(∑ g∈S,‖dir e₁ (v g) (z.re,z.im)‖^2)+
        (M:ℝ)*(∑ g∈S,‖dir e₂ (v g) (z.re,z.im)‖^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hnorm _) (hnorm _)) (sq_nonneg z.im)
    _ = (M:ℝ)*∑ g∈S,(hyperbolicEnergy (v g) (v g) (z.re,z.im)).re := by
      simp only [hyperbolicEnergy_self_eq,X,Y,Finset.sum_add_distrib,←Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl (fun g _ => upperEnergy_congruence_pullback N u g z)

#print axioms upperEnergy_congruence_pullback
#print axioms compact_poincare_gradient_square_bound

end QuantitativeMaass
