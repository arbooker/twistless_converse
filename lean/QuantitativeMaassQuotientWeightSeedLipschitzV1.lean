module

public import QuantitativeMaassUpperSeedSmoothExtensionV1
public import QuantitativeMaassQuotientWeightExtensionV1
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane

namespace QuantitativeMaass
open MaassDifferential

theorem bounded_complex_product_lipschitz {K L B C : NNReal}
    {f g : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hB : ∀ x,‖f x‖≤B) (hC : ∀ x,‖g x‖≤C) :
    LipschitzWith (B*L+C*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖f x*g x-f y*g y‖≤((B:ℝ)*L+(C:ℝ)*K)*dist x y
  calc
    _ = ‖f x*(g x-g y)+(f x-f y)*g y‖ := by congr 1; ring
    _ ≤ ‖f x*(g x-g y)‖+‖(f x-f y)*g y‖ := norm_add_le _ _
    _ = ‖f x‖*‖g x-g y‖+‖f x-f y‖*‖g y‖ := by rw [norm_mul,norm_mul]
    _ ≤ (B:ℝ)*((L:ℝ)*dist x y)+((K:ℝ)*dist x y)*(C:ℝ) :=
      add_le_add (mul_le_mul (hB x) (hg.norm_sub_le x y) (norm_nonneg _) B.coe_nonneg)
        (mul_le_mul (hf.norm_sub_le x y) (hC y) (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- Multiplying any actual smooth compact seed by the literal orbit weight
produces a globally Lipschitz coordinate seed after zero extension. -/
theorem quotientWeight_seed_lipschitz (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (u : SmoothUpperSeed) :
    ∃ K : NNReal,LipschitzWith K (fun Z => (quotientWeightPlane N ε v Z:ℂ)*
      upperSeedExtension (upperFunction u.toFun) Z) := by
  let f := upperSeedExtension (upperFunction u.toFun)
  have hc : HasCompactSupport f := upperSeedExtension_compact _ u.compact
  have hs := upperSeedExtension_smooth u
  obtain ⟨r,hr,hrK⟩ := hc.isCompact.exists_forall_le' continuous_snd.continuousOn
    (upperSeedExtension_support_positive _ u.compact)
  obtain ⟨Kb,b,hb,hbound,he⟩ := quotientWeight_bounded_extension N hε hv (half_pos hr)
  obtain ⟨Ku,hu⟩ := upperSeedExtension_lipschitz u
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hs.continuous
  let B : NNReal := ⟨quotientWeightBound ε,quotientWeightBound_nonneg ε⟩
  let D : NNReal := ⟨|C|,abs_nonneg C⟩
  have hb' : LipschitzWith Kb (fun Z => (b Z:ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hb.dist_le_mul x y
  have hbf (Z : ℝ×ℝ) : ‖(b Z:ℂ)‖≤B := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hbound Z).1]
    exact (hbound Z).2
  have huf (Z : ℝ×ℝ) : ‖f Z‖≤D := (hC Z).trans (le_abs_self C)
  have heq : (fun Z => (quotientWeightPlane N ε v Z:ℂ)*f Z)=
      (fun Z => (b Z:ℂ)*f Z) := by
    funext Z
    by_cases hz : f Z=0
    · simp only [hz,mul_zero]
    · have hp := hrK Z (subset_tsupport f hz)
      rw [he (by dsimp; linarith)]
  refine ⟨B*Ku+D*Kb,?_⟩
  change LipschitzWith (B*Ku+D*Kb) (fun Z => (quotientWeightPlane N ε v Z:ℂ)*f Z)
  rw [heq]
  exact bounded_complex_product_lipschitz hb' hu hbf huf

#print axioms bounded_complex_product_lipschitz
#print axioms quotientWeight_seed_lipschitz

end QuantitativeMaass
