module

public import QuantitativeMaassParabolicLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- The actual congruence element for each admissible integer cusp translation. -/
def cuspParabolicElement (N : ℕ) (A : SL(2,ℤ))
    (n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2}) : gamma N :=
  ⟨integralLabel (cuspParabolicMatrix A n.val),(cuspParabolicMatrix_mem_iff N A n.val).mpr n.property⟩

theorem cuspParabolicElement_injective (N : ℕ) (A : SL(2,ℤ)) :
    Function.Injective (cuspParabolicElement N A) := by
  intro n m he
  apply Subtype.ext
  exact cuspParabolicMatrix_label_injective A (congrArg Subtype.val he)

theorem cuspParabolicElement_action (N : ℕ) (A : SL(2,ℤ))
    (n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2}) (z : ℍ) :
    cuspParabolicElement N A n•(A•z)=A•((n.val:ℝ)+ᵥz) := by
  have ht : upperSL n.val•z=(n.val:ℝ)+ᵥz := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply,coe_vadd]
    simp [upperSL,AsymptoticFreshCRT.upper,add_comm]
  change integralLabel (A*upperSL n.val*A⁻¹)•(A•z)=_
  rw [integralLabel_action,mul_smul,mul_smul,inv_smul_smul,ht]

/-- Exact one-dimensional parabolic expansion of the actual high-cusp kernel.
The index condition is the proved integer divisibility criterion. -/
theorem radialPoincareKernel_high_cusp_parabolic_sum (N : ℕ) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (z w : ℍ) (hheight : z.im=w.im) (hz : Real.exp (R/2)<z.im) :
    radialPoincareKernel N g (A•w) (A•z)=
      ∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},g (Real.cosh (dist ((n.val:ℝ)+ᵥz) w)) := by
  let F : gamma N → ℂ := fun γ => g (Real.cosh (dist (γ•(A•z)) (A•w)))
  have hsupport : Function.support F⊆Set.range (cuspParabolicElement N A) := by
    intro γ hγ
    have hd : dist (γ•(A•z)) (A•w)≤R := by
      have hb := Real.cosh_le_cosh.mp (hs hγ)
      simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hb
    obtain ⟨n,hn,_⟩ := high_cusp_return_unique_translation N A γ z w hheight R hd hz
    exact ⟨⟨n,hn.1⟩,Subtype.ext hn.2⟩
  have hh := (cuspParabolicElement_injective N A).tsum_eq hsupport
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  change (∑' γ,F γ)=_
  rw [←hh]
  apply tsum_congr
  intro n
  dsimp only [F]
  rw [cuspParabolicElement_action,integral_action_dist]

#print axioms cuspParabolicElement_injective
#print axioms cuspParabolicElement_action
#print axioms radialPoincareKernel_high_cusp_parabolic_sum

end QuantitativeMaass
