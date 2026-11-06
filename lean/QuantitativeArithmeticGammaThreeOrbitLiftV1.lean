module
public import SmallLevelTwoThreeFourGeneratorsV1
public import SmallLevelNormalizedMatricesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGammaThreeOrbit
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem gamma_three_closure : CongruenceSubgroup.Gamma0 3=Subgroup.closure {T,lower 3,-1} := by
  apply le_antisymm
  · intro γ hγ
    apply gamma0_3_mem _ _ _ _ γ hγ
    all_goals apply Subgroup.subset_closure; simp
  · apply (Subgroup.closure_le _).mpr
    intro γ hγ
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hγ
    rcases hγ with rfl|rfl|rfl
    all_goals apply CongruenceSubgroup.Gamma0_mem.mpr; norm_num [T,lower]
    decide

/-- Covariance on the three generators propagates inside Gamma0(3).
The state may be indexed by a finite reduction, without independence of states. -/
theorem finite_orbit_lift (k : ℤ) (w : SL(2,ℤ) → ℍ → ℂ)
    (hT : ∀ A : SL(2,ℤ),A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] T=w (A*T))
    (hU : ∀ A : SL(2,ℤ),A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] lower 3=w (A*lower 3))
    (hZ : ∀ A : SL(2,ℤ),A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] (-1:SL(2,ℤ))=w (A*(-1)))
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 3) :
    ∀ A : SL(2,ℤ),A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] γ=w (A*γ) := by
  rw [gamma_three_closure] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem γ hγ =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hγ
    rcases hγ with rfl|rfl|rfl
    · exact hT
    · exact hU
    · exact hZ
  | one => intro A _; simp
  | mul γ δ hγ _ ihγ ihδ =>
    intro A hA
    rw [SlashAction.slash_mul,ihγ A hA,ihδ (A*γ) ((CongruenceSubgroup.Gamma0 3).mul_mem hA (by rwa [gamma_three_closure])),mul_assoc]
  | inv γ hγ ih =>
    intro A hA
    have hg : γ∈CongruenceSubgroup.Gamma0 3 := by rwa [gamma_three_closure]
    have hh := congrArg (fun F : ℍ → ℂ => F ∣[k] γ⁻¹)
      (ih (A*γ⁻¹) ((CongruenceSubgroup.Gamma0 3).mul_mem hA ((CongruenceSubgroup.Gamma0 3).inv_mem hg)))
    simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,mul_assoc,inv_mul_cancel,mul_one] using hh.symm
#print axioms finite_orbit_lift
end QuantitativeArithmeticGammaThreeOrbit
