module

public import QuantitativeArithmeticSmallLevelEisensteinBoundaryCongruenceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

def cuspColumn (N : ℕ) (γ : SL(2,ℤ)) : Fin 2 → ZMod N := fun i ↦ γ i 0

/-- Finite residue labels actually realized by primitive integral columns. -/
def boundaryLabels (N : ℕ) := Set.range (cuspColumn N)

instance boundaryLabels_finite (N : ℕ) [NeZero N] : Finite (boundaryLabels N) :=
  inferInstanceAs (Finite (Set.range (cuspColumn N)))

def boundaryRepresentative (N : ℕ) (v : boundaryLabels N) : SL(2,ℤ) :=
  Classical.choose v.property

theorem boundaryRepresentative_column (N : ℕ) (v : boundaryLabels N) :
    cuspColumn N (boundaryRepresentative N v) = v.val :=
  Classical.choose_spec v.property

variable (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)

/-- The actual modular boundary map in finitely many residue coordinates. -/
def finiteCuspBoundary (N : ℕ) : ModularForm Γ k →ₗ[ℂ] (boundaryLabels N → ℂ) where
  toFun F v := cuspBoundary Γ k F (boundaryRepresentative N v)
  map_add' F G := by ext v; exact congrFun ((cuspBoundary Γ k).map_add F G) _
  map_smul' c F := by ext v; exact congrFun ((cuspBoundary Γ k).map_smul c F) _

theorem finiteCuspBoundary_recovers (N : ℕ)
    (hΓ : ∀ rho ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ rho ∈ Γ)
    (F : ModularForm Γ k) (γ : SL(2,ℤ)) :
    finiteCuspBoundary Γ k N F ⟨cuspColumn N γ, γ, rfl⟩ = cuspBoundary Γ k F γ := by
  apply cuspBoundary_column_congr Γ k N hΓ
  intro i
  exact congrFun (boundaryRepresentative_column N ⟨cuspColumn N γ, γ, rfl⟩) i

/-- This finite map has exactly the cusp forms as kernel, uniformly in N.
It imposes no condition on the image (in particular none of the weight-two
residue constraints have been presumed). -/
theorem finiteCuspBoundary_ker (N : ℕ)
    (hΓ : ∀ rho ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ rho ∈ Γ) :
    LinearMap.ker (finiteCuspBoundary Γ k N) = ModularForm.cuspFormSubmodule Γ k := by
  rw [← cuspBoundary_ker Γ k]
  ext F
  constructor
  · intro hF
    apply funext
    intro γ
    rw [← finiteCuspBoundary_recovers Γ k N hΓ F γ]
    exact congrFun hF _
  · intro hF
    apply funext
    intro v
    exact congrFun hF (boundaryRepresentative N v)

#print axioms finiteCuspBoundary
#print axioms finiteCuspBoundary_recovers
#print axioms finiteCuspBoundary_ker

end QuantitativeArithmeticSmallLevelEisenstein
