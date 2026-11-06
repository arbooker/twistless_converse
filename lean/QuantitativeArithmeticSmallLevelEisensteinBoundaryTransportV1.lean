module

public import QuantitativeArithmeticSmallLevelEisensteinBoundaryV1
public import AsymptoticClassicalTriangularSlashV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

/-- Exact transport of a cusp constant through a positive triangular
matrix, retaining Mathlib's determinant normalization. -/
theorem tendsto_slash_triangular {F : ℍ → ℂ} {C : ℂ}
    (hF : Tendsto F atImInfty (nhds C))
    (a b d : ℝ) (ha : 0<a) (hd : 0<d) (k : ℤ) :
    Tendsto (F ∣[k] triangularGL a b d ha hd) atImInfty
      (nhds (triangularFactor a d k * C)) := by
  have h := (hF.comp (affine_tendsto (a/d) (div_pos ha hd) (b/d))).const_mul
    (triangularFactor a d k)
  convert h using 1
  ext z
  exact slash_triangular a b d ha hd k F z

theorem valueAtInfty_slash_triangular {F : ℍ → ℂ} {C : ℂ}
    (hF : Tendsto F atImInfty (nhds C))
    (a b d : ℝ) (ha : 0<a) (hd : 0<d) (k : ℤ) :
    valueAtInfty (F ∣[k] triangularGL a b d ha hd) = triangularFactor a d k * C :=
  (tendsto_slash_triangular hF a b d ha hd k).limUnder_eq

variable (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)

theorem cuspBoundary_left (F : ModularForm Γ k) (δ γ : SL(2,ℤ))
    (hδ : SpecialLinearGroup.mapGL ℝ δ ∈ Γ) :
    cuspBoundary Γ k F (δ*γ) = cuspBoundary Γ k F γ := by
  have hF := F.slash_action_eq' _ hδ
  change (F : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ δ = F at hF
  have hF' : (F : ℍ → ℂ) ∣[k] δ = F := by
    change (F : ℍ → ℂ) ∣[k]
      SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) δ) = F at hF
    simpa only [ModularForm.SL_slash] using hF
  simp only [cuspBoundary_apply,SlashAction.slash_mul,hF']

/-- Literal cusp constant after an arbitrary SL2Z matrix followed by a
positive triangular matrix. This is the analytic input to the Hecke action
on the boundary; the remaining work is finite matrix arithmetic. -/
theorem cuspBoundary_triangular (F : ModularForm Γ k) (γ : SL(2,ℤ))
    (a b d : ℝ) (ha : 0<a) (hd : 0<d) :
    valueAtInfty (((F : ℍ → ℂ) ∣[k] γ) ∣[k] triangularGL a b d ha hd) =
      triangularFactor a d k * cuspBoundary Γ k F γ :=
  valueAtInfty_slash_triangular (cuspBoundary_tendsto Γ k F γ) a b d ha hd k

#print axioms tendsto_slash_triangular
#print axioms cuspBoundary_left
#print axioms cuspBoundary_triangular

end QuantitativeArithmeticSmallLevelEisenstein
