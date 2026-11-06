module

public import QuantitativeArithmeticSmallLevelEisensteinBoundaryFiniteV1
public import AsymptoticClassicalIntegralTriangularV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

/-- Integral triangular reduction with the actual real GL matrix and both
primitive-column coordinates retained. -/
theorem integral_triangularGL (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : 0<B.det)
    (g : GL (Fin 2) ℝ) (hg : g.val = B.map (Int.castRingHom ℝ)) :
    ∃ (U : SL(2,ℤ)) (a b d : ℤ) (ha : 0<a) (hd : 0<d),
      a*d=B.det ∧ (∀ i : Fin 2, B i 0 = U i 0*a) ∧
      g = SpecialLinearGroup.mapGL ℝ U * triangularGL (a:ℝ) (b:ℝ) (d:ℝ)
        (by exact_mod_cast ha) (by exact_mod_cast hd) := by
  obtain ⟨U,a,b,d,ha,hd,he⟩ := integral_triangular B hB
  have had : a*d=B.det := by
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,U.property,one_mul] at hh
    simpa [Matrix.det_fin_two] using hh.symm
  refine ⟨U,a,b,d,ha,hd,had,?_,?_⟩
  · intro i
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M i 0) he
    simpa [Matrix.mul_apply,Fin.sum_univ_two] using hh
  · apply Units.ext
    rw [hg,he]
    change (U.val * !![a,b;0,d]).map (Int.castRingHom ℝ) =
      U.val.map (Int.castRingHom ℝ) * !![(a:ℝ),(b:ℝ);0,(d:ℝ)]
    rw [Matrix.map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- When triangular reduction preserves the primitive column modulo N,
its cusp constant is determined by that column and the diagonal factor. -/
theorem boundary_integral_term
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)
    (N : ℕ)
    (hΓ : ∀ rho ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ rho ∈ Γ)
    (F : ModularForm Γ k) (γ U : SL(2,ℤ)) (a b d : ℤ) (ha : 0<a) (hd : 0<d)
    (g : GL (Fin 2) ℝ)
    (htri : g = SpecialLinearGroup.mapGL ℝ U * triangularGL (a:ℝ) (b:ℝ) (d:ℝ)
      (by exact_mod_cast ha) (by exact_mod_cast hd))
    (hcol : ∀ i : Fin 2, (U i 0 : ZMod N) = (γ i 0 : ZMod N)) :
    Tendsto ((F : ℍ → ℂ) ∣[k] g) atImInfty
      (nhds (triangularFactor (a:ℝ) (d:ℝ) k * cuspBoundary Γ k F γ)) := by
  rw [htri,SlashAction.slash_mul]
  have ht := tendsto_slash_triangular (cuspBoundary_tendsto Γ k F U)
    (a:ℝ) (b:ℝ) (d:ℝ) (by exact_mod_cast ha) (by exact_mod_cast hd) k
  have he := cuspBoundary_column_congr Γ k N hΓ F U γ hcol
  change valueAtInfty ((F : ℍ → ℂ) ∣[k] U) = cuspBoundary Γ k F γ at he
  rw [he] at ht
  change Tendsto (((F : ℍ → ℂ) ∣[k]
    SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) U)) ∣[k] _) _ _
  simpa only [ModularForm.SL_slash] using ht

/-- The two possible triangular factors at a prime determinant. -/
theorem triangularFactor_prime (p : ℕ) (hp : 0<p) (k : ℤ) :
    triangularFactor 1 (p:ℝ) k = (p:ℂ)⁻¹ ∧
    triangularFactor (p:ℝ) 1 k = (p:ℂ)^(k-1) := by
  have hpC : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  constructor
  · simp only [triangularFactor,one_mul,Complex.ofReal_natCast]
    rw [← zpow_add₀ hpC]
    rw [show k-1+ -k = (-1 : ℤ) by omega]
    exact _root_.zpow_neg_one _
  · simp [triangularFactor]

#print axioms integral_triangularGL
#print axioms boundary_integral_term
#print axioms triangularFactor_prime

end QuantitativeArithmeticSmallLevelEisenstein
