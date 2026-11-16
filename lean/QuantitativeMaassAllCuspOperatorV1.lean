module

public import QuantitativeMaassCuspHeckeOperatorV1
public import Mathlib.NumberTheory.ModularForms.Cusps

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane OnePoint
open AsymptoticCongruenceStrip AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped MatrixGroups BigOperators

namespace QuantitativeMaass

/-- Integral charts really do cover every cusp of the arithmetic level
subgroup; the all-chart identities therefore omit no cusp. -/
theorem level_cusp_has_integral_chart (N : ℕ) (hN : 0<N)
    (c : OnePoint ℝ) (hc : IsCusp c (level N)) :
    ∃ s : SL(2,ℤ), c=SpecialLinearGroup.mapGL ℝ s • (∞ : OnePoint ℝ) := by
  let : NeZero N := ⟨hN.ne'⟩
  exact isCusp_SL2Z_iff'.mp ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (level N)).mp hc)

/-- The actual representative of the bounded self-adjoint Hecke operator
satisfies the proved constant-term law at every integral cusp chart. -/
theorem heckeRepresentative_allCusp_constant (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (s : SL(2,ℤ)) (y : ℝ) :
    cuspConstant N s (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val y =
      (Real.sqrt (p:ℝ))⁻¹ • cuspConstant N s f.val ((p:ℝ)*y) +
      Real.sqrt (p:ℝ) • cuspConstant N s f.val (y/p) := by
  rw [←normalizedCuspHecke_eq_representative N p hN hpN hNp A B hAB f]
  exact normalizedCuspHecke_constant N p hNp hpres s f.val hf f.property.2.1 y

/-- In particular the constructed bounded Hecke operator preserves actual
vanishing constant terms at every cusp, on continuous L² representatives. -/
theorem heckeRepresentative_preserves_allCusp_zero (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2,ℤ), ∀ y : ℝ, 0<y → cuspConstant N s f.val y=0)
    (s : SL(2,ℤ)) (y : ℝ) (hy : 0<y) :
    cuspConstant N s (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val y=0 := by
  rw [heckeRepresentative_allCusp_constant N p hN hpN hNp hpres A B hAB f hf]
  have hpR : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [hzero s _ (mul_pos hpR hy),hzero s _ (div_pos hy hpR),smul_zero,smul_zero,add_zero]

#print axioms level_cusp_has_integral_chart
#print axioms heckeRepresentative_allCusp_constant
#print axioms heckeRepresentative_preserves_allCusp_zero

end QuantitativeMaass
