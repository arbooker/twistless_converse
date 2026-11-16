module

public import QuantitativeMaassEulerLinearMapV1
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

def originalEulerPolynomial (N : ℕ) (r : ℝ) (σ : ℕ)
    (b : MaassOriginal.EulerS N (.principal r) σ) : polynomialCoefficientSpace :=
  ⟨b.val,mem_polynomialCoefficientSpace b.property.zero b.property.polynomialGrowth⟩

theorem originalEulerSmooth_independent (N : ℕ) (r : ℝ) (σ : ℕ) :
    LinearIndependent ℂ (fun b : MaassOriginal.EulerS N (.principal r) σ =>
      principalEulerSmoothMap r σ (originalEulerPolynomial N r σ b)) := by
  have hc : LinearIndependent ℂ (originalEulerPolynomial N r σ) :=
    LinearIndependent.of_comp polynomialCoefficientSpace.subtype
      (MaassOriginal.euler_independent N (.principal r) σ)
  exact hc.map' (principalEulerSmoothMap r σ)
    (LinearMap.ker_eq_bot.mpr (principalEulerSmoothMap_injective r σ))

theorem principalEigenvalue_injective : Function.Injective
    (fun r : {r : ℝ // 0≤r} => ((1/4+r.val^2:ℝ):ℂ)) := by
  intro r s h
  apply Subtype.ext
  have he : 1/4+r.val^2=1/4+s.val^2 := Complex.ofReal_injective h
  nlinarith [r.property,s.property]

/-- The complete original Euler family, indexed simultaneously by all
nonnegative real parameters and all coefficient sequences, is linearly
independent as actual smooth waves. Separation of parameters uses the
literal Laplacian; fixed-parameter independence uses Euler products. -/
theorem originalEuler_all_principal_independent (N σ : ℕ) :
    LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS N (.principal r.val) σ =>
      principalEulerSmoothMap rb.1.val σ (originalEulerPolynomial N rb.1.val σ rb.2)) := by
  let V := fun r : {r : ℝ // 0≤r} => smoothUpperLaplacian.eigenspace ((1/4+r.val^2:ℝ):ℂ)
  have hi : iSupIndep V := smoothUpper_eigenspaces_independent.comp principalEigenvalue_injective
  have hs (r : {r : ℝ // 0≤r}) : Submodule.span ℂ
      (range (fun b : MaassOriginal.EulerS N (.principal r.val) σ =>
        principalEulerSmoothMap r.val σ (originalEulerPolynomial N r.val σ b)))≤V r := by
    apply Submodule.span_le.mpr
    rintro v ⟨b,rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    exact principalEulerSmooth_eigen (polynomialCoefficientSpace_growth (originalEulerPolynomial N r.val σ b)) r.val σ
  apply linearIndependent_iUnion_finite (fun r : {r : ℝ // 0≤r} => originalEulerSmooth_independent N r.val σ)
  intro r t _ hrt
  apply (hi.disjoint_biSup hrt).mono (hs r)
  exact iSup_mono (fun s => iSup_mono (fun _ => hs s))

#print axioms originalEulerSmooth_independent
#print axioms principalEigenvalue_injective
#print axioms originalEuler_all_principal_independent

end QuantitativeMaass
