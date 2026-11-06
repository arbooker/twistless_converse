module

public import QuantitativeEulerDiamondNormalizerV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix CongruenceSubgroup QuantitativeArithmetic AsymptoticFreshMatrices
open scoped MatrixGroups

theorem swapped_certificate (N q : ℕ) (a b c : ℤ)
    (h : (q : ℤ)*c=(N : ℤ)*a*b+1) : (q : ℤ)*c=(N : ℤ)*b*a+1 := by
  nlinarith [h]

/-- The two conventions for the canonical matrix are explicitly related.
The fresh-branch convention is g=W*C(a,b), whereas the diamond convention
uses W*g⁻¹=C(b,a) projectively. This exact integral identity supplies the
conjugation before canceling W in the rational matrix group. -/
theorem canonical_fricke_inverse (N q : ℕ) (a b c : ℤ)
    (h : (q : ℤ)*c=(N : ℤ)*a*b+1) :
    integralFrickeMatrix N*((canonical N q a b c h)⁻¹).val=
      (canonical N q b a c (swapped_certificate N q a b c h)).val*integralFrickeMatrix N := by
  rw [SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralFrickeMatrix,canonical,canonicalEntries,
      adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

/-- Every pair of actual canonical matrices at the same prime differs
by a Γ₁ element, including the two canonical conventions above. -/
theorem canonical_same_prime_difference (N q : ℕ) (a b c a' b' c' : ℤ)
    (h : (q : ℤ)*c=(N : ℤ)*a*b+1)
    (h' : (q : ℤ)*c'=(N : ℤ)*a'*b'+1) :
    (canonical N q a b c h)⁻¹*canonical N q a' b' c' h'∈Gamma1 N :=
  same_residue_quotient N _ _ (canonical_mem_Gamma0 N q a b c h)
    (canonical_mem_Gamma0 N q a' b' c' h') rfl

#print axioms canonical_fricke_inverse
#print axioms canonical_same_prime_difference
end QuantitativeEulerDensityGenerators
