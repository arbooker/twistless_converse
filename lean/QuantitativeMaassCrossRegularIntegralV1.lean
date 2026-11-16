module

public import QuantitativeMaassCrossRegularDiagonalV1
public import AsymptoticFiniteBranchCornersV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticCongruenceStrip AsymptoticRegularTrace ContinuousLinearMap
namespace QuantitativeMaass.CrossCompactBranch

attribute [local instance] Classical.propDecidable

/-- The extra input corner in the physical kernel formula does not change
the regular diagonal at a point of that corner. -/
theorem inputCorner_regular_diagonal (S : Set ℍ) (hS : MeasurableSet S)
    (E : Expression) (x : ℍ) (hx : x ∈ S) :
    matrix (regularSum (composeExpression E [corner S hS]) x) 1 1 =
      matrix (regularSum E x) 1 1 := by
  rw [regularSum_compose]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,regular_corner]
  simp only [AsymptoticRegularTrace.matrix,comp_apply,
    AsymptoticOrbitDiagonal.corner_delta,one_smul,ite_eq_left hx]

/-- Exact regular main integral for the actual localized expression. The
cutoff occurs with its squared modulus, and the returning coefficient uses
membership in the level subgroup rather than a fixed point condition. -/
theorem localExpression_regular_integral (N : ℕ) (S : Set ℍ) (hS : IsCompact S)
    (b : ℍ → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖b x‖ ≤ B) (E : Expression) (v : ℂ) :
    let F := localExpression N S S hS hS b b hb hb B B hB hB hbound hbound E
    (∫ x in S, (matrix (regularSum (composeExpression F [corner S hS.measurableSet]) x) 1 1*v).re) =
      ∫ x in S, (((‖b x‖^2:ℝ):ℂ)*
        (E.map (fun q => if q.label ∈ gamma N then q.coefficient x else 0)).sum*v).re := by
  intro F
  apply setIntegral_congr_fun hS.measurableSet
  intro x hx
  dsimp only
  rw [inputCorner_regular_diagonal S hS.measurableSet F x hx]
  change (matrix (regularSum (localExpression N S S hS hS b b hb hb B B hB hB hbound hbound E) x) 1 1*v).re = _
  rw [localExpression_regular_diagonal N S S hS hS b b hb hb B B hB hB hbound hbound E x hx hx]
  have hn : star (b x)*b x=((‖b x‖^2:ℝ):ℂ) := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' (b x)
  congr 1
  rw [←hn]
  ring

/-- A constant quotient root coefficient factors out of the exact main
integral. The cutoff mass is explicit; it is not silently normalized to one. -/
theorem localExpression_regular_integral_constant (N : ℕ) (S : Set ℍ) (hS : IsCompact S)
    (b : ℍ → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖b x‖ ≤ B) (E : Expression) (c v : ℂ)
    (hcoeff : ∀ x ∈ S,
      (E.map (fun q => if q.label ∈ gamma N then q.coefficient x else 0)).sum = c) :
    let F := localExpression N S S hS hS b b hb hb B B hB hB hbound hbound E
    (∫ x in S, (matrix (regularSum (composeExpression F [corner S hS.measurableSet]) x) 1 1*v).re) =
      (∫ x in S, ‖b x‖^2)*(c*v).re := by
  intro F
  rw [localExpression_regular_integral N S hS b hb B hB hbound E v]
  calc
    _ = ∫ x in S, ‖b x‖^2*(c*v).re := by
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [hcoeff x hx,mul_assoc]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    _ = _ := integral_mul_const _ _

#print axioms inputCorner_regular_diagonal
#print axioms localExpression_regular_integral
#print axioms localExpression_regular_integral_constant

end QuantitativeMaass.CrossCompactBranch
