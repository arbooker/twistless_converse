module

public import AsymptoticFiniteBranchDataV1
public import AsymptoticRegionL2V1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap

noncomputable def corner (S : Set ℍ) (hS : MeasurableSet S) : Branch where
  label := 1
  coefficient := S.indicator (fun _ => (1:ℂ))
  measurable := measurable_const.indicator hS
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := AsymptoticRegionL2.indicator_norm S

theorem holomorphic_corner (S : Set ℍ) (hS : MeasurableSet S) (m : ℕ) :
    holomorphic (corner S hS) m=AsymptoticRegionL2.projection volume S hS :=
  AsymptoticConcreteRationalBranch.operator_one_label _ _ _ m

theorem regular_corner (S : Set ℍ) (hS : MeasurableSet S) (z : ℍ) :
    regular (corner S hS) z=AsymptoticOrbitDiagonal.corner S z := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext g
  classical
  simp only [regular,corner,AsymptoticOrbitBranch.operator_apply,AsymptoticOrbitDiagonal.corner_apply,one_mul]
  by_cases hz : g • z∈S <;> simp [hz]

/-- Cutting both endpoints keeps the same geometric branch label and
inserts the two endpoint indicators into its actual coefficient. -/
theorem corner_compose_coefficient (S T : Set ℍ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (b : Branch) (z : ℍ) :
    (compose (corner S hS) (compose b (corner T hT))).coefficient z=
      (S∩(fun w => b.label • w) ⁻¹' T).indicator b.coefficient z := by
  classical
  simp only [compose,corner,one_smul,mul_one]
  by_cases hs : z∈S <;> by_cases ht : b.label • z∈T <;> simp [hs,ht]

#print axioms holomorphic_corner
#print axioms regular_corner
#print axioms corner_compose_coefficient

end AsymptoticFiniteBranch
