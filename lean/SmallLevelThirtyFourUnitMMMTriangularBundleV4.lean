module
public meta import SmallLevelTriangularCertificateCommandsV4
public import SmallLevelThirtyFourUnitMMMInhomogeneousTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourUnitMMM
open Complex

theorem sourceRows_zero (X Y Z W a b : ℂ) :
    ∀ i, sourceRows X Y Z W a b (0 : Fin 510 → ℂ) i = 0 := by
  intro i
  unfold sourceRows
  split <;>
    (simp only [sourceRowsPart0, sourceRowsPart1, sourceRowsPart2, sourceRowsPart3, sourceRowsPart4, sourceRowsPart5, sourceRowsPart6, sourceRowsPart7, sourceRowsPart8, sourceRowsPart9, sourceRowsPart10, sourceRowsPart11, sourceRowsPart12, sourceRowsPart13, sourceRowsPart14, sourceRowsPart15, sourceRowsPart16, sourceRowsPart17, sourceRowsPart18, sourceRowsPart19, sourceRowsPart20, sourceRowsPart21, sourceRowsPart22, sourceRowsPart23, sourceRowsPart24, sourceRowsPart25, sourceRowsPart26, sourceRowsPart27, sourceRowsPart28, sourceRowsPart29, sourceRowsPart30, sourceRowsPart31, sourceRowsPart32, sourceRowsPart33, sourceRowsPart34,
       Pi.zero_apply, mul_zero, add_zero]
     <;> split <;> rfl)

/-- A linear certificate at a general right-hand side already proves its
homogeneous specialization: compare it with the same certificate at zero. -/
theorem homogeneous_of_inhomogeneous {d e : ℕ}
    {rows : (Fin d → ℂ) → Fin e → ℂ} {value : (Fin d → ℂ) → ℂ}
    {rhs : (Fin e → ℂ) → ℂ}
    (certificate : ∀ v r, (∀ i, rows v i = r i) → value v = rhs r)
    (hrows : ∀ i, rows 0 i = 0) (hvalue : value 0 = 0)
    (v : Fin d → ℂ) (hv : ∀ i, rows v i = 0) : value v = 0 :=
  (certificate v 0 hv).trans ((certificate 0 0 hrows).symm.trans hvalue)

specialize_homogeneous_pivots SmallLevelThirtyFourUnitMMMInhomogeneous
  in sourceRows dimension 510 count 411
  zero_rows sourceRows_zero via homogeneous_of_inhomogeneous

end SmallLevelThirtyFourUnitMMM
