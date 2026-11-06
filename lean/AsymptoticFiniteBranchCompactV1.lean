module

public import AsymptoticConcreteBranchMatrixV1
public import AsymptoticFiniteBranchSumsV1
public import AsymptoticFiniteBranchCornersV1
public import AsymptoticRegularCompactBranchV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap
open AsymptoticRationalFreeness

noncomputable def compactFold (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (n : ℤ) : Branch where
  label := AsymptoticRationalBranches.compactFold g hg n
  coefficient := AsymptoticCompactBranch.coefficient (realMatrix g) s ε t
  measurable := AsymptoticCompactBranch.coefficient_measurable (realMatrix g) hs hε t
  bound := D.bound
  bound_nonneg := D.bound_nonneg
  norm_le := AsymptoticCompactBranch.coefficient_norm_le (realMatrix g) hε t D

theorem holomorphic_compactFold (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (m : ℕ) (n : ℤ) :
    holomorphic (compactFold g hg hs hε t D n) m=
      AsymptoticCompactBranch.term (realMatrix g) hs hε t D m n :=
  AsymptoticConcreteRationalBranch.operator_compactFold g hg n _ _ _ m

theorem regular_compactFold (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (n : ℤ) (z : ℍ) :
    regular (compactFold g hg hs hε t D n) z=
      AsymptoticRegularCompactBranch.term g hg hε t D n z := rfl

noncomputable def compactRawExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) : Expression :=
  ofFinset D.folds (compactFold g hg hs hε t D)

theorem holomorphicSum_compactRawExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (m : ℕ) :
    holomorphicSum (compactRawExpression g hg hs hε t D) m=
      AsymptoticCompactBranch.operator (realMatrix g) hs hε t D m := by
  rw [compactRawExpression,holomorphicSum_ofFinset,AsymptoticCompactBranch.operator]
  exact Finset.sum_congr rfl (fun n _ => holomorphic_compactFold g hg hs hε t D m n)

theorem regularSum_compactRawExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (z : ℍ) :
    regularSum (compactRawExpression g hg hs hε t D) z=
      AsymptoticRegularCompactBranch.raw g hg hε t D z := by
  rw [compactRawExpression,regularSum_ofFinset,AsymptoticRegularCompactBranch.raw]
  exact Finset.sum_congr rfl (fun n _ => regular_compactFold g hg hs hε t D n z)

noncomputable def compactExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) : Expression :=
  composeExpression (compactRawExpression g hg hs hε t D)
    [corner AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable]

theorem holomorphicSum_compactExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (m : ℕ) :
    holomorphicSum (compactExpression g hg hs hε t D) m=
      (AsymptoticCompactBranch.operator (realMatrix g) hs hε t D m).comp
        (AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable) := by
  rw [compactExpression,holomorphicSum_compose,holomorphicSum_compactRawExpression]
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,holomorphic_corner]

theorem regularSum_compactExpression (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : AsymptoticCompactBranch.Data (realMatrix g) s ε t) (z : ℍ) :
    regularSum (compactExpression g hg hs hε t D) z=
      AsymptoticRegularCompactBranch.operator g hg hε t D z := by
  rw [compactExpression,regularSum_compose,regularSum_compactRawExpression]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,regular_corner]
  rfl

#print axioms holomorphic_compactFold
#print axioms regular_compactFold
#print axioms holomorphicSum_compactRawExpression
#print axioms regularSum_compactRawExpression
#print axioms holomorphicSum_compactExpression
#print axioms regularSum_compactExpression

end AsymptoticFiniteBranch
