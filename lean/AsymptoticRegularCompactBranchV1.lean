module

public import AsymptoticRationalCompactFoldV1
public import AsymptoticRegularAlgebraV1
public import AsymptoticOrbitRegionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularCompactBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticCompactBranch (Data coefficient coefficient_norm_le coefficient_measurable)
open scoped lp

noncomputable abbrev Space := ℓ²(AsymptoticRationalGroup.Group,ℂ)

noncomputable def term (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (n : ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator (compactFold g hg n) (coefficient (realMatrix g) s ε t)
    D.bound_nonneg (coefficient_norm_le (realMatrix g) hε t D) z

theorem term_norm_le (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (n : ℤ) (z : ℍ) : ‖term g hg hε t D n z‖≤D.bound :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

theorem term_covariant (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (n : ℤ) : Covariant (term g hg hε t D n) :=
  AsymptoticOrbitBranch.operator_covariant _ _ _ (coefficient_norm_le (realMatrix g) hε t D)

theorem term_matrix_measurable (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (n : ℤ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (term g hg hε t D n z) a b) :=
  AsymptoticOrbitBranch.operator_matrix_measurable (fun a => (action_continuous a).measurable)
    _ _ _ _ (coefficient_measurable (realMatrix g) hs hε t) a b

/-- The finite folded counting operator with exactly the fold set and
weight-ratio bound used in the hyperbolic realization. -/
noncomputable def raw (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) : Space →L[ℂ] Space := ∑ n∈D.folds,term g hg hε t D n z

theorem raw_norm_le (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) : ‖raw g hg hε t D z‖≤D.folds.card*D.bound := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le g hg hε t D n z)).trans_eq
  simp

theorem raw_covariant (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t) :
    Covariant (raw g hg hε t D) :=
  covariant_finsetSum _ _ (fun n _ => term_covariant g hg hε t D n)

theorem raw_matrix_measurable (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (raw g hg hε t D z) a b) :=
  matrix_finsetSum_measurable _ _ (fun n _ => term_matrix_measurable g hg hs hε t D n) a b

/-- Input restriction to the actual strip corner makes this a branch
on periodized counting data, matching the hyperbolic cylinder lift. -/
noncomputable def operator (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) : Space →L[ℂ] Space :=
  (raw g hg hε t D z).comp (AsymptoticOrbitDiagonal.corner AsymptoticMassTransport.strip z)

theorem operator_norm_le (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) : ‖operator g hg hε t D z‖≤D.folds.card*D.bound := by
  apply (opNorm_comp_le _ _).trans
  apply le_trans (mul_le_mul_of_nonneg_left (AsymptoticOrbitRegion.corner_norm_le _ _) (norm_nonneg _))
  simpa only [mul_one] using raw_norm_le g hg hε t D z

theorem operator_covariant (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t) :
    Covariant (operator g hg hε t D) :=
  covariant_comp _ _ (raw_covariant g hg hε t D) (AsymptoticOrbitDiagonal.corner_covariant _)

theorem operator_matrix_measurable (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (operator g hg hε t D z) a b) :=
  matrix_comp_measurable _ _ (raw_matrix_measurable g hg hs hε t D)
    (AsymptoticOrbitDiagonal.corner_matrix_measurable
      (fun a => (action_continuous a).measurable) AsymptoticMassTransport.strip_measurable) a b

theorem operator_apply (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) (f : Space) (a : AsymptoticRationalGroup.Group) :
    operator g hg hε t D z f a=
      ∑ n∈D.folds,coefficient (realMatrix g) s ε t (a • z)*
        (AsymptoticOrbitDiagonal.corner AsymptoticMassTransport.strip z f) (compactFold g hg n*a) := by
  change (lp.evalCLM ℂ (fun _ : AsymptoticRationalGroup.Group => ℂ) 2 a)
    ((∑ n∈D.folds,term g hg hε t D n z) (AsymptoticOrbitDiagonal.corner AsymptoticMassTransport.strip z f))=_
  rw [_root_.sum_apply,map_sum]
  rfl

#print axioms operator_norm_le
#print axioms operator_covariant
#print axioms operator_matrix_measurable
#print axioms operator_apply

end AsymptoticRegularCompactBranch
