module

public import QuantitativeArithmeticRetainedDilationOperatorV1
public import AsymptoticConcreteBranchMatrixV1
public import AsymptoticFiniteBranchDataV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedDilationBranches

open UpperHalfPlane Matrix MeasureTheory Set ContinuousLinearMap
open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedDilationOperator

/-- Rational representatives for the actual retained dilation branches. -/
def rationalAffine (a b : ℚ) (ha : 0<a) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a,b;0,1] (by simpa using ha.ne')

theorem real_positive {a : ℚ} (ha : 0<a) : (0:ℝ)<a := by exact_mod_cast ha

theorem realMatrix_affine (a b : ℚ) (ha : 0<a) :
    realMatrix (rationalAffine a b ha)=affine (a:ℝ) (b:ℝ) (real_positive ha) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrix,rationalAffine,affine,Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem det_positive (a b : ℚ) (ha : 0<a) :
    0<(realMatrix (rationalAffine a b ha)).det.val := by
  rw [realMatrix_affine,affine_det]
  exact real_positive ha

/-- One datum supplies both the holomorphic and regular realizations. -/
def branch (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (n : ℤ) : Branch where
  label := compactFold (rationalAffine a b ha) (det_positive a b ha) n
  coefficient := coefficient (a:ℝ) (b:ℝ) (real_positive ha) s r n
  measurable := coefficient_measurable (a:ℝ) (b:ℝ) (real_positive ha) hs hr n
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := coefficient_norm_le (a:ℝ) (b:ℝ) (real_positive ha) s r n

theorem holomorphic_branch (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (n : ℤ) (m : ℕ) :
    holomorphic (branch a b ha hs hr n) m=
      term (a:ℝ) (b:ℝ) (real_positive ha) hs hr (2*m) n := by
  unfold holomorphic branch
  rw [AsymptoticConcreteRationalBranch.operator_compactFold,realMatrix_affine]
  rfl

def lowBranch (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (t : ℕ) (n : ℤ) : Branch :=
  scale (((a:ℝ)⁻¹^t:ℝ):ℂ) (branch a b ha hs hr n)

theorem lowBranch_bound (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (t : ℕ) (n : ℤ) :
    (lowBranch a b ha hs hr t n).bound=(a:ℝ)⁻¹^t := by
  simp only [lowBranch,scale,branch,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (real_positive ha).le) t)

def terminalBranch (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (t : ℕ) (n : ℤ) : Branch where
  label := (branch a b ha hs hr n).label
  coefficient z := capWeight ε t z * (branch a b ha hs hr n).coefficient z
  measurable := (capWeight_measurable ε t).mul (branch a b ha hs hr n).measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le z := by
    rw [norm_mul]
    exact (mul_le_mul (capWeight_norm_le ε hε t z)
      ((branch a b ha hs hr n).norm_le z) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem holomorphic_low_sum (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (β : ℂ) (t m : ℕ) :
    (∑ n∈folds (a:ℝ) (b:ℝ), β • holomorphic (lowBranch a b ha hs hr t n) m)=
      weighted (a:ℝ) (b:ℝ) (real_positive ha) hs hr β t (2*m) := by
  simp only [lowBranch,holomorphic_scale,holomorphic_branch,weighted,folded,
    smul_smul,Finset.smul_sum]

theorem holomorphic_terminalBranch (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (t : ℕ) (n : ℤ) (m : ℕ) :
    holomorphic (terminalBranch a b ha hs hr ε hε t n) m=
      (capOperator ε hε t).comp (term (a:ℝ) (b:ℝ) (real_positive ha) hs hr (2*m) n) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hcap := AsymptoticL2Multiplier.operator_coeFn (capWeight ε t)
    (capWeight_measurable ε t).aestronglyMeasurable
    (Filter.Eventually.of_forall (capWeight_norm_le ε hε t))
    (term (a:ℝ) (b:ℝ) (real_positive ha) hs hr (2*m) n f)
  have hL := AsymptoticConcreteRationalBranch.operator_coeFn
    (terminalBranch a b ha hs hr ε hε t n).label
    (terminalBranch a b ha hs hr ε hε t n).coefficient
    (terminalBranch a b ha hs hr ε hε t n).measurable
    (terminalBranch a b ha hs hr ε hε t n).norm_le m f
  -- Comparing the coefficients via the same rational matrix avoids any
  -- choice of a different projective representative or slash phase.
  have hB := AsymptoticConcreteRationalBranch.operator_coeFn
    (branch a b ha hs hr n).label (branch a b ha hs hr n).coefficient
    (branch a b ha hs hr n).measurable (branch a b ha hs hr n).norm_le m f
  have hEq := holomorphic_branch a b ha hs hr n m
  filter_upwards [hL,hB,hcap] with z hL hB hcap
  change holomorphic (terminalBranch a b ha hs hr ε hε t n) m f z=
    capOperator ε hε t (term (a:ℝ) (b:ℝ) (real_positive ha) hs hr (2*m) n f) z
  rw [show holomorphic (terminalBranch a b ha hs hr ε hε t n) m f z=_ from hL,
    show capOperator ε hε t (term (a:ℝ) (b:ℝ) (real_positive ha) hs hr (2*m) n f) z=_ from hcap,
    ← hEq]
  change (capWeight ε t z * (branch a b ha hs hr n).coefficient z)*
      AsymptoticSlashGauge.phase (branch a b ha hs hr n).label m z*
      f ((branch a b ha hs hr n).label • z)=
    capWeight ε t z*(holomorphic (branch a b ha hs hr n) m f z)
  rw [show holomorphic (branch a b ha hs hr n) m f z=_ from hB]
  ring

theorem holomorphic_terminal_sum (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (β : ℂ) (t m : ℕ) :
    (∑ n∈folds (a:ℝ) (b:ℝ),β • holomorphic (terminalBranch a b ha hs hr ε hε t n) m)=
      terminal (a:ℝ) (b:ℝ) (real_positive ha) hs hr ε hε β t (2*m) := by
  simp only [holomorphic_terminalBranch,terminal,folded,comp_finsetSum,Finset.smul_sum]

theorem regular_low_norm_le (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (t : ℕ) (z : ℍ) :
    ‖∑ n∈folds (a:ℝ) (b:ℝ),regular (lowBranch a b ha hs hr t n) z‖≤
      (a:ℝ)⁻¹^t*(folds (a:ℝ) (b:ℝ)).card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n∈folds (a:ℝ) (b:ℝ),(a:ℝ)⁻¹^t := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [lowBranch_bound] using regular_norm_le (lowBranch a b ha hs hr t n) z
    _ = _ := by simp [mul_comm]

theorem regular_terminal_norm_le (a b : ℚ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (t : ℕ) (z : ℍ) :
    ‖∑ n∈folds (a:ℝ) (b:ℝ),regular (terminalBranch a b ha hs hr ε hε t n) z‖≤
      (folds (a:ℝ) (b:ℝ)).card := by
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun n _ => regular_norm_le
    (terminalBranch a b ha hs hr ε hε t n) z)).trans_eq (by simp [terminalBranch])

#print axioms holomorphic_terminal_sum
#print axioms holomorphic_branch
#print axioms holomorphic_low_sum
#print axioms holomorphic_terminalBranch
#print axioms regular_low_norm_le
#print axioms regular_terminal_norm_le

end QuantitativeArithmeticRetainedDilationBranches
