module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSoftObstruction
open Matrix

def tiltedProjection (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a^2,a*b; a*b,b^2]

def coordinateProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]

theorem tilted_idempotent {a b : ℝ} (hab : a^2+b^2=1) :
    tiltedProjection a b*tiltedProjection a b=tiltedProjection a b := by
  have h : tiltedProjection a b*tiltedProjection a b=(a^2+b^2) • tiltedProjection a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tiltedProjection,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  simpa only [hab,one_smul] using h

theorem tilted_trace {a b : ℝ} (hab : a^2+b^2=1) :
    Matrix.trace (tiltedProjection a b)=1 := by
  simpa [Matrix.trace,tiltedProjection,Fin.sum_univ_two] using hab

/-- Compression has a positive scalar on the entire tilted rank-one
source, even when that scalar is arbitrarily small. -/
theorem compressed_coordinate (a b : ℝ) :
    tiltedProjection a b*coordinateProjection*tiltedProjection a b=
      a^2 • tiltedProjection a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tiltedProjection,coordinateProjection,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- Killing the coordinate observed by the UNCOMPRESSED projection loses
only a^2 of trace, not the whole rank-one source. -/
theorem uncompressed_filter_trace {a b : ℝ} (hab : a^2+b^2=1) :
    Matrix.trace ((1-coordinateProjection)*tiltedProjection a b*(1-coordinateProjection))=1-a^2 := by
  simp [Matrix.trace,tiltedProjection,coordinateProjection,Matrix.mul_apply,Fin.sum_univ_two]
  linarith

theorem rational_unit_pair (m : ℝ) :
    (2*m/(m^2+1))^2+((m^2-1)/(m^2+1))^2=1 := by
  have hd : m^2+1≠0 := by positivity
  field_simp
  ring

/-- Thus the loss from filtering the uncompressed operator can tend to
zero although the compressed positive spectral direction has trace one.
This obstructs a naive replacement of exact deflation by that filter. -/
theorem rational_pair_small_loss {m : ℝ} (hm : 1≤m) :
    0<(2*m/(m^2+1))^2 ∧ (2*m/(m^2+1))^2≤4/m^2 := by
  have hmp : 0<m := zero_lt_one.trans_le hm
  have hd : 0<m^2+1 := by positivity
  constructor
  · positivity
  · rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hmp)).2
    nlinarith [sq_nonneg m]

#print axioms tilted_idempotent
#print axioms tilted_trace
#print axioms compressed_coordinate
#print axioms uncompressed_filter_trace
#print axioms rational_unit_pair
#print axioms rational_pair_small_loss
end QuantitativeEulerEndpointSoftObstruction
