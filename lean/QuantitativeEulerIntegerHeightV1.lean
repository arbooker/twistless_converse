module

public import QuantitativeHolomorphicMatrixActionV1
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.NumDen

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerIntegerHeight

open QuantitativeHolomorphic UpperHalfPlane

/-- One common nonzero integer clears every entry of a rational matrix. -/
theorem clear_entries (A : Matrix (Fin 2) (Fin 2) ℚ) :
    ∃ (d : ℤ) (M : IntegerMatrix2), d ≠ 0 ∧
      ∀ i j, (M i j : ℚ) = (d : ℚ) * A i j := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ij : Fin 2 × Fin 2 => A ij.1 ij.2)
  choose m hm using hd
  refine ⟨d, fun i j => m (i,j), ?_, ?_⟩
  · exact nonZeroDivisors.ne_zero d.property
  · intro i j
    simpa [Algebra.smul_def] using hm (i,j)

/-- Every positive rational projective label has an actual integer
Möbius representative valid throughout the upper half-plane. -/
theorem integer_action_exists (g : AsymptoticRationalGroup.Group) :
    ∃ M : IntegerMatrix2, IntegerAction g M := by
  let q := AsymptoticSlashGauge.representative g
  obtain ⟨d,M,hd,hM⟩ := clear_entries q.val
  have hr (i j : Fin 2) : (M i j : ℝ) = (d : ℝ) * (q.val i j : ℝ) := by
    exact_mod_cast hM i j
  have hc (i j : Fin 2) : (M i j : ℂ) = (d : ℂ) * ((q.val i j : ℝ) : ℂ) := by
    exact_mod_cast hr i j
  have hp := AsymptoticRationalGroup.representative_positive g
    (AsymptoticSlashGauge.representative_spec g)
  have hdet : (M.det : ℝ) = (d : ℝ)^2 *
      (AsymptoticRationalFreeness.realMatrix q).det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul]
    rw [hr,hr,hr,hr]
    change _ = (d : ℝ)^2 *
      ((q.val 0 0 : ℝ)*(q.val 1 1 : ℝ)-(q.val 0 1 : ℝ)*(q.val 1 0 : ℝ))
    ring
  refine ⟨M, ?_, ?_⟩
  · intro he
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hh := mul_ne_zero (pow_ne_zero 2 hd') hp.ne'
    exact hh (hdet.symm.trans (by rw [he, Int.cast_zero]))
  · intro z
    rw [← AsymptoticSlashGauge.representative_action g z, coe_smul_of_det_pos hp]
    change (((q.val 0 0 : ℝ):ℂ)*(z:ℂ)+((q.val 0 1 : ℝ):ℂ)) /
      (((q.val 1 0 : ℝ):ℂ)*(z:ℂ)+((q.val 1 1 : ℝ):ℂ)) = _
    rw [hc,hc,hc,hc]
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [mul_assoc, ← mul_add, mul_div_mul_left _ _ hd']

#print axioms clear_entries
#print axioms integer_action_exists

theorem fold_action_sub {L : ℚ} (hL : 0<L) (b d : ℚ) (n : ℤ) (z : UpperHalfPlane) :
    ((AsymptoticRationalBranches.fold hL b d n • z : UpperHalfPlane):ℂ) =
      ((AsymptoticRationalBranches.fold hL b d 0 • z : UpperHalfPlane):ℂ) - n := by
  rw [AsymptoticRationalBranches.fold_action, AsymptoticRationalBranches.fold_action]
  simp only [AsymptoticFoldedLow.fold]
  rw [AsymptoticReconstructionBranch.branch_action (show (0:ℝ)<L by exact_mod_cast hL),
    AsymptoticReconstructionBranch.branch_action (show (0:ℝ)<L by exact_mod_cast hL)]
  push_cast
  ring

/-- Integer fold translation enlarges representative height at most linearly
in the cutoff; the original representative remains fixed. -/
theorem fold_integer_height {L : ℚ} (hL : 0<L) (b d : ℚ)
    {M : IntegerMatrix2} {B : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.fold hL b d 0) M)
    (hB : MatrixEntryBound M B) (n : ℤ) :
    ∃ Mn : IntegerMatrix2,
      IntegerAction (AsymptoticRationalBranches.fold hL b d n) Mn ∧
        MatrixEntryBound Mn (2*(1+|(n:ℝ)|)*B) := by
  let T : IntegerMatrix2 := !![1,-n;0,1]
  have hT : MatrixEntryBound T (1+|(n:ℝ)|) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [T, abs_nonneg]
    positivity
  refine ⟨T*M, ⟨?_, ?_⟩, matrix_entry_bound_mul (by positivity) hT hB⟩
  · rw [Matrix.det_mul]
    simpa [T, Matrix.det_fin_two] using hM.1
  · intro z
    rw [fold_action_sub, hM.2]
    have hd := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 z
    norm_num [T, Matrix.mul_apply, Fin.sum_univ_two]
    apply (eq_div_iff hd).2
    rw [sub_mul, div_mul_cancel₀ _ hd]
    ring

/-- A fixed finite family of labels has a common integer entry bound. -/
theorem finite_family_height {ι : Type*} [Finite ι]
    (g : ι → AsymptoticRationalGroup.Group) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i, ∃ M : IntegerMatrix2,
      IntegerAction (g i) M ∧ MatrixEntryBound M B := by
  choose M hM using fun i => integer_action_exists (g i)
  let f := fun p : ι × Fin 2 × Fin 2 => |(M p.1 p.2.1 p.2.2 : ℝ)|
  obtain ⟨B,hB⟩ := (Set.finite_range f).bddAbove
  refine ⟨max 1 B, le_max_left _ _, fun i => ⟨M i, hM i, ?_⟩⟩
  intro j k
  exact (hB ⟨(i,j,k),rfl⟩).trans (le_max_right _ _)

#print axioms fold_integer_height
#print axioms finite_family_height
end QuantitativeEulerIntegerHeight
