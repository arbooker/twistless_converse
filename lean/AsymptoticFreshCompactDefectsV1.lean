module

public import AsymptoticFreshAveragingV1
public import AsymptoticCompactFamilyTranslationV1
public import AsymptoticRegularObservationRowsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshCompactDefects

open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticRegularBranchFamily
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticFreshResidues
open AsymptoticCompactFamilyTranslation AsymptoticRegularTrace AsymptoticMixing
open AsymptoticRegularCompactBranch (Space)
open UpperHalfPlane MeasureTheory ContinuousLinearMap

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

def parameter (i : Fin (q-1)) : ℚ := ((i.val+1:ℕ):ℚ)/q

noncomputable def matrixBranch (i : Fin (q-1)) : Branch :=
  ⟨AsymptoticFreshMatrices.branchMatrix N q hN.ne' (Fact.out : q.Prime).ne_zero
    ((permutation q N hq i).val+1) (i.val+1),
    AsymptoticFreshMatrices.branchMatrix_positive N q hN (Fact.out : q.Prime).pos _ _⟩

noncomputable def reflectedBranch (i : Fin (q-1)) : Branch :=
  ⟨AsymptoticReconstructionBranch.branch ((N:ℚ)*q^2) 0 (parameter q i) (by
    exact mul_ne_zero (by exact_mod_cast hN.ne') (pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero))),
    by
      rw [realMatrix_branch,AsymptoticReconstructionBranch.branch_det]
      have hqp : 0<q := (Fact.out : q.Prime).pos
      positivity⟩

noncomputable def identityBranch : Branch := AsymptoticRegularObservationRows.translation 0

noncomputable def translationBranch (i : Fin (q-1)) : Branch :=
  AsymptoticRegularObservationRows.translation (parameter q i)

theorem matrixBranch_label (i : Fin (q-1)) :
    ofMatrix (matrixBranch N q hN hq i).matrix (matrixBranch N q hN hq i).positive=
      AsymptoticFreshAveraging.defectLabel N q hN hq i := rfl

theorem reflectedBranch_label (i : Fin (q-1)) :
    ofMatrix (reflectedBranch N q hN i).matrix (reflectedBranch N q hN i).positive=
      AsymptoticFreshAveraging.reflectedLabel N q hN i := rfl

omit [Fact q.Prime] in
theorem identityBranch_label : ofMatrix identityBranch.matrix identityBranch.positive=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change AsymptoticRationalGroup.rationalMap (AsymptoticMobiusFold.translation (0:ℚ))=1
  have he : AsymptoticMobiusFold.translation (0:ℚ)=(1:GL (Fin 2) ℚ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AsymptoticMobiusFold.translation,Matrix.GeneralLinearGroup.mkOfDetNeZero ]
  rw [he,map_one]

variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)

/-- The actual bounded individual defect on Ω+b/q, read from the
periodic strip input and retaining its full-orbit output. -/
noncomputable def row (i : Fin (q-1)) (x : ℍ) : Space →L[ℂ] Space :=
  w • compact (matrixBranch N q hN hq i) (shifted_compact (parameter q i) hs) hε t x-
    compact identityBranch (shifted_compact (parameter q i) hs) hε t x

noncomputable def rowBound (i : Fin (q-1)) : ℝ :=
  ‖w‖*bound (matrixBranch N q hN hq i) (shifted_compact (parameter q i) hs) hε t+
    bound identityBranch (shifted_compact (parameter q i) hs) hε t

theorem rowBound_nonneg (i : Fin (q-1)) : 0≤rowBound N q hN hq w hs hε t i :=
  add_nonneg (mul_nonneg (norm_nonneg _) (bound_nonneg _ _ _ _)) (bound_nonneg _ _ _ _)

theorem row_norm_le (i : Fin (q-1)) (x : ℍ) :
    ‖row N q hN hq w hs hε t i x‖≤rowBound N q hN hq w hs hε t i := by
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (compact_norm_le _ _ _ _ _) (norm_nonneg _))
    (compact_norm_le _ _ _ _ _)

theorem row_regular (i : Fin (q-1)) :
    (∀ g h,Measurable (fun x => matrix (row N q hN hq w hs hε t i x) g h)) ∧
      Covariant (row N q hN hq w hs hε t i) :=
  ⟨matrix_sub_measurable _ _ (matrix_smul_measurable _ _ (compact_matrix_measurable _ _ _ _))
    (compact_matrix_measurable _ _ _ _),
    covariant_sub _ _ (covariant_smul _ _ (compact_covariant _ _ _ _)) (compact_covariant _ _ _ _)⟩

theorem row_supported (i : Fin (q-1)) (x : ℍ) :
    Supported (integralGroup q) (row N q hN hq w hs hε t i x) := by
  apply supported_sub
  · apply supported_smul
    apply compact_operator_supported_of_label
    rw [matrixBranch_label]
    exact AsymptoticFreshAveraging.defectLabel_integral N q hN hq i
  · apply compact_operator_supported_of_label
    rw [identityBranch_label]
    exact (integralGroup q).one_mem

theorem translated_matrix_row (i : Fin (q-1)) (x : ℍ) :
    (translation (primeLabels q i)).comp
      (compact (matrixBranch N q hN hq i) (shifted_compact (parameter q i) hs) hε t x)=
    compact (reflectedBranch N q hN (permutation q N hq i)) hs hε t x := by
  rw [show primeLabels q i=translationLabel (parameter q i) from rfl,
    compact_translate_shifted (matrixBranch N q hN hq i) (parameter q i) hs hε t x]
  refine compact_eq_of_label _ _ ?_ hs hε t x
  rw [right_label,matrixBranch_label,reflectedBranch_label]
  exact AsymptoticFreshAveraging.defectLabel_translation N q hN hq i

omit [Fact q.Prime] in
theorem translated_identity_row (i : Fin (q-1)) (x : ℍ) :
    (translation (primeLabels q i)).comp
      (compact identityBranch (shifted_compact (parameter q i) hs) hε t x)=
    compact (translationBranch q i) hs hε t x := by
  rw [show primeLabels q i=translationLabel (parameter q i) from rfl,
    compact_translate_shifted identityBranch (parameter q i) hs hε t x]
  refine compact_eq_of_label _ _ ?_ hs hε t x
  rw [right_label,identityBranch_label,one_mul]
  rfl

/-- Exact averaging identity for the bounded compact defect rows,
including their shifted cutoffs, cap ratios and all input folds. -/
theorem averaged_rows (x : ℍ) :
    mixed (primeLabels q) (fun i => row N q hN hq w hs hε t i x)=
      w • (∑ i,compact (reflectedBranch N q hN i) hs hε t x)-
        ∑ i,compact (translationBranch q i) hs hε t x := by
  simp only [mixed,row,comp_sub,comp_smul]
  simp_rw [translated_matrix_row N q hN hq hs hε t,translated_identity_row q hs hε t]
  rw [Finset.sum_sub_distrib,← Finset.smul_sum]
  congr 1
  exact congrArg (fun B => w • B) (Equiv.sum_comp (permutation q N hq)
    (fun i => compact (reflectedBranch N q hN i) hs hε t x))

#print axioms matrixBranch_label
#print axioms reflectedBranch_label
#print axioms identityBranch_label
#print axioms rowBound_nonneg
#print axioms row_norm_le
#print axioms row_regular
#print axioms row_supported
#print axioms translated_matrix_row
#print axioms translated_identity_row
#print axioms averaged_rows

end AsymptoticFreshCompactDefects
