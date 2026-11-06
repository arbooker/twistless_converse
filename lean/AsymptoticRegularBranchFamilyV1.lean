module

public import AsymptoticRegularCompactBranchV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularBranchFamily

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRationalFreeness AsymptoticRegularCompactBranch

/-- A rational branch together with the positivity needed for its actual
projective orbit label. -/
structure Branch where
  matrix : GL (Fin 2) ℚ
  positive : 0<(realMatrix matrix).det.val

noncomputable def compact (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  operator b.matrix b.positive hε t (AsymptoticCompactBranch.data (realMatrix b.matrix) hs hε t) z

noncomputable def bound (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  (AsymptoticCompactBranch.data (realMatrix b.matrix) hs hε t).folds.card*
    (AsymptoticCompactBranch.data (realMatrix b.matrix) hs hε t).bound

theorem bound_nonneg (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : 0≤bound b hs hε t :=
  mul_nonneg (Nat.cast_nonneg _) (AsymptoticCompactBranch.data (realMatrix b.matrix) hs hε t).bound_nonneg

theorem compact_norm_le (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : ‖compact b hs hε t z‖≤bound b hs hε t :=
  operator_norm_le _ _ _ _ _ _

theorem compact_covariant (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Covariant (compact b hs hε t) :=
  operator_covariant _ _ _ _ _

theorem compact_matrix_measurable (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (a c : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (compact b hs hε t z) a c) :=
  operator_matrix_measurable _ _ hs.measurableSet _ _ _ a c

variable {ι : Type*} [Fintype ι]

noncomputable def family (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ i,c i • compact (b i) hs hε t z

noncomputable def familyBound (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ := ∑ i,‖c i‖*bound (b i) hs hε t

theorem familyBound_nonneg (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : 0≤familyBound b c hs hε t :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (bound_nonneg (b i) hs hε t))

theorem family_norm_le (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : ‖family b c hs hε t z‖≤familyBound b c hs hε t := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (compact_norm_le (b i) hs hε t z) (norm_nonneg _)

theorem family_norm_le_unit (b : ι → Branch) (c : ι → ℂ) (hc : ∀ i,‖c i‖≤1)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    ‖family b c hs hε t z‖≤∑ i,bound (b i) hs hε t := by
  apply (family_norm_le b c hs hε t z).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc i) (bound_nonneg (b i) hs hε t)

theorem family_covariant (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Covariant (family b c hs hε t) :=
  covariant_finsetSum _ _ (fun i _ => covariant_smul _ _ (compact_covariant (b i) hs hε t))

theorem family_matrix_measurable (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (a d : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (family b c hs hε t z) a d) :=
  matrix_finsetSum_measurable _ _
    (fun i _ => matrix_smul_measurable _ _ (compact_matrix_measurable (b i) hs hε t)) a d

#print axioms compact_norm_le
#print axioms family_norm_le
#print axioms family_covariant
#print axioms family_matrix_measurable

end AsymptoticRegularBranchFamily
