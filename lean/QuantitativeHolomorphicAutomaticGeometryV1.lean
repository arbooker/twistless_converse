module

public import QuantitativeHolomorphicUniformTraceV1
public import QuantitativeArithmeticCertificateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch UpperHalfPlane MeasureTheory

/-- If both retained endpoints are impossible, all analytic requirements are
vacuous. A fixed nonscalar representative avoids an artificial obstruction
from integral translations in the periodized nonidentity test. -/
def retainedBranchGeometry_of_empty (b : Branch) (Y H D : ℝ) (S : Finset ℤ)
    (he : endpointRegion Y H b = ∅) : RetainedBranchGeometry b Y H D S where
  a := 2
  b' := 0
  c := 0
  d := 1
  det_ne := by norm_num
  denominator_ne := by intro z hz; simp only [he,Set.mem_empty_iff_false] at hz
  denominator_bound := by intro z hz; simp only [he,Set.mem_empty_iff_false] at hz
  action_formula := by intro z hz; simp only [he,Set.mem_empty_iff_false] at hz
  translated_nonidentity := by intro j _; exact Or.inr (Or.inl (by norm_num))

/-- A nonzero integral horizontal translate cannot have both endpoints in
the chosen half-open unit strip. This includes its boundary without an
almost-everywhere qualification. -/
theorem retained_endpoint_empty_of_integer_translation (b : Branch) (Y H : ℝ)
    (j : ℤ) (hj : j ≠ 0) (hact : ∀ z : UpperHalfPlane, (b.label • z).re=z.re+j) :
    endpointRegion Y H b=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz0 : 0 ≤ z.re := hz.1.1.1
  have hz1 : z.re < 1 := hz.1.1.2
  have hw0 : 0 ≤ (b.label • z).re := hz.2.1.1
  have hw1 : (b.label • z).re < 1 := hz.2.1.2
  rw [hact] at hw0 hw1
  have hj0 : (-1:ℤ)<j := by exact_mod_cast (show (-1:ℝ)<(j:ℝ) by linarith)
  have hj1 : j<(1:ℤ) := by exact_mod_cast (show (j:ℝ)<(1:ℝ) by linarith)
  omega

theorem rational_label_eq_one_of_fixed (g : AsymptoticRationalGroup.Group)
    (hg : ∀ z : UpperHalfPlane, g • z=z) : g=1 := by
  have hv : (volume : Measure UpperHalfPlane) ≠ 0 := by
    intro hv
    have ha := AsymptoticHyperbolicArea.closed_terminal_area (by norm_num : (0:ℝ)<1)
    rw [hv] at ha
    norm_num at ha
  let : NeZero (volume : Measure UpperHalfPlane) := ⟨hv⟩
  obtain ⟨z,hz⟩ := AsymptoticRationalGroup.ae_free.exists
  exact hz g (hg z)

/-- Failure of a periodized matrix nonidentity test says exactly that the
branch is an integral translate. -/
theorem integer_matrix_periodized_return (b : Branch) (M : IntegerMatrix2) (hdet : M.det ≠ 0)
    (hf : ∀ z : UpperHalfPlane, ((b.label • z : UpperHalfPlane):ℂ)=
      ((M 0 0:ℂ)*(z:ℂ)+M 0 1)/((M 1 0:ℂ)*(z:ℂ)+M 1 1))
    (j : ℤ) (hc : M 1 0=0) (ha : M 1 1=M 0 0+j*M 1 0) (hb : M 0 1+j*M 1 1=0) :
    ∀ z : UpperHalfPlane, ((b.label • z : UpperHalfPlane):ℂ)=(z:ℂ)-(j:ℂ) := by
  have hd : M 1 1≠0 := by
    intro hd
    apply hdet
    simp [Matrix.det_fin_two,hc,hd]
  have hdC : (M 1 1:ℂ)≠0 := by exact_mod_cast hd
  have haC : (M 1 1:ℂ)=(M 0 0:ℂ) := by exact_mod_cast (show M 1 1=M 0 0 by simpa only [hc,mul_zero,add_zero] using ha)
  have hbC : (M 0 1:ℂ)+(j:ℂ)*(M 1 1:ℂ)=0 := by exact_mod_cast hb
  intro z
  rw [hf,hc]
  simp only [Int.cast_zero,zero_mul,zero_add]
  apply (div_eq_iff hdC).mpr
  rw [← haC]
  linear_combination hbC

/-- A literal global integer representative automatically supplies all
periodized nonidentity tests. Empty translation branches are handled by a
vacuous certificate, so they require no impossible arithmetic hypothesis. -/
def retainedBranchGeometry_of_global_matrix (b : Branch) (Y H B : ℝ) (S : Finset ℤ)
    (M : IntegerMatrix2) (hB : 0 ≤ B) (hbound : MatrixEntryBound M B) (hdet : M.det ≠ 0)
    (hf : ∀ z : UpperHalfPlane, ((b.label • z : UpperHalfPlane):ℂ)=
      ((M 0 0:ℂ)*(z:ℂ)+M 0 1)/((M 1 0:ℂ)*(z:ℂ)+M 1 1))
    (hne : b.label ≠ 1) : RetainedBranchGeometry b Y H (B*(H+2)) S := by
  classical
  by_cases he : endpointRegion Y H b=∅
  · exact retainedBranchGeometry_of_empty b Y H _ S he
  refine ⟨M 0 0,M 0 1,M 1 0,M 1 1,?_,?_,?_,?_,?_⟩
  · simpa only [Matrix.det_fin_two] using hdet
  · intro z _
    exact QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hdet z
  · intro z hz
    apply strip_matrix_denominator_bound hB hbound z
    · rw [abs_of_nonneg hz.1.1.1]
      exact hz.1.1.2.le
    · exact hz.1.2.2.le
  · intro z _
    exact hf z
  · intro j _
    by_contra hc
    push Not at hc
    have ht := integer_matrix_periodized_return b M hdet hf j hc.1 hc.2.1 hc.2.2
    by_cases hj : j=0
    · apply hne
      apply rational_label_eq_one_of_fixed
      intro z
      apply UpperHalfPlane.ext
      simpa only [hj,Int.cast_zero,sub_zero] using ht z
    · apply he
      apply retained_endpoint_empty_of_integer_translation b Y H (-j) (neg_ne_zero.mpr hj)
      intro z
      have hr := congrArg Complex.re (ht z)
      simpa [sub_eq_add_neg] using hr

/-- The existing word-height bound now produces the full geometric trace
certificate from a global matrix word, including all periodization tests. -/
def retainedBranchGeometry_of_global_word (b : Branch) (Y H : ℝ) (S : Finset ℤ)
    (l : List IntegerMatrix2) {B : ℝ} (hB : 0 ≤ B)
    (hl : ∀ M ∈ l, MatrixEntryBound M B) (hdet : l.prod.det ≠ 0)
    (hf : ∀ z : UpperHalfPlane, ((b.label • z : UpperHalfPlane):ℂ)=
      ((l.prod 0 0:ℂ)*(z:ℂ)+l.prod 0 1)/((l.prod 1 0:ℂ)*(z:ℂ)+l.prod 1 1))
    (hne : b.label ≠ 1) :
    RetainedBranchGeometry b Y H (((2*B)^l.length)*(H+2)) S :=
  retainedBranchGeometry_of_global_matrix b Y H ((2*B)^l.length) S l.prod
    (by positivity) (matrix_entry_bound_word l hB hl) hdet hf hne

/-- A finite common height bound on literal matrix representatives is enough
for the whole expression certificate; no separate translated-nonidentity or
denominator assumptions are retained. -/
theorem expression_geometry_of_global_matrices (E : Expression) (Y H B : ℝ) (S : Finset ℤ)
    (hB : 0 ≤ B)
    (hm : ∀ b ∈ E, ∃ M : IntegerMatrix2, MatrixEntryBound M B ∧ M.det ≠ 0 ∧
      ∀ z : UpperHalfPlane, ((b.label • z : UpperHalfPlane):ℂ)=
        ((M 0 0:ℂ)*(z:ℂ)+M 0 1)/((M 1 0:ℂ)*(z:ℂ)+M 1 1)) :
    ∀ b ∈ E, b.label ≠ 1 → Nonempty (RetainedBranchGeometry b Y H (B*(H+2)) S) := by
  intro b hb hne
  obtain ⟨M,hbound,hdet,hf⟩ := hm b hb
  exact ⟨retainedBranchGeometry_of_global_matrix b Y H B S M hB hbound hdet hf hne⟩

#print axioms retainedBranchGeometry_of_empty
#print axioms retained_endpoint_empty_of_integer_translation
#print axioms retainedBranchGeometry_of_global_matrix
#print axioms retainedBranchGeometry_of_global_word

end QuantitativeHolomorphic
