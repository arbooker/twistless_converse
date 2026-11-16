module

public import QuantitativeHolomorphicObservationMatricesV1
public import QuantitativeHolomorphicMatrixExpressionV1
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch AsymptoticRationalBranches AsymptoticRationalGroup
open AsymptoticRationalFreeness QuantitativeHolomorphic
namespace QuantitativeMaass

/-- Every actual positive rational projective label admits a global
integer matrix representative; the denominator is cleared simultaneously. -/
theorem rational_label_integer_action (g : AsymptoticRationalGroup.Group) :
    ∃ M : IntegerMatrix2,IntegerAction g M := by
  obtain ⟨q,hq⟩ := g.val.property
  have hpos := representative_positive g hq
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : Fin 2×Fin 2 => q ij.1 ij.2)
  choose A hA using hd
  let M : IntegerMatrix2 := fun i j => A (i,j)
  have hdZ : (d:ℤ)≠0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdQ : ((d:ℤ):ℚ)≠0 := by exact_mod_cast hdZ
  have hm (i j : Fin 2) : (M i j:ℚ)=((d:ℤ):ℚ)*q i j := by
    simpa only [M,Algebra.smul_def,algebraMap_int_eq,Int.coe_castRingHom] using hA (i,j)
  have hdet : (M.det:ℚ)=((d:ℤ):ℚ)^2*(q.val.det) := by
    simp only [Matrix.det_fin_two,Int.cast_sub,Int.cast_mul,hm]
    ring
  have hqdet : q.val.det≠0 := Units.ne_zero q.det
  have hM : M.det≠0 := by
    intro hz
    rw [hz,Int.cast_zero] at hdet
    exact (mul_ne_zero (pow_ne_zero 2 hdQ) hqdet) hdet.symm
  have he : ofMatrix q hpos=g := by
    apply Subtype.ext
    apply Subtype.ext
    exact hq
  refine ⟨M,?_⟩
  rw [←he]
  exact integerAction_of_scaled_rational_entries q hpos M hM ((d:ℤ):ℚ) hdQ hm

/-- A fixed finite integer matrix has a positive common entry bound. -/
theorem integer_matrix_entry_bound_exists (M : IntegerMatrix2) :
    ∃ B : ℝ,1≤B ∧ MatrixEntryBound M B := by
  let B : ℝ := 1+∑ i,∑ j,|(M i j:ℝ)|
  have hs : 0≤∑ i,∑ j,|(M i j:ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  refine ⟨B,by dsimp only [B];linarith,?_⟩
  intro i j
  have h1 : |(M i j:ℝ)|≤∑ k,|(M i k:ℝ)| :=
    Finset.single_le_sum (f := fun k => |(M i k:ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ k,|(M i k:ℝ)|)≤∑ l,∑ k,|(M l k:ℝ)| :=
    Finset.single_le_sum (f := fun l => ∑ k,|(M l k:ℝ)|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  dsimp only [B]
  linarith

/-- Every fixed common rational expression has a finite integer height
bound. For growing expressions this lemma is used only on the fixed
base words, followed by the quantitative composition and power bounds. -/
theorem expression_matrix_bound_exists (E : Expression) :
    ∃ B : ℝ,1≤B ∧ ExpressionMatrixBound E B := by
  induction E with
  | nil => exact ⟨1,le_rfl,fun _ hb => False.elim (List.not_mem_nil hb)⟩
  | cons b E ih =>
    obtain ⟨M,hM⟩ := rational_label_integer_action b.label
    obtain ⟨C,hC,hMC⟩ := integer_matrix_entry_bound_exists M
    obtain ⟨B,hB,hE⟩ := ih
    refine ⟨max C B,hC.trans (le_max_left _ _),?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with he|he
    · subst a
      exact ⟨M,hM,fun i j => (hMC i j).trans (le_max_left _ _)⟩
    · exact hE.mono (le_max_right _ _) a he

#print axioms rational_label_integer_action
#print axioms integer_matrix_entry_bound_exists
#print axioms expression_matrix_bound_exists
end QuantitativeMaass
