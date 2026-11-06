module

public import AsymptoticRegularObservationPositiveV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservationStack

open ContinuousLinearMap InnerProductSpace

variable {ι E J : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The finite stack uses the Hilbert direct-sum norm, so its Gram
operator is exactly the sum of its row Gram operators. -/
theorem stack_gram (L : ι → E →L[ℂ] J) :
    (stack L).adjoint.comp (stack L)=∑ i,(L i).adjoint.comp (L i) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [comp_apply,adjoint_inner_left,PiLp.inner_apply,stack_apply,
    _root_.sum_apply,sum_inner]

#print axioms stack_gram

end AsymptoticObservationStack

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticSectorSigns

variable {ι : Type*} [Fintype ι]

noncomputable def gram {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  (observations hN r s hs hε t e z).adjoint.comp (observations hN r s hs hε t e z)

theorem gram_eq_sum {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) (z : ℍ) :
    gram hN r s hs hε t e z=∑ i,
      (AsymptoticRegularObservationRows.row hN (r i) e (hs i) hε t z).adjoint.comp
        (AsymptoticRegularObservationRows.row hN (r i) e (hs i) hε t z) :=
  AsymptoticObservationStack.stack_gram _

theorem gram_covariant {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) : Covariant (gram hN r s hs hε t e) := by
  have he : gram hN r s hs hε t e=fun z => ∑ i,
      (AsymptoticRegularObservationRows.row hN (r i) e (hs i) hε t z).adjoint.comp
        (AsymptoticRegularObservationRows.row hN (r i) e (hs i) hε t z) :=
    funext (gram_eq_sum hN r s hs hε t e)
  rw [he]
  apply covariant_finsetSum
  intro i _
  have hc := AsymptoticRegularObservationRows.row_covariant hN (r i) e (hs i) hε t
  exact covariant_comp _ _ (covariant_adjoint _ hc) hc

theorem gram_matrix_measurable {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (gram hN r s hs hε t e z) a b) := by
  simp only [gram_eq_sum]
  apply matrix_finsetSum_measurable
  intro i _
  apply matrix_comp_measurable
  · intro c d
    simp only [matrix_adjoint]
    exact Complex.continuous_conj.measurable.comp
      (AsymptoticRegularObservationRows.row_matrix_measurable hN (r i) e (hs i) hε t d c)
  · exact AsymptoticRegularObservationRows.row_matrix_measurable hN (r i) e (hs i) hε t

#print axioms gram_eq_sum
#print axioms gram_covariant
#print axioms gram_matrix_measurable

end AsymptoticRegularObservation
