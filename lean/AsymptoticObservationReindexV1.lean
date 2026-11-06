module

public import AsymptoticRepeatedObservationsV1
public import AsymptoticConcreteCountUpperV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservationStack

open ContinuousLinearMap

variable {ι κ E J : Type*} [Fintype ι] [Fintype κ]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem reindex_stack_gram (L : κ → E →L[ℂ] J) (e : ι ≃ κ) :
    (stack (fun i => L (e i))).adjoint.comp (stack (fun i => L (e i)))=
      (stack L).adjoint.comp (stack L) := by
  rw [stack_gram,stack_gram]
  exact e.sum_comp (fun i => (L i).adjoint.comp (L i))

#print axioms reindex_stack_gram

end AsymptoticObservationStack

namespace AsymptoticRegularObservation

open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem positive_reindex (hN : 0<N) (P : Parameters A) (r : κ → Row N)
    (s : κ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : ι ≃ κ) (χ : Sector N) (z : ℍ) :
    positive A hN P (fun i => r (e i)) (fun i => s (e i)) (fun i => hs (e i)) χ z=
      positive A hN P r s hs χ z := by
  unfold positive
  apply AsymptoticObservation.operator_eq_of_gram
  exact AsymptoticObservationStack.reindex_stack_gram
    (fun i => AsymptoticRegularObservationRows.row hN (r i) χ (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) e

#print axioms positive_reindex

end AsymptoticRegularObservation

namespace AsymptoticCompactObservationCount

open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem totalRegularTrace_reindex (hN : 0<N) (P : Parameters A) (r : κ → Row N)
    (s : κ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : ι ≃ κ) :
    totalRegularTrace A hN P (fun i => r (e i)) (fun i => s (e i)) (fun i => hs (e i))=
      totalRegularTrace A hN P r s hs := by
  unfold totalRegularTrace
  congr 1
  funext χ
  exact congrArg (fun B => (AsymptoticRegularTrace.trace MeasureTheory.volume B).toReal)
    (funext (AsymptoticRegularObservation.positive_reindex A hN P r s hs e χ))

#print axioms totalRegularTrace_reindex

end AsymptoticCompactObservationCount
