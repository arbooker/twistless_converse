module

public import QuantitativeEulerEndpointShiftedClassesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset QuantitativeArithmetic
attribute [local instance] Classical.propDecidable

/-- Reciprocal exceptional mass for the prime product, zero off the primes. -/
def badPrimeLoss (P : ℕ → Prop) (p : ℕ) : ℝ :=
  if p.Prime ∧ ¬P p then 1/((p : ℝ)-1) else 0

theorem badPrimeLoss_nonneg (P : ℕ → Prop) (p : ℕ) : 0≤badPrimeLoss P p := by
  unfold badPrimeLoss
  split_ifs with hp
  · have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.1.two_le
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

/-- Finite intersections and finite exclusions preserve summable
exceptional mass. This is stronger than relative prime density one. -/
theorem badPrimeLoss_finite_intersection {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop) (hs : ∀ i, Summable (badPrimeLoss (P i))) (E : Finset ℕ) :
    Summable (badPrimeLoss (fun p => (∀ i, P i p) ∧ p∉E)) := by
  let e := badPrimeLoss (fun p => p∉E)
  have hes : Summable e := summable_of_ne_finset_zero (s := E) (by
    intro p hp
    simp [e,badPrimeLoss,hp])
  have hss (S : Finset ι) : Summable (fun p => ∑ i∈S, badPrimeLoss (P i) p) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => simpa only [sum_insert hi] using (hs i).add ih
  apply Summable.of_nonneg_of_le (badPrimeLoss_nonneg _) (fun p => ?_) (hes.add (hss univ))
  by_cases hp : p.Prime ∧ ¬((∀ i, P i p) ∧ p∉E)
  · by_cases hpE : p∈E
    · have he : e p=1/((p : ℝ)-1) := by simp [e,badPrimeLoss,hp.1,hpE]
      rw [badPrimeLoss,ite_eq_left hp,he]
      exact le_add_of_nonneg_right (sum_nonneg (fun i _ => badPrimeLoss_nonneg (P i) p))
    · have hn : ¬∀ i, P i p := fun h => hp.2 ⟨h,hpE⟩
      obtain ⟨i,hi⟩ := not_forall.mp hn
      have hsum := single_le_sum (fun j _ => badPrimeLoss_nonneg (P j) p) (mem_univ i)
      have he : e p=0 := by simp [e,badPrimeLoss,hpE]
      have hiP : badPrimeLoss (P i) p=1/((p : ℝ)-1) := by simp [badPrimeLoss,hp.1,hi]
      rw [badPrimeLoss,ite_eq_left hp,he,zero_add]
      exact hiP ▸ hsum
  · rw [badPrimeLoss,ite_eq_right hp]
    exact add_nonneg (badPrimeLoss_nonneg _ p)
      (sum_nonneg (fun i _ => badPrimeLoss_nonneg (P i) p))

/-- Summability for the exact finite-family good set consumed by the
polynomial certificate construction, with exclusions and a lower cutoff. -/
theorem simultaneous_shifted_classes_exception_summable {ι : Type*} [Fintype ι]
    (Q M : ι → ℕ) (hQ : ∀ i, 0<Q i) (hM : ∀ i, 0<M i)
    (S : Finset ℕ) (bound : ℕ) :
    Summable (badPrimeLoss (fun p =>
      (∀ i, ShiftedDivisorClasses (Q i) (M i) p) ∧ p∉S ∧ bound<p)) := by
  have hs (i : ι) : Summable (badPrimeLoss (ShiftedDivisorClasses (Q i) (M i))) := by
    let : NeZero (M i) := ⟨(hM i).ne'⟩
    exact shiftedDivisorClasses_exception_summable (Q i) (M i) (hQ i)
  have h := badPrimeLoss_finite_intersection
    (fun i => ShiftedDivisorClasses (Q i) (M i)) hs (S ∪ range (bound+1))
  apply h.congr
  intro p
  simp only [badPrimeLoss,mem_union,mem_range,not_or,not_lt,Nat.add_one_le_iff]
  split_ifs <;> rfl

#print axioms badPrimeLoss_finite_intersection
#print axioms simultaneous_shifted_classes_exception_summable
end QuantitativeEulerEndpointAP
