module

public import QuantitativeEulerEndpointDivisorFamilyV1
public import QuantitativeArithmeticDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset QuantitativeArithmetic
attribute [local instance] Classical.propDecidable

/-- Summable exceptional reciprocal mass is preserved on enlarging the
good-prime set. Only prime inputs to the implication are needed. -/
theorem summable_exception_mono (P R : ℕ → Prop)
    (hP : Summable (fun p : ℕ => if p.Prime ∧ ¬P p then 1/((p : ℝ)-1) else 0))
    (hPR : ∀ p : ℕ, p.Prime → P p → R p) :
    Summable (fun p : ℕ => if p.Prime ∧ ¬R p then 1/((p : ℝ)-1) else 0) := by
  have hnonneg (p : ℕ) (hp : p.Prime) : 0≤1/((p : ℝ)-1) := by
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
    exact div_nonneg (by norm_num) (by linarith)
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hP
  · split_ifs with hp
    · exact hnonneg p hp.1
    · exact le_rfl
  · by_cases hp : p.Prime ∧ ¬R p
    · have hbad : p.Prime ∧ ¬P p := ⟨hp.1,fun h => hp.2 (hPR p hp.1 h)⟩
      simp only [hp,hbad]
      exact le_rfl
    · simp only [hp,ite_false]
      split_ifs with hbad
      · exact hnonneg p hbad.1
      · exact le_rfl

/-- The natural-number divisor condition agrees with the project's literal
integer-shift predicate above the fixed shift; finitely many smaller inputs
are excluded explicitly. -/
theorem good_unit_family_implies_shifted_classes (M : ℕ) [NeZero M] (Q p : ℕ)
    (hgood : divisorGoodFamily (fun _ : (ZMod M)ˣ => M) (fun u => (u : ZMod M))
      (fun _ => Q) (range (Q+1)) p) : ShiftedDivisorClasses Q M p := by
  have hQp : Q≤p := by
    have h := hgood.1
    simp only [mem_range,not_lt] at h
    omega
  intro a _ hacop
  obtain ⟨d,hddiv,hdpos,hdclass⟩ := hgood.2 (ZMod.unitOfCoprime a hacop)
  refine ⟨d,hdpos,?_,?_⟩
  · have hdi : (d : ℤ)∣((p-Q : ℕ) : ℤ) := by exact_mod_cast hddiv
    rwa [Nat.cast_sub hQp] at hdi
  · exact (ZMod.natCast_eq_natCast_iff d a M).mp hdclass

/-- Summability for the exact ShiftedDivisorClasses predicate already used
by the prepared matrix-certificate construction, including integer shifts. -/
theorem shiftedDivisorClasses_exception_summable (Q M : ℕ) [NeZero M] (hQ : 0<Q) :
    Summable (fun p : ℕ => if p.Prime ∧ ¬ShiftedDivisorClasses Q M p then
      1/((p : ℝ)-1) else 0) := by
  have hs := divisorGoodFamily_exception_summable
    (fun _ : (ZMod M)ˣ => M) (fun u => (u : ZMod M)) (fun u => u.isUnit)
    (fun _ => Q) (fun _ => hQ) (range (Q+1))
  exact summable_exception_mono _ _ hs (fun p _ h => good_unit_family_implies_shifted_classes M Q p h)

/-- Exact endpoint arithmetic product for the existing all-unit-class
shifted-divisor condition. The summability premise has been proved. -/
theorem shiftedDivisorClasses_endpoint_product (Q M : ℕ) [NeZero M] (hQ : 0<Q) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 0<n →
      (∏ p∈(n+1).primesBelow.filter (ShiftedDivisorClasses Q M),
        (1-(1-1/(p : ℝ))/((p : ℝ)-1)))≤C/Real.log (n+1 : ℝ) :=
  QuantitativeEulerEndpointProduct.endpoint_product_of_summable_exceptions
    (ShiftedDivisorClasses Q M) (shiftedDivisorClasses_exception_summable Q M hQ)

#print axioms shiftedDivisorClasses_exception_summable
#print axioms shiftedDivisorClasses_endpoint_product
end QuantitativeEulerEndpointAP
