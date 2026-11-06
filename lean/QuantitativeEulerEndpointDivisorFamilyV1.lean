module

public import QuantitativeEulerEndpointAPSummabilityV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset
attribute [local instance] Classical.propDecidable

def exceptionLoss {M : ℕ} (a : ZMod M) (Q p : ℕ) : ℝ :=
  if divisorException a Q p then 1/((p : ℝ)-1) else 0

theorem exceptionLoss_nonneg {M : ℕ} (a : ZMod M) (Q p : ℕ) : 0≤exceptionLoss a Q p := by
  unfold exceptionLoss
  split_ifs with hp
  · have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.1.two_le
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

/-- The denominator p-1 used by the fresh-prime product has summable
exceptional mass, as does the usual reciprocal p. -/
theorem exceptionLoss_summable {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (Q : ℕ) (hQ : 0<Q) : Summable (exceptionLoss a Q) := by
  apply Summable.of_nonneg_of_le (exceptionLoss_nonneg a Q) (fun p => ?_)
    ((divisorException_reciprocal_summable a ha Q hQ).mul_left 2)
  unfold exceptionLoss reciprocalIndicator
  split_ifs with hp
  · rw [mul_one_div]
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.1.two_le
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  · simp

def divisorGoodFamily {ι : Type*} (M : ι → ℕ) (a : ∀ i, ZMod (M i))
    (Q : ι → ℕ) (E : Finset ℕ) (p : ℕ) : Prop :=
  p∉E ∧ ∀ i, ∃ d : ℕ, d∣p-Q i ∧ 0<d ∧ (d : ZMod (M i))=a i

/-- Finite intersections of the actual shifted-divisor conditions, and
arbitrary finite exclusions, retain summable exceptional reciprocal mass. -/
theorem divisorGoodFamily_exception_summable {ι : Type*} [Fintype ι]
    (M : ι → ℕ) [∀ i, NeZero (M i)] (a : ∀ i, ZMod (M i)) (ha : ∀ i, IsUnit (a i))
    (Q : ι → ℕ) (hQ : ∀ i, 0<Q i) (E : Finset ℕ) :
    Summable (fun p : ℕ => if p.Prime ∧ ¬divisorGoodFamily M a Q E p then 1/((p : ℝ)-1) else 0) := by
  let b : ℕ → ℝ := fun p => if p.Prime ∧ ¬divisorGoodFamily M a Q E p then 1/((p : ℝ)-1) else 0
  let e : ℕ → ℝ := fun p => if p.Prime ∧ p∈E then 1/((p : ℝ)-1) else 0
  have he0 (p : ℕ) : 0≤e p := by
    dsimp [e]
    split_ifs with hp
    · have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.1.two_le
      exact div_nonneg (by norm_num) (by linarith)
    · exact le_rfl
  have hes : Summable e := summable_of_ne_finset_zero (s := E) (by intro p hp; simp [e,hp])
  have hss (S : Finset ι) : Summable (fun p => ∑ i∈S, exceptionLoss (a i) (Q i) p) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simpa only [sum_insert hi] using (exceptionLoss_summable (a i) (ha i) (Q i) (hQ i)).add ih
  have hs := hes.add (hss univ)
  have hb0 (p : ℕ) : 0≤b p := by
    dsimp [b]
    split_ifs with hp
    · have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.1.two_le
      exact div_nonneg (by norm_num) (by linarith)
    · exact le_rfl
  apply Summable.of_nonneg_of_le hb0 (fun p => ?_) hs
  by_cases hp : p.Prime ∧ ¬divisorGoodFamily M a Q E p
  · by_cases hpE : p∈E
    · simp only [b,e,hp,hpE,and_self,ite_true]
      exact le_add_of_nonneg_right (sum_nonneg (fun i _ => exceptionLoss_nonneg (a i) (Q i) p))
    · have hn : ¬∀ i, ∃ d : ℕ, d∣p-Q i ∧ 0<d ∧ (d : ZMod (M i))=a i := by
        intro hi
        exact hp.2 ⟨hpE,hi⟩
      obtain ⟨i,hi⟩ := not_forall.mp hn
      have hbad : divisorException (a i) (Q i) p := ⟨hp.1,hi⟩
      have hsum := single_le_sum (fun j _ => exceptionLoss_nonneg (a j) (Q j) p) (mem_univ i)
      simpa only [b,e,hp,hp.1,hpE,and_self,and_false,not_false_eq_true,ite_true,ite_false,zero_add,exceptionLoss,hbad] using hsum
  · have hsum0 := sum_nonneg (fun i (_ : i∈(univ : Finset ι)) => exceptionLoss_nonneg (a i) (Q i) p)
    simpa only [b,hp,ite_false] using add_nonneg (he0 p) hsum0

/-- The exponent-one arithmetic prime product for every finite family of
positive shifted-divisor/unit-class conditions is now unconditional.
This is an arithmetic ingredient, not the final holomorphic counting theorem. -/
theorem divisorGoodFamily_endpoint_product {ι : Type*} [Fintype ι]
    (M : ι → ℕ) [∀ i, NeZero (M i)] (a : ∀ i, ZMod (M i)) (ha : ∀ i, IsUnit (a i))
    (Q : ι → ℕ) (hQ : ∀ i, 0<Q i) (E : Finset ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 0<n →
      (∏ p∈(n+1).primesBelow.filter (divisorGoodFamily M a Q E),
        (1-(1-1/(p : ℝ))/((p : ℝ)-1)))≤C/Real.log (n+1 : ℝ) :=
  QuantitativeEulerEndpointProduct.endpoint_product_of_summable_exceptions
    (divisorGoodFamily M a Q E) (divisorGoodFamily_exception_summable M a ha Q hQ E)

#print axioms exceptionLoss_summable
#print axioms divisorGoodFamily_exception_summable
#print axioms divisorGoodFamily_endpoint_product
end QuantitativeEulerEndpointAP
