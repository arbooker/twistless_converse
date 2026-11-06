module

public import QuantitativeEulerEndpointThresholdBlocksV1
public import QuantitativeEulerEndpointPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSparsePrefix
open Finset QuantitativeEulerEndpointThresholdBlocks
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointProduct
attribute [local instance] Classical.propDecidable

def weight (Good : ℕ → Prop) (p : ℕ) : ℝ := if p.Prime ∧ Good p then 1-1/(p:ℝ) else 1

def value (Good : ℕ → Prop) (n : ℕ) : ℝ :=
  ∏ p∈(n+2).primesBelow.filter Good, (1-1/(p:ℝ))

theorem value_eq_range (Good : ℕ → Prop) (n : ℕ) :
    value Good n=∏ p∈range (n+2),weight Good p := by
  unfold value weight
  rw [Nat.primesBelow_eq_filter_range,filter_filter,prod_filter]

theorem weight_pos (Good : ℕ → Prop) (p : ℕ) : 0<weight Good p := by
  unfold weight
  split_ifs with hp
  · have hp1 : (1:ℝ)<p := by exact_mod_cast hp.1.one_lt
    have hi : 1/(p:ℝ)<1 := (div_lt_one (by linarith)).mpr hp1
    linarith
  · norm_num

theorem weight_le_one (Good : ℕ → Prop) (p : ℕ) : weight Good p≤1 := by
  unfold weight
  split_ifs
  · exact sub_le_self _ (by positivity)
  · rfl

theorem value_pos (Good : ℕ → Prop) (n : ℕ) : 0<value Good n := by
  rw [value_eq_range]
  exact prod_pos (fun p _ => weight_pos Good p)

theorem value_zero (Good : ℕ → Prop) : value Good 0=1 := by
  rw [value_eq_range]
  norm_num [weight,prod_range_succ]

theorem value_succ (Good : ℕ → Prop) (n : ℕ) :
    value Good (n+1)=value Good n*weight Good (n+2) := by
  rw [value_eq_range,value_eq_range,show n+1+2=(n+2)+1 by omega,prod_range_succ]

theorem value_antitone (Good : ℕ → Prop) : Antitone (value Good) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [value_succ]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (weight_le_one Good (n+2)) (value_pos Good n).le

theorem value_step (Good : ℕ → Prop) (n : ℕ) :
    value Good n*(1-1/((n:ℝ)+2))≤value Good (n+1) := by
  rw [value_succ]
  apply mul_le_mul_of_nonneg_left _ (value_pos Good n).le
  unfold weight
  split_ifs
  · simp only [Nat.cast_add,Nat.cast_ofNat,le_refl]
  · exact sub_le_self _ (by positivity)

def ofBound (Good : ℕ → Prop) (C : ℝ) (hC : 0<C)
    (hupper : ∀ n, value Good n≤C/Real.log ((n:ℝ)+2)) : Prefix where
  value := value Good
  zero := value_zero Good
  antitone := value_antitone Good
  step := value_step Good
  constant := C
  constant_pos := hC
  upper := hupper

/-- Summable non-detecting primes give prefix data for the SAME actual
preparation. No density, reciprocal-summability or product premise remains. -/
theorem prepared_bound (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ n, value (prepared N hN excluded threshold).Good n≤C/Real.log ((n:ℝ)+2) := by
  obtain ⟨C,hC,hbound⟩ := prepared_endpoint_product N hN excluded threshold
  refine ⟨C,hC,?_⟩
  intro n
  have h := hbound (n+1) (by omega)
  have he : value (prepared N hN excluded threshold).Good n=
      ∏ p∈(n+2).primesBelow.filter (prepared N hN excluded threshold).Good,
        (1-(1-1/(p:ℝ))/((p:ℝ)-1)) := by
    apply prod_congr rfl
    intro p hp
    exact (variable_tolerance_factor (Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1)).symm
  rw [he]
  convert h using 1
  congr 2
  push_cast
  ring

def preparedPrefix (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ) : Prefix :=
  ofBound (prepared N hN excluded threshold).Good
    (prepared_bound N hN excluded threshold).choose
    (prepared_bound N hN excluded threshold).choose_spec.1
    (prepared_bound N hN excluded threshold).choose_spec.2

theorem preparedPrefix_value (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold n : ℕ) :
    (preparedPrefix N hN excluded threshold).value n=value (prepared N hN excluded threshold).Good n := rfl

#print axioms value_step
#print axioms value_antitone
#print axioms prepared_bound
#print axioms preparedPrefix_value
end QuantitativeEulerEndpointSparsePrefix
