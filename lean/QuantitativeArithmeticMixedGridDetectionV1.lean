module

public import QuantitativeArithmeticMixedLabelDetectionV1

@[expose] public section

namespace QuantitativeArithmeticMixedGridDetection

open SpanningTraceAlgebra SpanningCyclicCoordinates CompleteRowCosets
  GridCarrier GridRestrictedRows GridLabelDetection GridActualIncidence
  GridSupportedDetection QuantitativeArithmeticMixedLabelDetection

theorem restricted_primeHit {K : Type*} [AddCommMonoid K] {G p : ℕ}
    (a : Fin G) (f : Fin G → K) :
    restrictedSum (fun z : Fin G => Nat.ModEq (G / p) z.val a.val) f =
      ∑ z ∈ primeHit p a, f z := by
  classical
  simp only [restrictedSum, primeHit, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

/-- A complete prime row restricts to a prime label row on each horizontal
slice of the grid. There is no bound on the translate `a*v+t`. -/
theorem prime_coset_sum {K : Type*} [AddCommMonoid K] {G v J p : ℕ}
    (hG : 0 < G) (hv : 0 < v) (hpG : p ∣ G) (hJv : 2*J < v)
    (a : Fin G) (t : Offsets J) (f : ℤ → K)
    (hf : ∀ j : Fin (G*v), j ∉ Set.range (gridIndex hG hv J) → f j.val = 0) :
    cosetSum (G*v) ((G/p)*v) ((a.val : ℤ)*v+t.val) f =
      ∑ z ∈ primeHit p a, f (gridIndex hG hv J (z,t)).val := by
  have hD : (G/p)*v ∣ G*v := Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hpG) v
  have he := selected_coset_sum (m:=G/p) (r:=1) (c:=a.val)
    hG hv hv (by simp) hD hJv hJv a t (by simp) (by simpa only [one_mul] using Nat.ModEq.refl a.val) f hf
  rw [restricted_primeHit] at he
  exact he

#print axioms prime_coset_sum

end QuantitativeArithmeticMixedGridDetection
