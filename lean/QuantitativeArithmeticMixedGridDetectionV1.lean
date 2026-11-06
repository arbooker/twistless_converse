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

/-- Grid reconstruction from selected legal rows at good labels and complete
prime rows at all remaining labels. This replaces the admissible-level
detector without any field or characteristic restrictions. -/
theorem mixed_grid_detect {K : Type*} [AddCommMonoid K] {G v J : ℕ}
    (hG : 0 < G) (hv : 0 < v) (hJv : 2*J < v)
    (good : Fin G → Prop) [DecidablePred good]
    (r w c p : Fin G → ℕ)
    (hw : ∀ a, good a → 0 < w a)
    (hvw : ∀ a, good a → v = r a*w a)
    (hD : ∀ a, good a → labelModulus a*w a ∣ G*v)
    (hJw : ∀ a, good a → 2*J < w a)
    (hc : ∀ a, good a → Nat.Coprime (labelModulus a) (r a))
    (ha : ∀ a, good a → Nat.ModEq (labelModulus a) (r a*a.val) (c a))
    (hp : ∀ a, ¬ good a → (p a).Prime)
    (hpG : ∀ a, ¬ good a → p a ∣ G)
    (hpa : ∀ a, ¬ good a → ¬ p a ∣ labelOrder a)
    (f : ℤ → K) (hcyc : Cyclic (G*v) f)
    (hsupport : ∀ j : Fin (G*v), j ∉ Set.range (gridIndex hG hv J) → f j.val = 0)
    (hrows : ∀ a, good a → ∀ t : Offsets J,
      cosetSum (G*v) (labelModulus a*w a) ((c a : ℤ)*w a+t.val) f = 0)
    (hprimes : ∀ a, ¬ good a → ∀ t : Offsets J,
      cosetSum (G*v) ((G/p a)*v) ((a.val : ℤ)*v+t.val) f = 0) : f = 0 := by
  have hgrid : ∀ x : Fin G × Offsets J, f (gridIndex hG hv J x).val = 0 := by
    intro x
    let g := fun z : Fin G => f (gridIndex hG hv J (z,x.2)).val
    have hg : g = 0 := mixed_label_detect hG good p hp hpG hpa g (by
        intro a hgood
        have he := selected_coset_sum hG hv (hw a hgood) (hvw a hgood) (hD a hgood)
          hJv (hJw a hgood) a x.2 (hc a hgood) (ha a hgood) f hsupport
        rw [restricted_labelHit] at he
        exact he.symm.trans (hrows a hgood x.2)) (by
        intro a hbad
        exact (prime_coset_sum hG hv (hpG a hbad) hJv a x.2 f hsupport).symm.trans
          (hprimes a hbad x.2))
    exact congrFun hg x.1
  have hfin : ∀ j : Fin (G*v), f j.val = 0 := by
    intro j
    by_cases hj : j ∈ Set.range (gridIndex hG hv J)
    · obtain ⟨x,rfl⟩ := hj
      exact hgrid x
    · exact hsupport j hj
  funext j
  change f j = 0
  rw [←cyclic_residue (Nat.mul_pos hG hv) f hcyc j]
  exact hfin _

#print axioms prime_coset_sum
#print axioms mixed_grid_detect

end QuantitativeArithmeticMixedGridDetection
