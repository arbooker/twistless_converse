module

public import SpanningCriterionLabelDetectionV1
public import QuantitativeArithmeticMixedGridDetectionV1

@[expose] public section

namespace SpanningCriterionGridDetection

open SpanningTraceAlgebra SpanningCyclicCoordinates CompleteRowCosets
  GridCarrier GridRestrictedRows GridLabelDetection GridActualIncidence
  GridSupportedDetection QuantitativeArithmeticMixedLabelDetection
  QuantitativeArithmeticMixedGridDetection

theorem mixed_grid_detect {K : Type*} [AddCommMonoid K] {G v J : ℕ}
    (hG : 0 < G) (hv : 0 < v) (hJv : 2*J < v)
    (good : Fin G → Prop) [DecidablePred good]
    (r w c p : Fin G → ℕ)
    (hw : ∀ a, 2 < labelOrder a → good a → 0 < w a)
    (hvw : ∀ a, 2 < labelOrder a → good a → v = r a*w a)
    (hD : ∀ a, 2 < labelOrder a → good a → labelModulus a*w a ∣ G*v)
    (hJw : ∀ a, 2 < labelOrder a → good a → 2*J < w a)
    (hc : ∀ a, 2 < labelOrder a → good a → Nat.Coprime (labelModulus a) (r a))
    (ha : ∀ a, 2 < labelOrder a → good a → Nat.ModEq (labelModulus a) (r a*a.val) (c a))
    (hp : ∀ a, 2 < labelOrder a → ¬ good a → (p a).Prime)
    (hpG : ∀ a, 2 < labelOrder a → ¬ good a → p a ∣ G)
    (hpa : ∀ a, 2 < labelOrder a → ¬ good a → ¬ p a ∣ labelOrder a)
    (f : ℤ → K) (hcyc : Cyclic (G*v) f)
    (hsupport : ∀ j : Fin (G*v), j ∉ Set.range (gridIndex hG hv J) → f j.val = 0)
    (hrows : ∀ a, 2 < labelOrder a → good a → ∀ t : Offsets J,
      cosetSum (G*v) (labelModulus a*w a) ((c a : ℤ)*w a+t.val) f = 0)
    (hprimes : ∀ a, 2 < labelOrder a → ¬ good a → ∀ t : Offsets J,
      cosetSum (G*v) ((G/p a)*v) ((a.val : ℤ)*v+t.val) f = 0)
    (hzero : ∀ t : Offsets J, f t.val = 0)
    (hpair : ∀ a : Fin G, 2*a.val = G → ∀ t : Offsets J,
      f t.val + f ((a.val : ℤ)*v+t.val) = 0) : f = 0 := by
  have hgrid : ∀ x : Fin G × Offsets J, f (gridIndex hG hv J x).val = 0 := by
    intro x
    let g := fun z : Fin G => f (gridIndex hG hv J (z,x.2)).val
    have hg : g = 0 := SpanningCriterionLabelDetection.mixed_label_detect hG good p hp hpG hpa g (by
        intro a hahi hgood
        have he := selected_coset_sum hG hv (hw a hahi hgood) (hvw a hahi hgood) (hD a hahi hgood)
          hJv (hJw a hahi hgood) a x.2 (hc a hahi hgood) (ha a hahi hgood) f hsupport
        rw [restricted_labelHit] at he
        exact he.symm.trans (hrows a hahi hgood x.2)) (by
        intro a hahi hbad
        exact (prime_coset_sum hG hv (hpG a hahi hbad) hJv a x.2 f hsupport).symm.trans
          (hprimes a hahi hbad x.2))
      (by simpa only [g,grid_evaluation hG hv f hcyc,Nat.cast_zero,zero_mul,zero_add]
            using hzero x.2)
      (by intro a haa
          simpa only [g,grid_evaluation hG hv f hcyc,Nat.cast_zero,zero_mul,zero_add]
            using hpair a haa x.2)
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


#print axioms mixed_grid_detect

end SpanningCriterionGridDetection
