module

public import QuantitativeArithmeticRamifiedFullTraceV1
public import QuantitativeArithmeticRetainedHolomorphicSpaceV1
public import FinitenessOriginalDiskIndependenceV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeArithmeticRamifiedOriginalBridge

open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  FinitenessOriginalDiskIndependence FinitenessHolomorphicSpace
  QuantitativeArithmeticRamifiedFullTrace QuantitativeArithmeticRetainedHolomorphicSpace
  QuantitativeArithmeticRetainedReconstruction

theorem lift_representative (N k : ℕ) (f : S N k) {z : ℂ} (hz : 0 < z.im) :
    lift (representative N k f).val z = fourier (fullCoefficients f.val k) z :=
  disk_eq_fourier _ hz

theorem original_complete_laws {N m : ℕ} (hm : 0 < m) (f : S N (2 * m)) :
    CompleteLaws N.primeFactors (multiplier f.val m)
      (lift (representative N (2 * m) f).val) := by
  intro p hp z hz
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpN : p ∣ N := (Nat.mem_primeFactors.mp hp).2.1
  have htrace : completeTwist (lift (representative N (2 * m) f).val) p z =
      completeTwist (fourier (fullCoefficients f.val (2 * m))) p z := by
    unfold completeTwist
    apply Finset.sum_congr rfl
    intro a _
    apply lift_representative
    simpa only [Complex.add_im, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_im, add_zero] using hz
  rw [htrace, lift_representative N (2 * m) f (dilation_height hprime.pos hz)]
  exact original_complete_even f.property.toEulerData hprime hpN hm hz

/-- Every literal original solution has one of the finite ramified sign
patterns, and its canonical holomorphic disk representative obeys those
complete-row laws. Neither spanning nor a converse theorem is assumed. -/
theorem original_sign_cover {N m : ℕ} (hm : 0 < m) (f : S N (2 * m)) :
    ∃ b : ℕ → ℂ,
      (∀ p ∈ N.primeFactors, b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) ∧
      CompleteLaws N.primeFactors b (lift (representative N (2 * m) f).val) := by
  refine ⟨multiplier f.val m, ?_, original_complete_laws hm f⟩
  intro p hp
  exact multiplier_values f.property.toEulerData (Nat.mem_primeFactors.mp hp).1
    (Nat.mem_primeFactors.mp hp).2.1 m

#print axioms lift_representative
#print axioms original_complete_laws
#print axioms original_sign_cover

end QuantitativeArithmeticRamifiedOriginalBridge
