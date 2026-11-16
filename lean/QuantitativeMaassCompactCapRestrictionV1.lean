module

public import QuantitativeMaassCompactCapCancellationV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane

namespace QuantitativeMaass

/-- A finite sum of inverse-band multipliers has the sum of their literal
coefficients as its almost-everywhere representative. -/
theorem LogBands.compact_inverse_sum_coeFn {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (l : α → ℝ) (hl : Measurable l) (S : Finset ℤ)
    (f : Lp ℂ 2 μ) :
    (∑ n ∈ S, inverse μ l hl n) f =ᵐ[μ]
      (fun x => (∑ n ∈ S, inverseCoefficient l n x) * f x) := by
  classical
  simp only [sum_apply]
  have hs := Lp.coeFn_finsetSum S (fun n => inverse μ l hl n f)
  have hi : ∀ᵐ x ∂μ, ∀ n ∈ S,
      inverse μ l hl n f x = inverseCoefficient l n x * f x :=
    (eventually_all_finite S.finite_toSet).mpr (fun n _ => inverse_coeFn μ l hl n f)
  filter_upwards [hs, hi] with x hx hi
  rw [hx, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun n hn => hi n hn)

/-- On a region above the propagated lower cutoff, the bounded inverse
cap recovers the unweighted representative. No global inverse-cap domain
or integrability assumption on the unweighted representative is used. -/
theorem compact_inverse_cap_restriction_coeFn
    (μ : Measure ℍ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (m : ℕ)
    (hl : Measurable (fun z : ℍ => Real.log (cappedHeightWeight δ m z)))
    (S : Set ℍ) (hS : MeasurableSet S)
    (hheight : ∀ z ∈ S, δ * Real.exp (-R) ≤ z.im)
    (f : Lp ℂ 2 μ) (F : ℍ → ℂ)
    (hf : f =ᵐ[μ] (fun z => (cappedHeightWeight δ m z : ℂ) * F z)) :
    let J := ⌈(m : ℝ) * R + 1⌉₊
    let K := ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
      LogBands.inverse μ (fun z => Real.log (cappedHeightWeight δ m z)) hl n
    AsymptoticRegionL2.projection μ S hS (K f) =ᵐ[μ] S.indicator F := by
  intro J K
  have hk := LogBands.compact_inverse_sum_coeFn μ
    (fun z => Real.log (cappedHeightWeight δ m z)) hl
    (Finset.Icc (-(J : ℤ)) (J : ℤ)) f
  filter_upwards [AsymptoticRegionL2.projection_coeFn μ S hS (K f), hk, hf]
    with z hp hk hf
  classical
  by_cases hz : z ∈ S
  · rw [hp, indicator_of_mem hz, indicator_of_mem hz, hk, hf, ← mul_assoc]
    rw [compact_inverse_cap_coefficient hδ hR m z (hheight z hz), one_mul]
  · rw [hp, indicator_of_notMem hz, indicator_of_notMem hz]

/-- Local square-integrability follows from the bounded inverse-band
construction itself, rather than being an extra hypothesis. -/
theorem compact_unweighted_representative_memLp
    (μ : Measure ℍ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (m : ℕ)
    (hl : Measurable (fun z : ℍ => Real.log (cappedHeightWeight δ m z)))
    (S : Set ℍ) (hS : MeasurableSet S)
    (hheight : ∀ z ∈ S, δ * Real.exp (-R) ≤ z.im)
    (f : Lp ℂ 2 μ) (F : ℍ → ℂ)
    (hf : f =ᵐ[μ] (fun z => (cappedHeightWeight δ m z : ℂ) * F z)) :
    MemLp (S.indicator F) 2 μ := by
  have he := compact_inverse_cap_restriction_coeFn μ hδ hR m hl S hS hheight f F hf
  exact (memLp_congr_ae he).mp (Lp.memLp _)

#print axioms LogBands.compact_inverse_sum_coeFn
#print axioms compact_inverse_cap_restriction_coeFn
#print axioms compact_unweighted_representative_memLp

end QuantitativeMaass
