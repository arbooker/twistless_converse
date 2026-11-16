module

public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Points whose actual congruence orbit meets the given core. -/
def orbitCore (N : ℕ) (S : Set ℍ) : Set ℍ :=
  {z | ∃ γ : gamma N,γ.val•z∈S}

theorem orbitCore_measurable (N : ℕ) (S : Set ℍ) (hS : MeasurableSet S) :
    MeasurableSet (orbitCore N S) := by
  change MeasurableSet {z | ∃ γ : gamma N,γ.val•z∈S}
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro γ
  exact hS.preimage (AsymptoticRationalGroup.measurePreserving γ.val).measurable

theorem orbitCore_contains (N : ℕ) (S : Set ℍ) : S⊆orbitCore N S := by
  intro z hz
  exact ⟨1,by simpa only [Subgroup.coe_one,one_smul] using hz⟩

theorem orbitCore_mem_smul (N : ℕ) (S : Set ℍ) (g : gamma N) (z : ℍ) :
    g.val•z∈orbitCore N S ↔ z∈orbitCore N S := by
  constructor
  · rintro ⟨h,hh⟩
    exact ⟨h*g,by simpa only [Subgroup.coe_mul,mul_smul] using hh⟩
  · rintro ⟨h,hh⟩
    exact ⟨h*g⁻¹,by simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,inv_smul_smul] using hh⟩

/-- Invariant quotient energy on the orbit-saturated core is bounded by
the literal raw core integral. Only the actual density unfolding is used. -/
theorem quotient_orbitCore_lintegral_le (N : ℕ) (S : Set ℍ) (hS : MeasurableSet S)
    (F : ℍ→ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N,∀ z,F (g.val•z)=F z) :
    (∫⁻ z in orbitCore N S,F z ∂quotientMeasure N)≤∫⁻ z in S,F z := by
  have hun := lintegral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (S.indicator F) (hF.indicator hS)
  rw [←lintegral_indicator hS F,←hun,
    ←lintegral_indicator (orbitCore_measurable N S hS) F]
  apply lintegral_mono
  intro z
  by_cases hz : z∈orbitCore N S
  · obtain ⟨g,hg⟩ := hz
    rw [Set.indicator_of_mem (show z∈orbitCore N S from ⟨g,hg⟩)]
    calc
      F z=S.indicator F (g.val•z) := by rw [Set.indicator_of_mem hg,hinv]
      _≤∑' a : gamma N,S.indicator F (a.val•z) := ENNReal.le_tsum (f := fun a : gamma N => S.indicator F (a.val•z)) g
  · rw [Set.indicator_of_notMem hz]
    exact bot_le

#print axioms orbitCore_measurable
#print axioms orbitCore_contains
#print axioms orbitCore_mem_smul
#print axioms quotient_orbitCore_lintegral_le

end QuantitativeMaass
