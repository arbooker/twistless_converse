module

public import QuantitativeMaassWeightedQuotientEmbeddingV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open AsymptoticCompactBranch
open scoped ENNReal

namespace QuantitativeMaass

def heightWeightFloor (ε : ℝ) (v : ℕ) (Y : ℝ) : ℝ := ((min (Y/ε) 1)^v)^2

theorem heightWeightFloor_pos {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) (v : ℕ) :
    0<heightWeightFloor ε v Y :=
  pow_pos (pow_pos (lt_min (div_pos hY hε) zero_lt_one) v) 2

theorem weight_lower_of_height (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y)
    {v : ℕ} (hv : 1≤v) (z : ℍ) (hz : Y≤z.im) :
    heightWeightFloor ε v Y≤weight N ε v z := by
  apply le_trans _ (weight_lower N hε hv z)
  change ((min (Y/ε) 1)^v)^2 ≤ ((min (z.im/ε) 1)^v)^2
  apply pow_le_pow_left₀ (pow_nonneg (le_min (div_pos hY hε).le zero_le_one) v)
  apply pow_le_pow_left₀ (le_min (div_pos hY hε).le zero_le_one)
  exact min_le_min (div_le_div_of_nonneg_right hz hε.le) le_rfl

/-- Finite cusp coverage gives a positive lower bound for the sum of the
actual orbit weights at those normalizers. The covering condition is a
geometric statement, independent of a function or spectral parameter. -/
theorem normalizer_weight_sum_lower {ι : Type*} [Fintype ι] (N : ℕ)
    {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • (g i • z)).im) (z : ℍ) :
    ENNReal.ofReal (heightWeightFloor ε v Y)≤
      ∑ i,ENNReal.ofReal (weight N ε v (g i • z)) := by
  classical
  obtain ⟨i,a,ha⟩ := hcover z
  have h := weight_lower_of_height N hε hY hv (a.val • (g i • z)) ha
  rw [weight_invariant] at h
  exact (ENNReal.ofReal_le_ofReal h).trans (Finset.single_le_sum (f := fun j => ENNReal.ofReal (weight N ε v (g j • z)))
    (fun _ _ => zero_le) (Finset.mem_univ i))

/-- Under a quotient normalizer preserving the absolute value of a
representative, the weighted quotient energy is unchanged. -/
theorem weighted_energy_normalizer (N : ℕ) (ε : ℝ) (v : ℕ)
    (g : AsymptoticRationalGroup.Group)
    (hc : ∀ a∈gamma N,g*a*g⁻¹∈gamma N)
    (hci : ∀ a∈gamma N,g⁻¹*a*g∈gamma N)
    (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ a : gamma N,∀ z,f (a.val • z)=f z)
    (hg : ∀ z,‖f (g • z)‖=‖f z‖) :
    (∫⁻ z,ENNReal.ofReal (weight N ε v (g • z))*ENNReal.ofReal (‖f z‖^2)
      ∂quotientMeasure N)=
    ∫⁻ z,ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f z‖^2)
      ∂quotientMeasure N := by
  have h := OrbitIntegral.lintegral_normalizer volume AsymptoticRationalGroup.measurePreserving
    (gamma N) g hc hci (density N) (density_measurable N) (density_orbit_sum N)
    (fun z => ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f z‖^2))
    ((weight_measurable N ε v).ennreal_ofReal.mul (hf.norm.pow_const 2).ennreal_ofReal)
    (by intro a z; rw [weight_invariant,hinv])
  simpa only [hg,quotientMeasure] using h

/-- Lower metric estimate from explicit finite normalizer coverage. The
actual new/sign application must supply the normalizer list, its cusp
coverage and its modulus-one functional equations. -/
theorem weighted_quotient_energy_lower_of_normalizers {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group)
    (hc : ∀ i,∀ a∈gamma N,g i*a*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ a∈gamma N,(g i)⁻¹*a*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • (g i • z)).im)
    (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ a : gamma N,∀ z,f (a.val • z)=f z)
    (hg : ∀ i z,‖f (g i • z)‖=‖f z‖) :
    ENNReal.ofReal (heightWeightFloor ε v Y)*
      (∫⁻ z,ENNReal.ofReal (‖f z‖^2) ∂quotientMeasure N)≤
      (Fintype.card ι:ℝ≥0∞)*
        ∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*f z‖^2) ∂quotientMeasure 0 := by
  classical
  rw [weighted_quotient_energy N hε hv f hf hinv,
    ←lintegral_const_mul _ ((hf.norm.pow_const 2).ennreal_ofReal)]
  calc
    _≤∫⁻ z,(∑ i,ENNReal.ofReal (weight N ε v (g i • z)))*ENNReal.ofReal (‖f z‖^2)
        ∂quotientMeasure N := by
      apply lintegral_mono
      intro z
      exact mul_le_mul (normalizer_weight_sum_lower N hε hY hv g hcover z)
        le_rfl (zero_le) (zero_le)
    _=∑' i,∫⁻ z,ENNReal.ofReal (weight N ε v (g i • z))*ENNReal.ofReal (‖f z‖^2)
        ∂quotientMeasure N := by
      simp_rw [tsum_fintype, Finset.sum_mul]
      apply lintegral_finsetSum
      intro i _
      exact (((weight_measurable N ε v).comp
        (AsymptoticRationalGroup.measurePreserving (g i)).measurable).ennreal_ofReal.mul
          (hf.norm.pow_const 2).ennreal_ofReal)
    _=_ := by
      simp only [weighted_energy_normalizer N ε v _ (hc _) (hci _) f hf hinv (hg _),
        tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

#print axioms heightWeightFloor_pos
#print axioms weight_lower_of_height
#print axioms normalizer_weight_sum_lower
#print axioms weighted_energy_normalizer
#print axioms weighted_quotient_energy_lower_of_normalizers

end QuantitativeMaass
