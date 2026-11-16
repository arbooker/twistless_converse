module

public import QuantitativeMaassPoincareEnergyV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

theorem square_energy_toReal {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : A → ℂ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ).toReal=‖hf.toLp f‖^2 := by
  rw [complex_toLp_norm_sq]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (hf.aestronglyMeasurable.norm.pow 2)).symm

/-- A single boundedness constant for periodizing all L² seeds supported
in a prescribed compact set, now in the actual Hilbert norm. -/
theorem compact_poincare_uniform_norm_bound {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) :
    ∃ C : ℝ, 0<C ∧ ∀ (f : A → ℂ) (hm : Measurable f)
      (hs : Function.support f ⊆ K) (hL : MemLp f 2 μ),
      ‖(compact_poincare_memLp μ hmp ρ hρ hn K hK f hm hs hL).toLp
        (poincareSum (G := G) f)‖≤C*‖hL.toLp f‖ := by
  obtain ⟨M,hM⟩ := compact_poincare_uniform_energy_bound μ hmp ρ hρ hn K hK
  refine ⟨M+1,by positivity,?_⟩
  intro f hm hs hL
  let hP := compact_poincare_memLp μ hmp ρ hρ hn K hK f hm hs hL
  have hi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ)≠∞ :=
    ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hi.2).ne
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) (hM f hm hs)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,square_energy_toReal f hL,
    square_energy_toReal _ hP] at hb
  have hpos := norm_nonneg (hL.toLp f)
  have hposP := norm_nonneg (hP.toLp (poincareSum (G := G) f))
  have hMpos : (0:ℝ)≤M := Nat.cast_nonneg M
  have hC : 0≤((M:ℝ)+1)*‖hL.toLp f‖ := mul_nonneg (by positivity) hpos
  have hsquare : ‖hP.toLp (poincareSum (G := G) f)‖^2≤
      (((M:ℝ)+1)*‖hL.toLp f‖)^2 := by
    have hm : (M:ℝ)≤((M:ℝ)+1)^2 := by nlinarith
    have hx := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖hL.toLp f‖)
    nlinarith
  nlinarith

#print axioms compact_poincare_uniform_norm_bound

end QuantitativeMaass
