module

public import QuantitativeMaassQuotientLocalL2V1
public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

variable {G A : Type*} [Group G] [Countable G]
  [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
  [ProperlyDiscontinuousSMul G A]

/-- Compact restriction has one uniform energy bound for all invariant
representatives. The constant depends only on compact orbit overlap. -/
theorem quotient_restriction_energy_bound
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) (hKm : MeasurableSet K) :
    ∃ M : ℕ, ∀ (f : A → ℂ), Measurable f →
      (∀ g : G, ∀ x, f (g•x)=f x) →
      (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ.restrict K) ≤
        (M : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ.withDensity ρ := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_count_bound (G := G) K hK
  refine ⟨M, ?_⟩
  intro f hf hinv
  let F : A → ℝ≥0∞ := fun x => ENNReal.ofReal (‖f x‖^2)
  have hF : Measurable F := (hf.norm.pow_const 2).ennreal_ofReal
  have hun := lintegral_poincare_unfold μ hmp ρ hρ hn (K.indicator F) (hF.indicator hKm)
  have he (x : A) : (∑' g : G, K.indicator F (g•x)) =
      (∑' g : G, K.indicator (fun _ => (1 : ℝ≥0∞)) (g•x))*F x := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    by_cases hg : g•x ∈ K
    · simp only [Set.indicator_of_mem hg, one_mul]
      exact congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) (hinv g x)
    · simp only [Set.indicator_of_notMem hg, zero_mul]
  change (∫⁻ x, F x ∂μ.restrict K) ≤ (M : ℝ≥0∞)*∫⁻ x, F x ∂μ.withDensity ρ
  rw [← lintegral_indicator hKm F, ← hun]
  simp_rw [he]
  calc
    _ ≤ ∫⁻ x, (M : ℝ≥0∞)*F x ∂μ.withDensity ρ :=
      lintegral_mono (fun x => by gcongr; exact hM x)
    _ = _ := lintegral_const_mul _ hF

/-- Uniform local L² control by the quotient norm. This is the boundedness
needed before extending cusp averages to the Hilbert completion. -/
theorem quotient_restriction_norm_bound
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) (hKm : MeasurableSet K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : A → ℂ) (hf : Measurable f)
      (hinv : ∀ g : G, ∀ x, f (g•x)=f x) (hL : MemLp f 2 (μ.withDensity ρ)),
      ‖(invariant_memLp_restrict_compact μ hmp ρ hρ hn f hf hinv hL K hK hKm).toLp f‖ ≤
        C * ‖hL.toLp f‖ := by
  obtain ⟨M,hM⟩ := quotient_restriction_energy_bound μ hmp ρ hρ hn K hK hKm
  refine ⟨M+1, by positivity, ?_⟩
  intro f hf hinv hL
  let hloc := invariant_memLp_restrict_compact μ hmp ρ hρ hn f hf hinv hL K hK hKm
  have hi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ.withDensity ρ) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hi.2).ne
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) (hM f hf hinv)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, square_energy_toReal f hloc,
    square_energy_toReal f hL] at hb
  have hmul := mul_le_mul_of_nonneg_right
    (show (M : ℝ) ≤ ((M : ℝ)+1)^2 by nlinarith [Nat.cast_nonneg (α := ℝ) M])
    (sq_nonneg ‖hL.toLp f‖)
  have hc : 0 ≤ ((M : ℝ)+1) * ‖hL.toLp f‖ := by positivity
  change ‖hloc.toLp f‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) hc).mp
  rw [mul_pow]
  exact hb.trans hmul

#print axioms quotient_restriction_energy_bound
#print axioms quotient_restriction_norm_bound

end QuantitativeMaass
