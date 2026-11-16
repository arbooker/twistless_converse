module

public import QuantitativeMaassQuotientLocalL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- One multiplicity constant works for every seed supported in a fixed
compact set. No continuity of the seed is required. -/
theorem compact_poincare_uniform_square_bound {G A : Type*} [Group G]
    [TopologicalSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (K : Set A) (hK : IsCompact K) :
    ∃ M : ℕ, ∀ f : A → ℂ, Function.support f ⊆ K → ∀ x,
      ‖poincareSum (G := G) f x‖^2≤(M:ℝ)*∑' g : G, ‖f (g•x)‖^2 := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_overlap (G := G) K hK
  refine ⟨M,?_⟩
  intro f hf x
  let hS := compact_orbit_point_finite (G := G) K hK x
  let S := hS.toFinset
  have hout (g : G) (hg : g∉S) : f (g•x)=0 := by
    by_contra hne
    exact hg (hS.mem_toFinset.mpr (hf hne))
  have hcard : S.card≤M := hM x S (fun g hg => hS.mem_toFinset.mp hg)
  have hp : poincareSum (G := G) f x=∑ g∈S, f (g•x) := tsum_eq_sum hout
  have hq : (∑' g : G, ‖f (g•x)‖^2)=∑ g∈S, ‖f (g•x)‖^2 :=
    tsum_eq_sum (fun g hg => by simp [hout g hg])
  rw [hp,hq]
  calc
    ‖∑ g∈S, f (g•x)‖^2 ≤ (∑ g∈S, ‖f (g•x)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (S.card:ℝ)*∑ g∈S, ‖f (g•x)‖^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Uniform L² energy control for all measurable seeds in one compact set.
This is the estimate needed to pass fixed-support approximations through
periodization; its constant is independent of the approximating seed. -/
theorem compact_poincare_uniform_energy_bound {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) :
    ∃ M : ℕ, ∀ f : A → ℂ, Measurable f → Function.support f ⊆ K →
      (∫⁻ x, ENNReal.ofReal (‖poincareSum (G := G) f x‖^2) ∂μ.withDensity ρ)≤
        (M:ℝ≥0∞)*∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ := by
  classical
  obtain ⟨M,hM⟩ := compact_poincare_uniform_square_bound (G := G) K hK
  refine ⟨M,?_⟩
  intro f hm hf
  have hpoint (x : A) : ENNReal.ofReal (‖poincareSum (G := G) f x‖^2)≤
      (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) := by
    have hs : Summable (fun g : G => ‖f (g•x)‖^2) := by
      apply summable_of_hasFiniteSupport
      apply (compact_orbit_point_finite (G := G) K hK x).subset
      intro g hg
      apply hf
      intro hz
      exact hg (by simp [hz])
    have hb := ENNReal.ofReal_le_ofReal (hM f hf x)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg M),ENNReal.ofReal_natCast,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs] at hb
  calc
    _ ≤ ∫⁻ x, (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) ∂μ.withDensity ρ :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp),
        lintegral_poincare_unfold μ hmp ρ hρ hn _ (hm.norm.pow_const 2).ennreal_ofReal]

#print axioms compact_poincare_uniform_energy_bound

end QuantitativeMaass
