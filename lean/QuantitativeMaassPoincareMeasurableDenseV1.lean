module

public import QuantitativeMaassPoincareEnergyV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Classes of literal Poincaré series of compactly supported ambient L²
seeds. This set has no assumed density property. -/
def compactSeedClasses {G A : Type*} [Group G] [MulAction G A]
    [TopologicalSpace A] [MeasurableSpace A] (μ ν : Measure A) : Set (Lp ℂ 2 ν) :=
  {v | ∃ φ : A → ℂ, Measurable φ ∧ HasCompactSupport φ ∧ MemLp φ 2 μ ∧
    ∃ hP : MemLp (poincareSum (G := G) φ) 2 ν, v=hP.toLp (poincareSum (G := G) φ)}

/-- Every actual invariant quotient-L² representative is approximated by
literal compact measurable Poincaré seeds. -/
theorem invariant_mem_closure_compactSeedClasses {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : CompactExhaustion A) (f : A → ℂ) (hf : Measurable f)
    (hinv : ∀ g : G, ∀ x, f (g•x)=f x) (hL : MemLp f 2 (μ.withDensity ρ)) :
    hL.toLp f ∈ closure (compactSeedClasses (G := G) μ (μ.withDensity ρ)) := by
  let φ (n : ℕ) : A → ℂ := (K n).indicator (fun x => ((ρ x).toReal:ℂ)*f x)
  have hm (n : ℕ) : Measurable (φ n) :=
    ((Complex.continuous_ofReal.measurable.comp hρ.ennreal_toReal).mul hf).indicator
      (K.isCompact n).isClosed.measurableSet
  have hs (n : ℕ) : Function.support (φ n) ⊆ K n := Set.support_indicator_subset
  have hc (n : ℕ) : HasCompactSupport (φ n) :=
    (K.isCompact n).of_isClosed_subset isClosed_closure
      (closure_minimal (hs n) (K.isCompact n).isClosed)
  have hφ (n : ℕ) : MemLp (φ n) 2 μ := compact_weighted_seed_memLp μ hmp ρ hρ hn
    f hf hinv hL (K n) (K.isCompact n) (K.isCompact n).isClosed.measurableSet
  have hP (n : ℕ) : MemLp (poincareSum (G := G) (φ n)) 2 (μ.withDensity ρ) :=
    compact_poincare_memLp μ hmp ρ hρ hn (K n) (K.isCompact n) (φ n) (hm n) (hs n) (hφ n)
  have he (n : ℕ) (x : A) : ‖poincareSum (G := G) (φ n) x-f x‖^2=
      ‖f x‖^2*(1-orbitCutoff (G := G) ρ (K n) x)^2 := by
    rw [poincare_compact_weighted_seed ρ f hinv]
    have hfactor : (orbitCutoff (G := G) ρ (K n) x:ℂ)*f x-f x=
        ((orbitCutoff (G := G) ρ (K n) x-1:ℝ):ℂ)*f x := by push_cast; ring
    rw [hfactor,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  have ht := tendsto_toLp_of_square_energy (fun n => poincareSum (G := G) (φ n)) hP f hL
    (by simpa only [he] using orbitCutoff_energy_tendsto_zero μ hmp ρ hρ hn K f hf hL)
  apply isClosed_closure.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  apply subset_closure
  exact ⟨φ n,hm n,hc n,hφ n,hP n,rfl⟩

/-- Density holds in the completed automorphic Hilbert space, not only for
pointwise invariant representatives. -/
theorem automorphic_space_subset_closure_compactSeedClasses {G A : Type*}
    [Group G] [Countable G] [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : CompactExhaustion A) :
    (AutomorphicL2.space (⊤ : Subgroup G) (μ.withDensity ρ) : Set (Lp ℂ 2 (μ.withDensity ρ))) ⊆
      closure (compactSeedClasses (G := G) μ (μ.withDensity ρ)) := by
  apply closure_minimal _ isClosed_closure
  rintro v ⟨f,rfl⟩
  exact invariant_mem_closure_compactSeedClasses μ hmp ρ hρ hn K f.val f.property.1
    (fun g x => f.property.2.1 ⟨g,Subgroup.mem_top g⟩ x) f.property.2.2

#print axioms automorphic_space_subset_closure_compactSeedClasses

end QuantitativeMaass
