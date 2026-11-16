module

public import QuantitativeMaassPoincareMeasurableDenseV1
public import QuantitativeMaassPoincareSeedApproxV1
public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Literal periodizations of continuous compactly supported ambient seeds. -/
def continuousSeedClasses {G A : Type*} [Group G] [MulAction G A]
    [TopologicalSpace A] [MeasurableSpace A] (μ ν : Measure A) : Set (Lp ℂ 2 ν) :=
  {v | ∃ φ : A → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ MemLp φ 2 μ ∧
    ∃ hP : MemLp (poincareSum (G := G) φ) 2 ν, v=hP.toLp (poincareSum (G := G) φ)}

/-- The fixed-support bound transports ambient L² approximation through
actual periodization, even when the initial seed is only measurable. -/
theorem compactSeedClasses_subset_closure_continuousSeedClasses {G A : Type*}
    [Group G] [Countable G] [TopologicalSpace A] [LocallyCompactSpace A]
    [T2Space A] [NormalSpace A] [MeasurableSpace A] [BorelSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) [μ.Regular]
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) :
    compactSeedClasses (G := G) μ (μ.withDensity ρ) ⊆
      closure (continuousSeedClasses (G := G) μ (μ.withDensity ρ)) := by
  rintro v ⟨f,hm,hc,hf,hP,rfl⟩
  obtain ⟨L,hL,hKL,happrox⟩ := compact_seed_continuous_approx μ (tsupport f) hc
  obtain ⟨C,hC,hbound⟩ := compact_poincare_uniform_norm_bound μ hmp ρ hρ hn L hL
  rw [mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall]
  intro ε hε
  have hδ : 0<ε/C := div_pos hε hC
  obtain ⟨g,hg,hgs,hgc,hgL,herr⟩ := happrox f hf (subset_tsupport f)
    (ENNReal.ofReal (ε/C)) (by positivity)
  have hfs : Function.support f ⊆ L := (subset_tsupport f).trans hKL
  have hsub : Function.support (f-g) ⊆ L := by
    intro x hx
    by_contra hnL
    have hf0 : f x=0 := Function.notMem_support.mp (fun h => hnL (hfs h))
    have hg0 : g x=0 := Function.notMem_support.mp (fun h => hnL (hgs h))
    exact hx (by simp [hf0,hg0])
  let hgP := compact_poincare_memLp μ hmp ρ hρ hn L hL g hg.measurable hgs hgL
  refine ⟨hgP.toLp (poincareSum (G := G) g),⟨g,hg,hgc,hgL,hgP,rfl⟩,?_⟩
  have hb := hbound (f-g) (hm.sub hg.measurable) hsub (hf.sub hgL)
  have he : ((compact_poincare_memLp μ hmp ρ hρ hn L hL (f-g)
      (hm.sub hg.measurable) hsub (hf.sub hgL)).toLp (poincareSum (G := G) (f-g))) =
      hP.toLp (poincareSum (G := G) f)-hgP.toLp (poincareSum (G := G) g) := by
    rw [← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (poincareSum_sub_compact L hL f g hfs hgs))
  rw [he] at hb
  have hnerr : ‖(hf.sub hgL).toLp (f-g)‖≤ε/C := by
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono (by simp) herr).trans_eq (ENNReal.toReal_ofReal hδ.le)
  rw [Metric.mem_closedBall,dist_comm,dist_eq_norm]
  exact hb.trans ((mul_le_mul_of_nonneg_left hnerr hC.le).trans_eq (mul_div_cancel₀ ε hC.ne'))

/-- Continuous compact Poincaré seeds are dense in the completed actual
invariant quotient Hilbert space, with no density hypothesis. -/
theorem automorphic_space_subset_closure_continuousSeedClasses {G A : Type*}
    [Group G] [Countable G] [TopologicalSpace A] [LocallyCompactSpace A]
    [T2Space A] [NormalSpace A] [MeasurableSpace A] [BorelSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) [μ.Regular]
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : CompactExhaustion A) :
    (AutomorphicL2.space (⊤ : Subgroup G) (μ.withDensity ρ) : Set (Lp ℂ 2 (μ.withDensity ρ))) ⊆
      closure (continuousSeedClasses (G := G) μ (μ.withDensity ρ)) :=
  (automorphic_space_subset_closure_compactSeedClasses μ hmp ρ hρ hn K).trans
    (closure_minimal (compactSeedClasses_subset_closure_continuousSeedClasses μ hmp ρ hρ hn)
      isClosed_closure)

#print axioms compactSeedClasses_subset_closure_continuousSeedClasses
#print axioms automorphic_space_subset_closure_continuousSeedClasses

end QuantitativeMaass
