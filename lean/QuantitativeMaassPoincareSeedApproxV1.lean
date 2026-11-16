module

public import QuantitativeMaassPoincareFixedSupportV1
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- L² approximation with one fixed compact support for every approximating
seed. The larger compact depends only on the original compact, not on the
function or the requested error. This keeps orbit-overlap constants uniform. -/
theorem compact_seed_continuous_approx {A : Type*} [TopologicalSpace A]
    [LocallyCompactSpace A] [T2Space A] [NormalSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.Regular] (K : Set A) (hK : IsCompact K) :
    ∃ L : Set A, IsCompact L ∧ K ⊆ L ∧
      ∀ f : A → ℂ, MemLp f 2 μ → Function.support f ⊆ K →
        ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ g : A → ℂ,
          Continuous g ∧ Function.support g ⊆ L ∧ HasCompactSupport g ∧
            MemLp g 2 μ ∧ eLpNorm (f-g) 2 μ ≤ ε := by
  obtain ⟨η,hηK,hηc,-,hηb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hK isOpen_univ (subset_univ K)
  refine ⟨tsupport η,hηc,?_,?_⟩
  · intro x hx
    apply subset_closure
    simpa only [Function.mem_support,hηK hx,Pi.one_apply] using (one_ne_zero : (1:ℝ)≠0)
  intro f hf hs ε hε
  obtain ⟨g,hgc,herr,hg,hgL⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε
  let g' : A → ℂ := fun x => (η x:ℂ)*g x
  have hg' : Continuous g' := (Complex.continuous_ofReal.comp η.continuous).mul hg
  have hgs : Function.support g' ⊆ tsupport η := by
    intro x hx
    apply subset_closure
    intro hz
    exact hx (by simp [g',hz])
  have hgb (x : A) : ‖g' x‖≤‖g x‖ := by
    dsimp [g']
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hηb x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηb x).2
  have hg'L : MemLp g' 2 μ := hgL.mono hg'.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  refine ⟨g',hg',hgs,hηc.of_isClosed_subset isClosed_closure (closure_minimal hgs
    isClosed_closure),hg'L,?_⟩
  apply le_trans (eLpNorm_mono (hf.sub hg'L).aestronglyMeasurable ?_) herr
  intro x
  have he : f x-g' x=(η x:ℂ)*(f x-g x) := by
    by_cases hx : x∈K
    · simp [g',hηK hx]
    · have hz : f x=0 := by
        by_contra hne
        exact hx (hs hne)
      simp [g',hz]
  change ‖f x-g' x‖≤‖f x-g x‖
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hηb x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hηb x).2

#print axioms compact_seed_continuous_approx

end QuantitativeMaass
