module

public import QuantitativeMaassPoincareL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

section CompactOverlap
variable {G A : Type*} [Group G] [TopologicalSpace A] [MulAction G A]
  [ProperlyDiscontinuousSMul G A]

/-- Uniform finite multiplicity of a compact set under the actual action. -/
theorem compact_orbit_overlap (K : Set A) (hK : IsCompact K) :
    ∃ M : ℕ, ∀ x : A, ∀ S : Finset G,
      (∀ g∈S, g•x∈K) → S.card≤M := by
  classical
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hK hK
  refine ⟨hfin.toFinset.card,?_⟩
  intro x S hS
  by_cases hne : S.Nonempty
  · obtain ⟨g₀,hg₀⟩ := hne
    apply Finset.card_le_card_of_injOn (fun g => g*g₀⁻¹)
    · intro g hg
      apply hfin.mem_toFinset.mpr
      refine ⟨g•x,⟨g₀•x,hS g₀ hg₀,?_⟩,hS g hg⟩
      simp only [mul_smul,inv_smul_smul]
    · exact (Equiv.mulRight g₀⁻¹).injective.injOn
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

theorem compact_orbit_point_finite (K : Set A) (hK : IsCompact K) (x : A) :
    {g : G | g•x∈K}.Finite := by
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G)
    (isCompact_singleton (x := x)) hK
  exact hf.subset (fun g hg => ⟨g•x,⟨x,mem_singleton x,rfl⟩,hg⟩)

theorem compact_orbit_count_bound (K : Set A) (hK : IsCompact K) :
    ∃ M : ℕ, ∀ x : A, (∑' g : G, K.indicator (fun _ => (1:ℝ≥0∞)) (g•x))≤M := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_overlap (G := G) K hK
  refine ⟨M,?_⟩
  intro x
  let hS := compact_orbit_point_finite (G := G) K hK x
  let S := hS.toFinset
  have hout (g : G) (hg : g∉S) : K.indicator (fun _ => (1:ℝ≥0∞)) (g•x)=0 := by
    apply Set.indicator_of_notMem
    intro hx
    exact hg (hS.mem_toFinset.mpr hx)
  rw [tsum_eq_sum hout]
  have he : (∑ g∈S, K.indicator (fun _ => (1:ℝ≥0∞)) (g•x))=S.card := by
    calc
      _ = ∑ _g∈S, (1:ℝ≥0∞) := Finset.sum_congr rfl
        (fun g hg => Set.indicator_of_mem (s := K)
          (show g•x∈K from hS.mem_toFinset.mp hg) _)
      _ = _ := by simp
  rw [he]
  exact_mod_cast hM x S (fun g hg => hS.mem_toFinset.mp hg)

end CompactOverlap

/-- Every invariant quotient-L² function is locally L² in the ambient
space. Compact orbit multiplicity and exact unfolding prove this fact. -/
theorem invariant_memLp_restrict_compact {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (f : A → ℂ) (hf : Measurable f) (hinv : ∀ g : G, ∀ x, f (g•x)=f x)
    (hL : MemLp f 2 (μ.withDensity ρ)) (K : Set A) (hK : IsCompact K)
    (hKm : MeasurableSet K) : MemLp f 2 (μ.restrict K) := by
  classical
  let F : A → ℝ≥0∞ := fun x => ENNReal.ofReal (‖f x‖^2)
  have hF : Measurable F := (hf.norm.pow_const 2).ennreal_ofReal
  have hFI : (∫⁻ x, F x ∂μ.withDensity ρ)<∞ := by
    have hi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hi.2
  obtain ⟨M,hM⟩ := compact_orbit_count_bound (G := G) K hK
  have hun := lintegral_poincare_unfold μ hmp ρ hρ hn (K.indicator F) (hF.indicator hKm)
  have he (x : A) : (∑' g : G, K.indicator F (g•x))=
      (∑' g : G, K.indicator (fun _ => (1:ℝ≥0∞)) (g•x))*F x := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    by_cases hg : g•x∈K
    · simp only [Set.indicator_of_mem hg,one_mul]
      exact congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) (hinv g x)
    · simp only [Set.indicator_of_notMem hg,zero_mul]
  have hbound : (∫⁻ x, F x ∂μ.restrict K)≤(M:ℝ≥0∞)*∫⁻ x, F x ∂μ.withDensity ρ := by
    rw [← lintegral_indicator hKm F,← hun]
    simp_rw [he]
    calc
      _ ≤ ∫⁻ x, (M:ℝ≥0∞)*F x ∂μ.withDensity ρ :=
        lintegral_mono (fun x => by gcongr; exact hM x)
      _ = _ := lintegral_const_mul _ hF
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by simp) hFI)

#print axioms compact_orbit_count_bound
#print axioms invariant_memLp_restrict_compact

end QuantitativeMaass
