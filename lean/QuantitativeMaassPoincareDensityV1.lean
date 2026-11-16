module

public import QuantitativeMaassPoincareSmoothDenseV1
public import QuantitativeMaassPoincarePairingV1
public import QuantitativeMaassPoincareCoreV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open scoped ENNReal Topology MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

theorem smoothSeedClasses_subset_automorphic_space {G : Type*} [Group G]
    [MulAction G ℍ] [ProperlyDiscontinuousSMul G ℍ] [ContinuousConstSMul G ℍ]
    (ν : Measure ℍ) : smoothSeedClasses (G := G) ν ⊆
      (AutomorphicL2.space (⊤ : Subgroup G) ν : Set (Lp ℂ 2 ν)) := by
  rintro v ⟨u,hu,hc,hP,rfl⟩
  have huc : Continuous (upperFunction u) :=
    hu.continuous.comp upperCoordinates_openEmbedding.continuous
  let f : AutomorphicL2.representatives (⊤ : Subgroup G) ν :=
    ⟨poincareSum (G := G) (upperFunction u),
      (poincareSum_continuous (G := G) (upperFunction u) hc huc).measurable,
      (fun g x => poincareSum_invariant (upperFunction u) g.val x),hP⟩
  exact (LinearMap.range (AutomorphicL2.embedding (⊤ : Subgroup G) ν)).le_topologicalClosure
    (LinearMap.mem_range_self _ f)

/-- Equality with the closure of the constructed smooth Poincaré family.
This is Hilbert-space density, not an assertion that this family is an
operator core for a previously constructed self-adjoint Laplacian. -/
theorem closure_smoothSeedClasses_eq_automorphic_space {G : Type*}
    [Group G] [Countable G] [MulAction G ℍ]
    [ProperlyDiscontinuousSMul G ℍ] [ContinuousConstSMul G ℍ]
    (μ : Measure ℍ) [μ.Regular]
    (hmp : ∀ g : G, MeasurePreserving (fun x : ℍ => g•x) μ μ)
    (ρ : ℍ → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) :
    closure (smoothSeedClasses (G := G) (μ.withDensity ρ))=
      (AutomorphicL2.space (⊤ : Subgroup G) (μ.withDensity ρ) : Set (Lp ℂ 2 (μ.withDensity ρ))) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (smoothSeedClasses_subset_automorphic_space _)
      (LinearMap.range (AutomorphicL2.embedding (⊤ : Subgroup G)
        (μ.withDensity ρ))).isClosed_topologicalClosure
  · exact automorphic_space_subset_closure_smoothSeedClasses μ hmp ρ hρ hn

/-- Specialization to each literal integral subgroup, using the proved
proper discontinuity of its actual upper-half-plane action. -/
theorem integral_subgroup_smooth_poincare_dense (H : Subgroup SL(2,ℤ))
    (μ : Measure ℍ) [μ.Regular]
    (hmp : ∀ g : H, MeasurePreserving (fun x : ℍ => g•x) μ μ)
    (ρ : ℍ → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : H, ρ (g•x)=1) :
    closure (smoothSeedClasses (G := H) (μ.withDensity ρ))=
      (AutomorphicL2.space (⊤ : Subgroup H) (μ.withDensity ρ) : Set (Lp ℂ 2 (μ.withDensity ρ))) := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable SL(2,ℤ) := Function.Injective.countable
    (f := fun s : SL(2,ℤ) => s.val) Subtype.val_injective
  let : ContinuousConstSMul H ℍ :=
    ⟨fun g => continuous_const_smul (SpecialLinearGroup.mapGL ℝ g.val)⟩
  exact closure_smoothSeedClasses_eq_automorphic_space μ hmp ρ hρ hn

#print axioms integral_subgroup_smooth_poincare_dense

end QuantitativeMaass
