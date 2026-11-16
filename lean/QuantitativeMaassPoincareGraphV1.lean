module

public import QuantitativeMaassPoincareGreenV1
public import Mathlib.Analysis.InnerProductSpace.Continuous

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane Topology
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass
open MaassDifferential

/-- Concrete smooth compact seeds on the upper half-plane. -/
structure SmoothUpperSeed where
  toFun : Point → ℂ
  smooth : ContDiffOn ℝ ∞ toFun {Z | 0<Z.2}
  compact : HasCompactSupport (upperFunction toFun)

def SmoothUpperSeed.laplacian (u : SmoothUpperSeed) : SmoothUpperSeed where
  toFun := hyperbolic u.toFun
  smooth := hyperbolic_contDiffOn u.smooth
  compact := upperLaplacian_compact u.toFun u.compact

theorem poincareSeed_representative (N : ℕ) (u : SmoothUpperSeed) :
    poincareSum (G := gamma N) (upperFunction u.toFun) ∈
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  refine ⟨(poincareSum_continuous (G := gamma N) _ u.compact
    (upperFunction_continuous u.smooth)).measurable,?_,?_⟩
  · intro g z
    exact poincareSum_invariant _ g z
  · exact poincareSum_memLp volume
      (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
      (density N) (density_measurable N) (density_orbit_sum N)
      _ (upperFunction_continuous u.smooth) u.compact

/-- The literal Poincaré representative, in the actual closed quotient
Hilbert space rather than an abstract completion supplied as a premise. -/
def poincareSeedVector (N : ℕ) (u : SmoothUpperSeed) : AutomorphicSpace N :=
  AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)
    ⟨_,poincareSeed_representative N u⟩

theorem poincareSeedVector_coeFn (N : ℕ) (u : SmoothUpperSeed) :
    ((poincareSeedVector N u).val : ℍ → ℂ)=ᵐ[quotientMeasure N]
      poincareSum (G := gamma N) (upperFunction u.toFun) :=
  (poincareSeed_representative N u).2.2.coeFn_toLp

theorem poincareSeedVector_inner (N : ℕ) (u v : SmoothUpperSeed) :
    inner ℂ (poincareSeedVector N u) (poincareSeedVector N v)=
      ∫ z, star (poincareSum (G := gamma N) (upperFunction u.toFun) z)*
        poincareSum (G := gamma N) (upperFunction v.toFun) z ∂quotientMeasure N := by
  change inner ℂ (poincareSeedVector N u).val (poincareSeedVector N v).val=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [poincareSeedVector_coeFn N u,poincareSeedVector_coeFn N v] with z hu hv
  simp [hu,hv,mul_comm]

theorem poincareSeedVector_dense (N : ℕ) : DenseRange (poincareSeedVector N) := by
  intro x
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change x.val∈closure (Subtype.val '' range (poincareSeedVector N))
  have hs : smoothSeedClasses (G := gamma N) (quotientMeasure N)⊆
      Subtype.val '' range (poincareSeedVector N) := by
    rintro f ⟨u,hu,hc,hP,rfl⟩
    refine ⟨poincareSeedVector N ⟨u,hu.contDiffOn,hc⟩,⟨_,rfl⟩,?_⟩
    rfl
  apply closure_mono hs
  rw [congruence_smooth_poincare_dense]
  exact x.property

theorem poincareSeedVector_laplacian_symmetric (N : ℕ) (u v : SmoothUpperSeed) :
    inner ℂ (poincareSeedVector N u.laplacian) (poincareSeedVector N v)=
      inner ℂ (poincareSeedVector N u) (poincareSeedVector N v.laplacian) := by
  rw [poincareSeedVector_inner,poincareSeedVector_inner]
  have h := poincare_green_symmetric N u.smooth v.smooth u.compact v.compact
  rw [upperLaplacian_congruencePoincareCartesian N u.smooth u.compact,
    upperLaplacian_congruencePoincareCartesian N v.smooth v.compact] at h
  exact h.symm

/-- Graph of the actual quotient differential expression on Poincaré
seeds. Single-valuedness below is proved; it is not built into this definition. -/
def PoincareGraph (N : ℕ) (x y : AutomorphicSpace N) : Prop :=
  ∃ u : SmoothUpperSeed, x=poincareSeedVector N u ∧ y=poincareSeedVector N u.laplacian

theorem poincareGraph_denseDomain (N : ℕ) :
    Dense {x : AutomorphicSpace N | ∃ y, PoincareGraph N x y} := by
  apply (poincareSeedVector_dense N).mono
  rintro x ⟨u,rfl⟩
  exact ⟨_,u,rfl,rfl⟩

theorem poincareGraph_symmetric (N : ℕ) {x y x' y' : AutomorphicSpace N}
    (h : PoincareGraph N x y) (h' : PoincareGraph N x' y') :
    inner ℂ y x'=inner ℂ x y' := by
  obtain ⟨u,rfl,rfl⟩ := h
  obtain ⟨v,rfl,rfl⟩ := h'
  exact poincareSeedVector_laplacian_symmetric N u v

/-- Symmetry and actual Hilbert density remove the ambiguity of seed
representatives. Thus this is a genuine differential operator on classes. -/
theorem poincareGraph_singleValued (N : ℕ) {x y z : AutomorphicSpace N}
    (hy : PoincareGraph N x y) (hz : PoincareGraph N x z) : y=z := by
  apply (poincareSeedVector_dense N).eq_of_inner_left (𝕜 := ℂ)
  intro u
  rw [poincareGraph_symmetric N hy ⟨u,rfl,rfl⟩,
    poincareGraph_symmetric N hz ⟨u,rfl,rfl⟩]

#print axioms poincareGraph_denseDomain
#print axioms poincareGraph_singleValued
#print axioms poincareGraph_symmetric

end QuantitativeMaass
