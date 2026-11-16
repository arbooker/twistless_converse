module

public import QuantitativeMaassPoincareSmoothV1
public import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
@[expose] public noncomputable section

open Set UpperHalfPlane Topology
open scoped Topology

namespace QuantitativeMaass
open MaassDifferential

/-- Compact support makes extension by zero continuous along an open
embedding. The compact-support condition controls the boundary. -/
theorem compact_continuous_extend_zero {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [T2Space B] (e : A → B) (he : IsOpenEmbedding e)
    (f : A → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (e.extend f 0) := by
  apply continuous_of_tsupport
  intro y hy
  obtain ⟨x,-,rfl⟩ := hc.tsupport_extend_zero_subset he.continuous hy
  rw [← he.continuousAt_iff,Function.extend_comp he.injective]
  exact hf.continuousAt

def upperCoordinates (z : ℍ) : Point := (z.re,z.im)

theorem upperCoordinates_openEmbedding : IsOpenEmbedding upperCoordinates :=
  Complex.equivRealProdCLM.toHomeomorph.isOpenEmbedding.comp isOpenEmbedding_coe

/-- Literal zero extension of an upper-half-plane seed to Cartesian space. -/
def upperSeedExtension (f : ℍ → ℂ) : Point → ℂ := upperCoordinates.extend f 0

theorem upperSeedExtension_represents (f : ℍ → ℂ) : upperFunction (upperSeedExtension f)=f := by
  exact Function.extend_comp upperCoordinates_openEmbedding.injective f 0

theorem upperSeedExtension_continuous (f : ℍ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Continuous (upperSeedExtension f) :=
  compact_continuous_extend_zero upperCoordinates upperCoordinates_openEmbedding f hf hc

theorem upperSeedExtension_compact (f : ℍ → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (upperSeedExtension f) := hc.extend_zero upperCoordinates_openEmbedding.continuous

theorem upperSeedExtension_support (f : ℍ → ℂ) (hc : HasCompactSupport f) :
    tsupport (upperSeedExtension f) ⊆ upperCoordinates '' tsupport f :=
  hc.tsupport_extend_zero_subset upperCoordinates_openEmbedding.continuous

theorem upperSeedExtension_support_positive (f : ℍ → ℂ) (hc : HasCompactSupport f) :
    tsupport (upperSeedExtension f) ⊆ {Z : Point | 0<Z.2} := by
  rintro Z hZ
  obtain ⟨z,-,rfl⟩ := upperSeedExtension_support f hc hZ
  exact z.im_pos

#print axioms upperSeedExtension_continuous
#print axioms upperSeedExtension_support_positive

end QuantitativeMaass
