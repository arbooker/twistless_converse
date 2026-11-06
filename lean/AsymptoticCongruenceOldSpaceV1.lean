module

public import AsymptoticOvergroupIsometryV1
public import AsymptoticFiberCompressionV1
public import AsymptoticQuotientCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticCongruenceQuotient
open AsymptoticRegularTrace
open scoped lp ComplexConjugate Classical

variable (N : ℕ) (J : Subgroup AsymptoticRationalGroup.Group) (hJ : gamma N≤J)
variable [Finite (J ⧸ (gamma N).subgroupOf J)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- The old direction attached to a finite-index overgroup, embedded in
the actual weighted strip Hilbert space by the congruence isometry. -/
noncomputable def induction (z : ℍ) :
    ℓ²(AsymptoticNestedQuotients.Classes J,ℂ) →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (AsymptoticCongruenceQuotient.induction N hε ht z).comp
    (AsymptoticNestedQuotients.isometry hJ)

noncomputable def space (z : ℍ) : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (induction N J hJ hε ht z).toLinearMap.range

noncomputable instance space_complete (z : ℍ) : CompleteSpace (space N J hJ hε ht z) :=
  AsymptoticIsometryRange.range_complete (induction N J hJ hε ht z)

theorem space_le_quotient (z : ℍ) : space N J hJ hε ht z≤quotientSpace N hε ht z := by
  rintro v ⟨f,rfl⟩
  exact ⟨AsymptoticNestedQuotients.isometry hJ f,rfl⟩

theorem space_mem (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    v∈space N J hJ hε ht z ↔ v∈quotientSpace N hε ht z ∧
      ∀ a : J,∀ g,coordinate N ε t z (a.val*g) v=coordinate N ε t z g v := by
  constructor
  · intro hv
    refine ⟨space_le_quotient N J hJ hε ht z hv,?_⟩
    obtain ⟨f,rfl⟩ := hv
    change ∀ a : J,∀ g,
      coordinate N ε t z (a.val*g)
        (AsymptoticCongruenceQuotient.induction N hε ht z (AsymptoticNestedQuotients.isometry hJ f))=
      coordinate N ε t z g
        (AsymptoticCongruenceQuotient.induction N hε ht z (AsymptoticNestedQuotients.isometry hJ f))
    simp only [coordinate_induction]
    exact (AsymptoticNestedQuotients.isometry_range_iff hJ _).mp ⟨f,rfl⟩
  · rintro ⟨⟨u,rfl⟩,hu⟩
    change ∀ a : J,∀ g,coordinate N ε t z (a.val*g)
      (AsymptoticCongruenceQuotient.induction N hε ht z u)=coordinate N ε t z g
      (AsymptoticCongruenceQuotient.induction N hε ht z u) at hu
    simp only [coordinate_induction] at hu
    have hi : u∈(AsymptoticNestedQuotients.isometry hJ).toLinearMap.range := by
      apply (AsymptoticNestedQuotients.isometry_range_iff hJ u).mpr
      exact hu
    obtain ⟨f,rfl⟩ := hi
    exact ⟨f,rfl⟩

theorem projection_matrix (z : ℍ) (g k : AsymptoticRationalGroup.Group) :
    matrix (space N J hJ hε ht z).starProjection g k=
      if AsymptoticNestedQuotients.classOf J g=AsymptoticNestedQuotients.classOf J k then
        amplitude N ε t (g • z)*conj (amplitude N ε t (k • z))*
          ((((gamma N).subgroupOf J).index:ℝ)⁻¹:ℂ)
      else 0 := by
  have he := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht z) (AsymptoticNestedQuotients.isometry hJ)
  have hm := AsymptoticFiberIsometry.compression_matrix (classOf N)
    (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z)
    (AsymptoticNestedQuotients.space hJ).starProjection g k
  change matrix (space N J hJ hε ht z).starProjection g k=_
  have he' := congrArg (fun T : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ) => T (delta k) g) he
  change matrix (space N J hJ hε ht z).starProjection g k=_ at he'
  have hmatrix := he'.trans hm
  rw [hmatrix,AsymptoticNestedQuotients.projection_matrix]
  have hg : AsymptoticNestedQuotients.forget hJ (classOf N g)=
      AsymptoticNestedQuotients.classOf J g := rfl
  have hk : AsymptoticNestedQuotients.forget hJ (classOf N k)=
      AsymptoticNestedQuotients.classOf J k := rfl
  simp only [hg,hk,mul_ite,mul_zero]

#print axioms space_le_quotient
#print axioms space_mem
#print axioms projection_matrix

end AsymptoticCongruenceOldSpace
