module

public import AsymptoticClassicalPeterssonDensityV1
public import AsymptoticFrickeCosetsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCosets

open Matrix AsymptoticClassicalCusp AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels
open scoped MatrixGroups

variable {A B : Type*} [Group A] [Group B]

/-- Passing to a homomorphic image preserves relative cosets when the
 kernel is contained in the smaller subgroup. This retains representatives,
 rather than merely identifying the numerical indices. -/
def imageEquiv (f : A →* B) (H K : Subgroup A) (hk : f.ker ≤ H) :
    K ⧸ H.subgroupOf K ≃ K.map f ⧸ (H.map f).subgroupOf (K.map f) := by
  let F := f.subgroupMap K
  have hm (a : A) : f a ∈ H.map f ↔ a ∈ H := by
    change a ∈ (H.map f).comap f ↔ _
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hk]
  have key (x y : K) : QuotientGroup.leftRel (H.subgroupOf K) x y ↔
      QuotientGroup.leftRel ((H.map f).subgroupOf (K.map f)) (F x) (F y) := by
    simp only [QuotientGroup.leftRel_apply]
    change x.val⁻¹ * y.val ∈ H ↔ (f x.val)⁻¹ * f y.val ∈ H.map f
    rw [← map_inv, ← map_mul, hm]
  refine Equiv.ofBijective (Quotient.map' F (fun x y => (key x y).mp)) ⟨?_, ?_⟩
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    obtain ⟨y, hy⟩ := f.subgroupMap_surjective K x
    exact ⟨y, (Quotient.map'_mk'' F _ y).trans (congrArg Quotient.mk'' hy)⟩

@[simp] theorem imageEquiv_mk (f : A →* B) (H K : Subgroup A)
    (hk : f.ker ≤ H) (a : K) :
    imageEquiv f H K hk (QuotientGroup.mk a) =
      QuotientGroup.mk (f.subgroupMap K a) := rfl

/-- Integral congruence cosets and projective congruence cosets agree,
 including the representative map used in trace sums. -/
def projectiveEquiv (N M : ℕ) :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M) ≃
    gamma M ⧸ (gamma N).subgroupOf (gamma M) :=
  imageEquiv integralLabel _ _ (integralLabel_ker_le N)

/-- The same integral cosets parameterize Mathlib's actual GL trace. -/
def matrixEquiv (N M : ℕ) :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M) ≃
    level M ⧸ (level N).subgroupOf (level M) :=
  imageEquiv (SpecialLinearGroup.mapGL ℝ) _ _ (by
    intro a ha
    have he : a = 1 := SpecialLinearGroup.mapGL_injective
      (ha.trans (map_one (SpecialLinearGroup.mapGL ℝ)).symm)
    rw [he]
    exact Subgroup.one_mem _)

/-- A representative-compatible bridge from the classical trace quotient
 to the projective quotient used for Petersson integration. -/
def traceEquiv (N M : ℕ) :
    level M ⧸ (level N).subgroupOf (level M) ≃
    gamma M ⧸ (gamma N).subgroupOf (gamma M) :=
  (matrixEquiv N M).symm.trans (projectiveEquiv N M)

theorem traceEquiv_mk (N M : ℕ) (a : CongruenceSubgroup.Gamma0 M) :
    traceEquiv N M (QuotientGroup.mk ((SpecialLinearGroup.mapGL ℝ).subgroupMap _ a)) =
      QuotientGroup.mk (integralLabel.subgroupMap _ a) := by
  change (projectiveEquiv N M)
    ((matrixEquiv N M).symm ((matrixEquiv N M) (QuotientGroup.mk a))) = _
  rw [Equiv.symm_apply_apply]
  rfl

#print axioms imageEquiv
#print axioms imageEquiv_mk
#print axioms projectiveEquiv
#print axioms matrixEquiv
#print axioms traceEquiv
#print axioms traceEquiv_mk

end AsymptoticClassicalCosets
