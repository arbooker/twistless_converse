module

public import AsymptoticClassicalFrickeGroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCosets

open Matrix AsymptoticClassicalCusp AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels AsymptoticFreshMatrices UpperHalfPlane
open scoped MatrixGroups

variable {A B : Type*} [Group A] [Group B]

/-- Representative map into a specified image subgroup. -/
def imageRepresentative (f : A →* B) (K : Subgroup A) (J : Subgroup B)
    (hJ : K.map f = J) (a : K) : J :=
  ⟨f a.val, hJ ▸ ⟨a.val, a.property, rfl⟩⟩

/-- The relative image-coset equivalence with its two image subgroups
 rewritten to concrete groups. -/
def imageEquivOfEq (f : A →* B) (H K : Subgroup A) (L J : Subgroup B)
    (hk : f.ker ≤ H) (hL : H.map f = L) (hJ : K.map f = J) :
    K ⧸ H.subgroupOf K ≃ J ⧸ L.subgroupOf J := by
  subst L
  subst J
  exact imageEquiv f H K hk

theorem imageEquivOfEq_mk (f : A →* B) (H K : Subgroup A) (L J : Subgroup B)
    (hk : f.ker ≤ H) (hL : H.map f = L) (hJ : K.map f = J) (a : K) :
    imageEquivOfEq f H K L J hk hL hJ (QuotientGroup.mk a) =
      QuotientGroup.mk (imageRepresentative f K J hJ a) := by
  subst L
  subst J
  rfl

variable (N M : ℕ) (hN : 0 < N)

def frickeMatrixRepresentative (a : CongruenceSubgroup.Gamma0 M) : frickeOldLevel N M hN :=
  imageRepresentative (frickeMatrixLabel N hN) _ _ (frickeMatrixLabel_image N M hN) a

def frickeProjectiveRepresentative (a : CongruenceSubgroup.Gamma0 M) : frickeOldGroup N M hN :=
  imageRepresentative (frickeProjectiveLabel N hN) _ _ (frickeProjectiveLabel_image N M hN) a

def frickeMatrixEquiv :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M) ≃
    frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN) :=
  imageEquivOfEq (frickeMatrixLabel N hN) _ _ _ _ (by
    intro a ha
    have he : a = 1 := frickeMatrixLabel_injective N hN
      (ha.trans (map_one (frickeMatrixLabel N hN)).symm)
    rw [he]
    exact Subgroup.one_mem _)
    (frickeMatrixLabel_small N hN) (frickeMatrixLabel_image N M hN)

def frickeProjectiveEquiv :
    CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M) ≃
    frickeOldGroup N M hN ⧸ (gamma N).subgroupOf (frickeOldGroup N M hN) :=
  imageEquivOfEq (frickeProjectiveLabel N hN) _ _ _ _
    (frickeProjectiveLabel_ker_le N hN)
    (frickeProjectiveLabel_small N hN) (frickeProjectiveLabel_image N M hN)

def frickeTraceEquiv :
    frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN) ≃
    frickeOldGroup N M hN ⧸ (gamma N).subgroupOf (frickeOldGroup N M hN) :=
  (frickeMatrixEquiv N M hN).symm.trans (frickeProjectiveEquiv N M hN)

theorem frickeTraceEquiv_mk (a : CongruenceSubgroup.Gamma0 M) :
    frickeTraceEquiv N M hN (QuotientGroup.mk (frickeMatrixRepresentative N M hN a)) =
      QuotientGroup.mk (frickeProjectiveRepresentative N M hN a) := by
  have hm : frickeMatrixEquiv N M hN (QuotientGroup.mk a) =
      QuotientGroup.mk (frickeMatrixRepresentative N M hN a) := imageEquivOfEq_mk ..
  have hp : frickeProjectiveEquiv N M hN (QuotientGroup.mk a) =
      QuotientGroup.mk (frickeProjectiveRepresentative N M hN a) := imageEquivOfEq_mk ..
  rw [← hm]
  exact (congrArg (frickeProjectiveEquiv N M hN)
    ((frickeMatrixEquiv N M hN).symm_apply_apply _)).trans hp

omit M in
/-- The conjugated projective representative has exactly the action of
 its honest real matrix, including the inverse action used in a trace. -/
theorem fricke_label_action (a : SL(2, ℤ)) (z : ℍ) :
    frickeProjectiveLabel N hN a • z = frickeMatrixLabel N hN a • z := by
  have hw (x : ℍ) : frickeLabel N hN • x = frickeReal N hN • x :=
    AsymptoticRationalBranches.ofMatrix_action _ _ x
  have hi (x : ℍ) : (frickeLabel N hN)⁻¹ • x = (frickeReal N hN)⁻¹ • x := by
    apply (MulAction.bijective (frickeLabel N hN)).injective
    change frickeLabel N hN • ((frickeLabel N hN)⁻¹ • x) =
      frickeLabel N hN • ((frickeReal N hN)⁻¹ • x)
    rw [smul_inv_smul, hw, smul_inv_smul]
  change (frickeLabel N hN * integralLabel a * (frickeLabel N hN)⁻¹) • z =
    (frickeReal N hN * SpecialLinearGroup.mapGL ℝ a * (frickeReal N hN)⁻¹) • z
  simp only [mul_smul, hw, hi, integralLabel_action]
  rfl

#print axioms imageEquivOfEq
#print axioms imageEquivOfEq_mk
#print axioms frickeTraceEquiv
#print axioms frickeTraceEquiv_mk
#print axioms fricke_label_action

end AsymptoticClassicalCosets
