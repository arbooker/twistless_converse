module

public import QuantitativeEulerOldProjectionPhysicalDensityV1
public import AsymptoticQuotientEquivarianceV1
public import AsymptoticCosetTraceSumsV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionPhysical

open AsymptoticNestedQuotients AsymptoticRegularTrace AsymptoticQuotientOperators
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α] (H : Subgroup G) [H.FiniteIndex]

local instance rightFinite : Finite (Classes H) := Finite.of_equiv (G ⧸ H)
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
local instance rightFintype : Fintype (Classes H) := Fintype.ofFinite _

variable (f : α → ℂ) (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)

/-- The actual finite vector of translates of an H-automorphic function. -/
def orbitValue (q : Classes H) (x : α) : ℂ :=
  QuantitativeMaass.CosetTrace.value H f hinv
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q) x

omit [H.FiniteIndex] in
theorem orbitValue_classOf (g : G) (x : α) :
    orbitValue H f hinv (classOf H g) x = f (g • x) := by
  change f (g⁻¹⁻¹ • x) = _
  rw [inv_inv]

def orbitVector (x : α) : ℓ²(Classes H,ℂ) :=
  ⟨fun q => orbitValue H f hinv q x, memℓp_gen (hasSum_fintype _).summable⟩

theorem orbitVector_apply (x : α) (q : Classes H) :
    orbitVector H f hinv x q = orbitValue H f hinv q x := rfl

theorem orbitVector_classOf (x : α) (g : G) :
    orbitVector H f hinv x (classOf H g) = f (g • x) := orbitValue_classOf H f hinv g x

theorem orbitVector_translate (g : G) (x : α) (q : Classes H) :
    orbitVector H f hinv (g • x) q = orbitVector H f hinv x (rightMulEquiv H g q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change orbitVector H f hinv (g • x) (classOf H a) =
      orbitVector H f hinv x (rightMulEquiv H g (classOf H a))
    rw [rightMulEquiv_classOf, orbitVector_classOf, orbitVector_classOf, mul_smul]

section Matrix
variable {ι : Type*} [Fintype ι]

theorem finite_matrix_apply (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (v : ℓ²(ι,ℂ)) (i : ι) :
    B v i = ∑ j, matrix B i j * v j := by
  classical
  have hv := (lp.hasSum_single (p := 2) (by norm_num) v).tsum_eq
  rw [tsum_fintype] at hv
  have hs (j : ι) : lp.single 2 j (v j) = v j • delta j := by
    rw [delta, ← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  simp_rw [hs] at hv
  conv_lhs => rw [← hv, map_sum]
  change (∑ j, B (v j • delta j)) i = _
  simp only [map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, matrix, mul_comm]
end Matrix

variable (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (hB : Equivariant B)

/-- Apply an actual equivariant root matrix to the finite orbit vector,
then evaluate at the identity coset. -/
def orbitOperator (x : α) : ℂ := B (orbitVector H f hinv x) (classOf H 1)

include hB in
theorem orbitOperator_translate (g : G) (x : α) :
    orbitOperator H f hinv B (g • x) = B (orbitVector H f hinv x) (classOf H g) := by
  rw [orbitOperator, finite_matrix_apply, finite_matrix_apply]
  simp_rw [orbitVector_translate]
  have he := Equiv.sum_comp (rightMulEquiv H g)
    (fun j => matrix B (classOf H g) j * orbitVector H f hinv x j)
  rw [← he]
  apply Finset.sum_congr rfl
  intro q _
  have hh := hB g (classOf H 1) q
  rw [rightMulEquiv_classOf, one_mul] at hh
  rw [hh]

include hB in
theorem orbitOperator_invariant (h : H) (x : α) :
    orbitOperator H f hinv B (h.val • x) = orbitOperator H f hinv B x := by
  rw [orbitOperator_translate H f hinv B hB]
  have he : classOf H h.val = classOf H 1 := by
    rw [classOf_eq_iff]
    simpa only [inv_one, mul_one] using h.property
  rw [he]
  rfl

/-- Exact reconstruction of the transformed finite vector. This makes
polynomial identities of root matrices transferable to actual functions. -/
theorem orbitVector_operator (x : α) :
    orbitVector H (orbitOperator H f hinv B) (orbitOperator_invariant H f hinv B hB) x =
      B (orbitVector H f hinv x) := by
  ext q
  induction q using Quotient.inductionOn with
  | h g =>
    change orbitVector H (orbitOperator H f hinv B)
      (orbitOperator_invariant H f hinv B hB) x (classOf H g) = _
    rw [orbitVector_classOf]
    exact orbitOperator_translate H f hinv B hB g x

/-- At the identity coordinate, the root old projector is exactly the
normalized physical finite-coset trace. -/
theorem orbitOperator_old {J : Subgroup G} (hHJ : H ≤ J) (x : α) :
    orbitOperator H f hinv (space hHJ).starProjection x =
      ((H.subgroupOf J).index : ℂ)⁻¹ *
        ∑' q : J ⧸ H.subgroupOf J, f (q.out.val⁻¹ • x) := by
  let : Fintype (J ⧸ H.subgroupOf J) := Fintype.ofFinite _
  rw [orbitOperator, projection_apply]
  have hs := fibre_sum_eq_coset_sum hHJ
    (fun q : J ⧸ H.subgroupOf J => q.out) (Equiv.refl _)
    (fun q => q.out_eq.symm) (fun q => orbitVector H f hinv x q) 1
  rw [forget_classOf, hs, tsum_fintype]
  simp only [orbitVector_classOf, mul_one]

/-- Composition of equivariant root matrices acts by literal composition
on automorphic functions. This supplies polynomial transfer without any
analytic approximation or spectral hypothesis. -/
theorem orbitOperator_comp (C : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hC : Equivariant C) (x : α) :
    orbitOperator H (orbitOperator H f hinv C) (orbitOperator_invariant H f hinv C hC) B x =
      orbitOperator H f hinv (B.comp C) x := by
  rw [orbitOperator, orbitVector_operator H f hinv C hC x]
  rfl

#print axioms orbitOperator_old
#print axioms orbitOperator_comp
#print axioms orbitVector_translate
#print axioms finite_matrix_apply
#print axioms orbitOperator_invariant
#print axioms orbitVector_operator
end QuantitativeEulerOldProjectionPhysical
