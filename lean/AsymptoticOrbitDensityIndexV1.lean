module

public import AsymptoticOrbitDensityFundamentalV1
public import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticOrbitDensity

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G α : Type*} [Group G] [MulAction G α]

/-- A coset decomposition with its representative formula exposed. -/
noncomputable def leftProductEquiv (H : Subgroup G) : (G ⧸ H) × H ≃ G where
  toFun a := a.1.out*a.2.val
  invFun g := (QuotientGroup.mk g,⟨(Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹*g,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ H))⟩)
  left_inv := by
    rintro ⟨q,h⟩
    have hq : (QuotientGroup.mk (q.out*h.val) : G ⧸ H)=q := by
      apply Eq.trans _ (QuotientGroup.out_eq' q)
      apply QuotientGroup.eq.mpr
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using H.inv_mem h.property
    apply Prod.ext hq
    apply Subtype.ext
    change (Quotient.out (QuotientGroup.mk (q.out*h.val) : G ⧸ H))⁻¹*(q.out*h.val)=h.val
    rw [hq,inv_mul_cancel_left]
  right_inv g := by
    change (Quotient.out (QuotientGroup.mk g : G ⧸ H))*
      ((Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹*g)=g
    exact mul_inv_cancel_left _ _

/-- An orbit density normalized on a finite-index subgroup has total
mass equal to that index on the whole group. -/
theorem subgroup_mass_eq_index (H : Subgroup G) [Finite (G ⧸ H)]
    (f : α → ℝ≥0∞) (hn : ∀ x,∑' h : H,f (h.val • x)=1) (x : α) :
    (∑' g : G,f (g • x))=(H.index:ℝ≥0∞) := by
  classical
  let E : G ≃ (G ⧸ H) × H := (leftProductEquiv H).symm
  have he (q : G ⧸ H) (h : H) : E.symm (q,h)=q.out*h.val := rfl
  have hi : (∑' g : G,f (g • x))=∑' g : G,f (g⁻¹ • x) :=
    ((Equiv.inv G).tsum_eq (fun g => f (g • x))).symm
  rw [hi,← E.symm.tsum_eq (fun g => f (g⁻¹ • x)),ENNReal.tsum_prod']
  have hs (q : G ⧸ H) : (∑' h : H,f ((E.symm (q,h))⁻¹ • x))=1 := by
    simp only [he,mul_inv_rev,mul_smul]
    have hsum := (Equiv.inv H).tsum_eq (fun h : H => f (h.val • (q.out⁻¹ • x)))
    exact hsum.trans (hn (q.out⁻¹ • x))
  simp only [hs]
  let := Fintype.ofFinite (G ⧸ H)
  rw [tsum_fintype]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Subgroup.index,Fintype.card_eq_nat_card]

variable [Countable G] [MeasurableSpace α]

/-- Exact finite-index covolume scaling, proved by integrating the
normalized subgroup density on one ambient fundamental domain. -/
theorem integral_eq_index_mul_volume (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (H : Subgroup G) [Finite (G ⧸ H)]
    (f : α → ℝ≥0∞) (hf : Measurable f)
    (hn : ∀ x,∑' h : H,f (h.val • x)=1)
    (s : Set α) (hs : IsFundamentalDomain G s μ) :
    (∫⁻ x,f x ∂μ)=(H.index:ℝ≥0∞)*μ s :=
  integral_eq_mass_mul_volume μ hmp f hf H.index (subgroup_mass_eq_index H f hn) s hs

#print axioms leftProductEquiv
#print axioms subgroup_mass_eq_index
#print axioms integral_eq_index_mul_volume

end AsymptoticOrbitDensity
