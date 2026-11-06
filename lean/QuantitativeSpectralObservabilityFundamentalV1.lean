module

public import QuantitativeSpectralObservabilityCoverV1
public import AsymptoticModularFundamentalV1
public import AsymptoticProjectiveCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticModularDomain
open scoped MatrixGroups Modular Pointwise

theorem integralLabel_mem_gamma_iff (N : ℕ) (A : SL(2,ℤ)) :
    integralLabel A∈gamma N ↔ A∈CongruenceSubgroup.Gamma0 N := by
  change A∈((CongruenceSubgroup.Gamma0 N).map integralLabel).comap integralLabel ↔ _
  rw [Subgroup.comap_map_eq_self (integralLabel_ker_le N)]

def integralOne (A : SL(2,ℤ)) : gamma 1 :=
  ⟨integralLabel A, (integralLabel_mem_gamma_iff 1 A).mpr (by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact Subsingleton.elim _ _)⟩

/-- The literal finite-coset fundamental set uses exactly the same
representatives as the wide compact sampler. -/
def fundamentalSet (N : ℕ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    (integralLabel q.out)⁻¹ • 𝒟

theorem fundamentalSet_measurable (N : ℕ) (hN : 0<N) : MeasurableSet (fundamentalSet N) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply MeasurableSet.iUnion
  intro q
  rw [← preimage_smul_inv]
  exact ModularGroup.isClosed_fd.measurableSet.preimage
    (AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measurable

theorem fundamentalSet_orbit_meets (N : ℕ) (z : ℍ) :
    ∃ h : gamma N, h.val • z∈fundamentalSet N := by
  obtain ⟨A,hA⟩ := ModularGroup.exists_smul_mem_fd z
  let q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N := QuotientGroup.mk A
  have hm : q.out⁻¹*A∈CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  refine ⟨⟨integralLabel (q.out⁻¹*A),(integralLabel_mem_gamma_iff N _).mpr hm⟩,?_⟩
  apply mem_iUnion.mpr
  refine ⟨q,A • z,hA,?_⟩
  simp only [map_mul,map_inv,mul_smul,integralLabel_action]

private theorem shifted_representatives_ne (N : ℕ) (h : gamma N) (hh : h≠1)
    (q r : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    h.val*(integralLabel q.out)⁻¹ ≠ (integralLabel r.out)⁻¹ := by
  intro he
  have heq : integralLabel r.out*h.val=integralLabel q.out := by
    have h := congrArg (fun a => integralLabel r.out*a*integralLabel q.out) he
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,inv_mul_cancel,mul_one] using h
  have hm : integralLabel (r.out⁻¹*q.out)∈gamma N := by
    rw [map_mul,map_inv,←heq,inv_mul_cancel_left]
    exact h.property
  have hqr : r=q := by
    have hm' := (integralLabel_mem_gamma_iff N _).mp hm
    have he' := QuotientGroup.eq.mpr hm'
    simpa only [QuotientGroup.out_eq'] using he'
  subst r
  have hh1 : h.val=1 := by
    apply mul_left_cancel (a:=integralLabel q.out)
    simpa only [mul_one] using heq
  exact hh (Subtype.ext hh1)

/-- Scalar signs are removed before invoking the modular fundamental
domain, so the finite-coset union is a genuine Gamma0 fundamental domain. -/
theorem fundamentalSet_isFundamental (N : ℕ) (hN : 0<N) :
    IsFundamentalDomain (gamma N) (fundamentalSet N) (volume : Measure ℍ) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply IsFundamentalDomain.mk'' (fundamentalSet_measurable N hN).nullMeasurableSet
    (Filter.Eventually.of_forall (fundamentalSet_orbit_meets N))
  · intro h hh
    change AEDisjoint volume (h.val • fundamentalSet N) (fundamentalSet N)
    simp only [fundamentalSet,smul_set_iUnion,AEDisjoint.iUnion_left_iff,
      AEDisjoint.iUnion_right_iff]
    intro r q
    let a : gamma 1 := ⟨h.val*(integralLabel q.out)⁻¹,
      (gamma 1).mul_mem (gamma_le_of_dvd (one_dvd N) h.property)
        ((gamma 1).inv_mem (integralOne q.out).property)⟩
    let b : gamma 1 := (integralOne r.out)⁻¹
    have hab : a≠b := by
      intro he
      exact shifted_representatives_ne N h hh q r (congrArg Subtype.val he)
    have hd := gamma_one_fundamental.aedisjoint hab
    change AEDisjoint volume ((h.val*(integralLabel q.out)⁻¹) • 𝒟)
      ((integralLabel r.out)⁻¹ • 𝒟) at hd
    simpa only [←mul_smul] using hd
  · intro h
    exact (AsymptoticRationalGroup.measurePreserving h.val).quasiMeasurePreserving

theorem modular_fd_subset_wideBox {H : ℝ} {z : ℍ} (hz : z∈𝒟) (hH : z.im≤H) :
    z∈wideBox H := by
  have hr : |z.re|≤(1:ℝ)/2 := hz.2
  have hi := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy : (1:ℝ)/4≤z.im := by nlinarith [z.im_pos]
  exact ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2],hy,hH⟩

def fundamentalCompact (N : ℕ) (H : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    (integralLabel q.out)⁻¹ • (𝒟 ∩ {z : ℍ | z.im≤H})

theorem fundamentalCompact_subset_wide (N : ℕ) (H : ℝ) :
    fundamentalCompact N H ⊆ wideCompactCover N H := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨q,w,modular_fd_subset_wideBox hw.1 hw.2,rfl⟩

theorem fundamentalSet_subset_compact_tail (N : ℕ) (H : ℝ) :
    fundamentalSet N ⊆ fundamentalCompact N H ∪ wideTailCover N H := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  by_cases hH : w.im≤H
  · exact Or.inl (mem_iUnion.mpr ⟨q,w,⟨hw,hH⟩,rfl⟩)
  · right
    apply mem_iUnion.mpr
    refine ⟨q,w,?_,rfl⟩
    have hr : |w.re|≤(1:ℝ)/2 := hw.2
    exact ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2],lt_of_not_ge hH⟩

#print axioms fundamentalSet_isFundamental
#print axioms fundamentalCompact_subset_wide
#print axioms fundamentalSet_subset_compact_tail

end QuantitativeSpectralObservability
