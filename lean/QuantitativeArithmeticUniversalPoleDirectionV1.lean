module
public import QuantitativeArithmeticUniversalPoleVectorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Every universal principal vector obeys the analytic cross-relations of
one common Laurent regularization. -/
theorem IsLeadingVector.cross_regularization {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G x v) (u : ℕ) (g : ℂ → ι → ℂ)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g z i) x)
    (he : ∀ᶠ z in 𝓝[≠] x, (z-x)^u • G z=g z) (i j : ι) :
    g x i*v j=g x j*v i := by
  classical
  let A : ℂ → ι → ℂ := fun z t =>
    g z i*(if t=j then 1 else 0)-g z j*(if t=i then 1 else 0)
  have ha (t : ι) : AnalyticAt ℂ (fun z => A z t) x :=
    ((hg i).mul analyticAt_const).sub ((hg j).mul analyticAt_const)
  have hs (z : ℂ) (w : ι → ℂ) : ∑ t, A z t*w t=g z i*w j-g z j*w i := by
    simp [A,sub_mul,Finset.sum_sub_distrib]
  have hzero : (fun z => ∑ t, A z t*G z t)=ᶠ[𝓝[≠] x] (fun _ => (0:ℂ)) := by
    filter_upwards [he] with z hz
    have hi : (z-x)^u*G z i=g z i := congrFun hz i
    have hj : (z-x)^u*G z j=g z j := congrFun hz j
    rw [hs,← hi,← hj]
    ring
  have h := hv.2 A (fun _ => 0) ha analyticAt_const hzero
  rw [hs] at h
  exact sub_eq_zero.mp h

/-- A universal principal vector has exactly the nonzero coordinates of the
highest Laurent vector, even if it was constructed using a different set of
analytic equations. -/
theorem IsLeadingVector.zero_iff_regularization {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G x v) (u : ℕ) (g : ℂ → ι → ℂ)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g z i) x) (hg0 : g x≠0)
    (he : ∀ᶠ z in 𝓝[≠] x, (z-x)^u • G z=g z) (j : ι) :
    v j=0 ↔ g x j=0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, g x i≠0 := by
    by_contra! h
    exact hg0 (funext h)
  have hvi : v i≠0 := by
    intro hvi
    apply hv.1
    funext t
    have ht := hv.cross_regularization u g hg he i t
    rw [hvi,mul_zero] at ht
    exact (mul_eq_zero.mp ht).resolve_left hi
  have hj := hv.cross_regularization u g hg he i j
  constructor
  · intro h
    rw [h,mul_zero] at hj
    exact (mul_eq_zero.mp hj.symm).resolve_right hvi
  · intro h
    rw [h,zero_mul] at hj
    exact (mul_eq_zero.mp hj).resolve_left hi

/-- Nonvanishing of a specified pole coordinate survives a change of
universal principal vector. Useful when adjoining lower-point germs. -/
theorem IsLeadingVector.coordinate_zero_iff {G : ℂ → ι → ℂ} {x : ℂ} {v w : ι → ℂ}
    (hv : IsLeadingVector G x v) (hw : IsLeadingVector G x w)
    (hG : ∀ j, MeromorphicAt (fun z => G z j) x)
    (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<0) (j : ι) :
    v j=0 ↔ w j=0 := by
  obtain ⟨u,g,_,hg,hg0,he⟩ := SmallLevelPoleGrid.leading_vector hG hpole
  have ha : ∀ i, AnalyticAt ℂ (fun z => g z i) x := analyticAt_pi_iff.mp hg
  exact (hv.zero_iff_regularization u g ha hg0 he j).trans
    (hw.zero_iff_regularization u g ha hg0 he j).symm

#print axioms IsLeadingVector.cross_regularization
#print axioms IsLeadingVector.zero_iff_regularization
#print axioms IsLeadingVector.coordinate_zero_iff
end QuantitativeArithmeticUniversalPoleVector
