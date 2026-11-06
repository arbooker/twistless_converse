module

public import AsymptoticFiniteFiberInductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteFiberInduction

open ContinuousLinearMap AsymptoticRegularTrace InnerProductSpace
open scoped lp InnerProduct ComplexConjugate Classical

variable {ι κ : Type*} (p : ι → κ) (n : ℕ) (hn : 0<n)
variable [∀ y,Finite {i // p i=y}]
variable (hc : ∀ y,Nat.card {i // p i=y}=n)

theorem adjoint_apply (v : ℓ²(ι,ℂ)) (y : κ) :
    (isometry p n hn hc).toContinuousLinearMap.adjoint v y=
      conj (coefficient n)*(∑' i : {i // p i=y},v i.val) := by
  rw [← delta_inner,adjoint_inner_right,lp.inner_eq_tsum]
  change (∑' i,⟪isometry p n hn hc (delta y) i,v i⟫_ℂ)=_
  have hs : Function.support (fun i => ⟪isometry p n hn hc (delta y) i,v i⟫_ℂ)⊆{i | p i=y} := by
    intro i hi
    by_contra h
    change p i≠y at h
    apply hi
    simp [isometry_apply,delta,h]
  rw [← tsum_subtype_eq_of_support_subset hs]
  have hv : ∀ i : {i // p i=y},isometry p n hn hc (delta y) i.val=coefficient n := by
    intro i
    rw [isometry_apply]
    simp [delta,i.property]
  simp_rw [hv,RCLike.inner_apply]
  rw [tsum_mul_right,mul_comm]
  rfl

/-- The actual orthogonal projection is the finite fibre average on
arbitrary square-summable vectors, not only on delta vectors. -/
theorem projection_apply (v : ℓ²(ι,ℂ)) (i : ι) :
    projection p n hn hc v i=((n:ℂ)⁻¹)*(∑' j : {j // p j=p i},v j.val) := by
  change isometry p n hn hc ((isometry p n hn hc).toContinuousLinearMap.adjoint v) i=_
  rw [isometry_apply,adjoint_apply,← mul_assoc,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,coefficient_norm_sq hn,Complex.ofReal_inv,Complex.ofReal_natCast]

theorem projection_eq_zero_iff (v : ℓ²(ι,ℂ)) : projection p n hn hc v=0 ↔
    ∀ y, (∑' i : {i // p i=y},v i.val)=0 := by
  constructor
  · intro hv y
    have hsur : Function.Surjective p := by
      intro y
      have hcard : Nat.card {i // p i=y}≠0 := by rw [hc]; exact hn.ne'
      have : Nonempty {i // p i=y} := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hcard) |>.1
      obtain ⟨i,hi⟩ := this
      exact ⟨i,hi⟩
    obtain ⟨i,rfl⟩ := hsur y
    have he := congrArg (fun w : ℓ²(ι,ℂ) => w i) hv
    rw [projection_apply] at he
    have hn' : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hn')
  · intro hv
    apply lp.ext
    funext i
    rw [projection_apply,hv,mul_zero]
    rfl

#print axioms adjoint_apply
#print axioms projection_apply
#print axioms projection_eq_zero_iff

end AsymptoticFiniteFiberInduction
