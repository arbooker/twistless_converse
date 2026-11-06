module

public import AsymptoticFiberProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteFiberInduction

open ContinuousLinearMap AsymptoticRegularTrace
open scoped lp ComplexConjugate Classical

/-- Counting-measure normalization for a fibre of size n. -/
noncomputable def coefficient (n : ℕ) : ℂ := ((Real.sqrt (n:ℝ))⁻¹:ℝ)

theorem coefficient_ne_zero {n : ℕ} (hn : 0<n) : coefficient n≠0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact inv_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'

theorem coefficient_norm_sq {n : ℕ} (hn : 0<n) : ‖coefficient n‖^2=(n:ℝ)⁻¹ := by
  rw [coefficient,Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,
    Real.sq_sqrt (by exact_mod_cast hn.le)]

variable {ι κ : Type*} (p : ι → κ) (n : ℕ) (hn : 0<n)
variable [∀ y,Finite {i // p i=y}]
variable (hc : ∀ y,Nat.card {i // p i=y}=n)

include hn hc

theorem fibre_hasSum (y : κ) :
    HasSum (fun _ : {i // p i=y} => ‖coefficient n‖^2) 1 := by
  classical
  let := Fintype.ofFinite {i // p i=y}
  have hcard : Fintype.card {i // p i=y}=n := by
    rw [← Nat.card_eq_fintype_card]
    exact hc y
  have he : (∑ _ : {i // p i=y},‖coefficient n‖^2)=1 := by
    simp only [coefficient_norm_sq hn,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')
  rw [← he]
  exact hasSum_fintype _

noncomputable def isometry : ℓ²(κ,ℂ) →ₗᵢ[ℂ] ℓ²(ι,ℂ) :=
  AsymptoticFiberIsometry.isometry p (fun _ => coefficient n) (fibre_hasSum p n hn hc)

theorem isometry_apply (f : ℓ²(κ,ℂ)) (i : ι) :
    isometry p n hn hc f i=coefficient n*f (p i) := rfl

noncomputable def projection : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ) :=
  (isometry p n hn hc).toContinuousLinearMap.comp (isometry p n hn hc).toContinuousLinearMap.adjoint

theorem projection_matrix (i j : ι) : projection p n hn hc (delta j) i=
    if p i=p j then ((n:ℝ)⁻¹:ℂ) else 0 := by
  classical
  have he := AsymptoticFiberIsometry.projection_apply_delta p (fun _ => coefficient n)
    (fibre_hasSum p n hn hc) i j
  change projection p n hn hc (delta j) i=
    if p i=p j then coefficient n*conj (coefficient n) else 0 at he
  simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,coefficient_norm_sq hn,
    Complex.ofReal_inv] using he

theorem range_iff (v : ℓ²(ι,ℂ)) :
    v∈(isometry p n hn hc).toLinearMap.range ↔ ∃ f : κ → ℂ,∀ i,v i=f (p i) := by
  change v∈(AsymptoticFiberIsometry.linear p (fun _ => coefficient n)
    (fibre_hasSum p n hn hc)).range ↔ _
  rw [AsymptoticFiberIsometry.range_iff]
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨fun y => coefficient n*f y,hf⟩
  · rintro ⟨f,hf⟩
    refine ⟨fun y => f y/coefficient n,?_⟩
    intro i
    rw [hf]
    field_simp [coefficient_ne_zero hn]

#print axioms coefficient_ne_zero
#print axioms coefficient_norm_sq
#print axioms fibre_hasSum
#print axioms isometry_apply
#print axioms projection_matrix
#print axioms range_iff

end AsymptoticFiniteFiberInduction
