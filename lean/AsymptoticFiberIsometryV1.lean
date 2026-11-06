module

public import AsymptoticRegularTraceV1
public import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiberIsometry

open AsymptoticRegularTrace ContinuousLinearMap
open scoped lp InnerProduct ComplexConjugate

variable {ι κ : Type*} (p : ι → κ) (r : ι → ℂ)
variable (hr : ∀ y,HasSum (fun i : {i // p i=y} => ‖r i.val‖^2) 1)

include hr

/-- Normalizing each fibre in counting measure makes weighted pullback
preserve square norms, with no finiteness assumption on the fibres. -/
theorem square_hasSum (f : ℓ²(κ,ℂ)) :
    HasSum (fun i => ‖r i*f (p i)‖^2) (‖f‖^2) := by
  have hf : HasSum (fun y => ‖f y‖^2) (‖f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) f
  have hy (y : κ) : HasSum (fun i : {i // p i=y} => ‖r i.val*f (p i.val)‖^2)
      (‖f y‖^2) := by
    have he := (hr y).mul_right (‖f y‖^2)
    rw [one_mul] at he
    apply he.congr_fun
    intro i
    rw [norm_mul,mul_pow,i.property]
  have hs : Summable (fun i : Σ y,{i // p i=y} => ‖r i.2.val*f (p i.2.val)‖^2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun y => (hy y).summable,by simpa only [(hy _).tsum_eq] using hf.summable⟩
  exact (Equiv.sigmaFiberEquiv p).hasSum_iff.mp (hf.sigma_of_hasSum hy hs)

noncomputable def linear : ℓ²(κ,ℂ) →ₗ[ℂ] ℓ²(ι,ℂ) where
  toFun f := ⟨fun i => r i*f (p i),memℓp_gen (by
    simpa using (square_hasSum p r hr f).summable)⟩
  map_add' f g := by
    apply lp.ext
    funext i
    change r i*(f (p i)+g (p i))=r i*f (p i)+r i*g (p i)
    ring
  map_smul' c f := by
    apply lp.ext
    funext i
    change r i*(c*f (p i))=c*(r i*f (p i))
    ring

theorem linear_apply (f : ℓ²(κ,ℂ)) (i : ι) : linear p r hr f i=r i*f (p i) := rfl

theorem linear_norm (f : ℓ²(κ,ℂ)) : ‖linear p r hr f‖=‖f‖ := by
  have hn : HasSum (fun i => ‖linear p r hr f i‖^2) (‖linear p r hr f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) (linear p r hr f)
  have he := hn.unique (square_hasSum p r hr f)
  nlinarith [norm_nonneg (linear p r hr f),norm_nonneg f]

noncomputable def isometry : ℓ²(κ,ℂ) →ₗᵢ[ℂ] ℓ²(ι,ℂ) :=
  { linear p r hr with norm_map' := linear_norm p r hr }

/-- The range characterization does not assume square summability of
the unweighted function. It follows from the fibre normalization. -/
theorem range_iff (v : ℓ²(ι,ℂ)) : v∈(linear p r hr).range ↔
    ∃ f : κ → ℂ,∀ i,v i=r i*f (p i) := by
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨f,fun _ => rfl⟩
  · rintro ⟨f,hf⟩
    have hv : HasSum (fun i => ‖v i‖^2) (‖v‖^2) := by
      simpa using lp.hasSum_norm (p:=2) (by norm_num) v
    have hy (y : κ) : HasSum (fun i : {i // p i=y} => ‖v i.val‖^2) (‖f y‖^2) := by
      have he := (hr y).mul_right (‖f y‖^2)
      rw [one_mul] at he
      apply he.congr_fun
      intro i
      rw [hf,norm_mul,mul_pow,i.property]
    have hs := ((Equiv.sigmaFiberEquiv p).hasSum_iff.mpr hv).sigma hy
    let f' : ℓ²(κ,ℂ) := ⟨f,memℓp_gen (by simpa using hs.summable)⟩
    refine ⟨f',?_⟩
    apply lp.ext
    funext i
    exact (hf i).symm

#print axioms square_hasSum
#print axioms linear_apply
#print axioms linear_norm
#print axioms range_iff

end AsymptoticFiberIsometry
