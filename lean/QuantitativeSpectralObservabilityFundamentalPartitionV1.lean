module

public import QuantitativeSpectralObservabilityFundamentalRetainedV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticOrbitDiagonal
open scoped lp

theorem fundamentalTransfer_supported (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    (fundamentalTransfer N hε ht x).comp (corner (fundamentalSet N) x)=
      fundamentalTransfer N hε ht x := by
  by_cases hx : fundamentalGood N x
  · calc
      _ = (fundamentalTransfer N hε ht x).comp
        ((fundamentalTransfer N hε ht x).adjoint.comp (fundamentalTransfer N hε ht x)) :=
          congrArg (fun B => (fundamentalTransfer N hε ht x).comp B)
            (fundamentalTransfer_gram N hε ht x hx).symm
      _ = ((fundamentalTransfer N hε ht x).comp
        (fundamentalTransfer N hε ht x).adjoint).comp (fundamentalTransfer N hε ht x) :=
          (comp_assoc _ _ _).symm
      _ = (projection N hε ht x).comp (fundamentalTransfer N hε ht x) :=
        congrArg (fun B => B.comp (fundamentalTransfer N hε ht x))
          (fundamentalTransfer_cogram N hε ht x hx)
      _ = _ := by
        apply ContinuousLinearMap.ext
        intro v
        exact (Submodule.starProjection_eq_self_iff).mpr (fundamentalTransfer_range N hε ht x v)
  · simp only [fundamentalTransfer,dite_eq_right hx,zero_comp]

theorem fundamentalSubsetProjection_full (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x) :
    fundamentalSubsetProjection N hε ht (fundamentalSet N) x=projection N hε ht x := by
  simp only [fundamentalSubsetProjection_formula N hε ht (fundamentalSet N) x,
    fundamentalTransfer_supported N hε ht x]
  exact fundamentalTransfer_cogram N hε ht x hx

theorem fundamental_corner_partition (N : ℕ) (H : ℝ) (x : ℍ) :
    corner (G:=OrbitGroup) (fundamentalRetained N H) x+
      corner (fundamentalTail N H) x=corner (fundamentalSet N) x := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp only [_root_.add_apply,lp.coeFn_add,Pi.add_apply,corner_apply]
  by_cases hf : g • x∈fundamentalSet N <;>
    by_cases hh : g • x∈wideTailCover N H <;>
    simp [fundamentalRetained,fundamentalTail,hf,hh]

/-- Retained and exceptional quotient corners partition the actual
quotient projection, with no abstract rank or support premise. -/
theorem fundamental_quotient_partition (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (H : ℝ) (x : ℍ) (hx : fundamentalGood N x) :
    fundamentalSubsetProjection N hε ht (fundamentalRetained N H) x+
      fundamentalSubsetProjection N hε ht (fundamentalTail N H) x=projection N hε ht x := by
  simp only [fundamentalSubsetProjection_formula N hε ht (fundamentalRetained N H) x,
    fundamentalSubsetProjection_formula N hε ht (fundamentalTail N H) x,
    ← add_comp,← comp_add,fundamental_corner_partition N H x]
  calc
    _ = fundamentalSubsetProjection N hε ht (fundamentalSet N) x :=
      (fundamentalSubsetProjection_formula N hε ht (fundamentalSet N) x).symm
    _ = _ := fundamentalSubsetProjection_full N hε ht x hx

theorem fundamental_quotient_decompose (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (H : ℝ) (x : ℍ) (hx : fundamentalGood N x)
    (u : ℓ²(OrbitGroup,ℂ)) (hu : u∈quotientSpace N hε ht x) :
    u=fundamentalSubsetProjection N hε ht (fundamentalRetained N H) x u+
      fundamentalSubsetProjection N hε ht (fundamentalTail N H) x u := by
  have he := congrArg (fun B : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) => B u)
    (fundamental_quotient_partition N hε ht H x hx)
  have hu' : projection N hε ht x u=u :=
    (Submodule.starProjection_eq_self_iff).mpr hu
  simpa only [_root_.add_apply,hu'] using he.symm

#print axioms fundamentalTransfer_supported
#print axioms fundamental_quotient_partition
#print axioms fundamental_quotient_decompose

end QuantitativeSpectralObservability
