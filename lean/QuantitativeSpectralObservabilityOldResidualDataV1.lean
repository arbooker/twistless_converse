module

public import QuantitativeSpectralObservabilityOldResidualV1
public import QuantitativeSpectralObservabilityOldTailRowsV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp

def oldBranches {I : Type*} {J : Subgroup OrbitGroup} (r : I → J) : I → Branch :=
  fun i => projectiveBranch (r i).val⁻¹

def oldCoefficients {I : Type*} (N : ℕ) (J : Subgroup OrbitGroup) : I → ℂ :=
  fun _ => (((gamma N).subgroupOf J).index:ℂ)⁻¹

/-- Fixed witnesses for the already proved actual old-row factorization.
The constructor below supplies every field from finite coset representatives
and geometric reduction; this is not an extra analytic input. -/
structure OldResidualData {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (r : I → J) where
  C : ℝ
  B : ℝ
  L : ℝ
  K : ℝ
  n : ℕ
  w : Fin n → I → List SL(2,ℤ)
  letters : ∀ j i a, a∈w j i → a∈signedGenerators S
  C_pos : 0<C
  B_pos : 0<B
  L_ge_one : 1≤L
  K_ge_one : 1≤K
  factor : ∀ Y : ℝ, B≤Y → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t) (x : ℍ),
    let hs := wideCompactCover_compact N hN (Y/C)
    let D := commonResidualStack (signedGenerators S) (oldBranches r) w
      (oldCoefficients N J) hs hε t x
    ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
      ‖R‖≤L*(1+ε*K*(Y/C+3)^2)^(2*t) ∧ ∀ v : ℓ²(OrbitGroup,ℂ),
        oldSampledRow N hN J hJ Y hε ht x v=R (D v)+
          oldTailRow N hN J hJ Y (Y/C) hε ht x v

/-- A fixed choice of actual geometric old-row witnesses, independent of
cutoffs, exponent, base point and vector. -/
def oldResidualData {I : Type*} [Fintype I] (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (r : I → J)
    (e : I ≃ (J ⧸ (gamma N).subgroupOf J))
    (he : ∀ i, e i=QuotientGroup.mk (r i)) : OldResidualData N hN S J hJ r :=
  Classical.choice (by
    obtain ⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,hall⟩ :=
      exists_oldProjection_residual N hN S hS J hJ r e he
    refine ⟨⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,?_⟩⟩
    intro Y hY ε hε t ht x
    obtain ⟨R,hR,_htrace,hfac⟩ := hall Y hY ε hε t ht x
    exact ⟨R,hR,hfac⟩)

/-- On the actual tail-error kernel the old projection is controlled by
its original row/generator stack with the proved polynomial constant. -/
theorem OldResidualData.old_norm_le {I : Type*} [Fintype I]
    {N : ℕ} {hN : 0<N} {S : Finset SL(2,ℤ)}
    {J : Subgroup OrbitGroup} {hJ : gamma N≤J}
    [Finite (J ⧸ (gamma N).subgroupOf J)] {r : I → J}
    (d : OldResidualData N hN S J hJ r) {Y : ℝ} (hY : d.B≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : oldTailRow N hN J hJ Y (Y/d.C) hε ht x v=0) :
    ‖oldSampledRow N hN J hJ Y hε ht x v‖≤
      (d.L*(1+ε*d.K*(Y/d.C+3)^2)^(2*t))*
        ‖commonResidualStack (signedGenerators S) (oldBranches r) d.w
          (oldCoefficients N J) (wideCompactCover_compact N hN (Y/d.C)) hε t x v‖ := by
  obtain ⟨R,hR,hfac⟩ := d.factor Y hY ε hε t ht x
  rw [hfac v,hv,add_zero]
  exact R.le_of_opNorm_le hR _

#print axioms oldResidualData
#print axioms OldResidualData.old_norm_le

end QuantitativeSpectralObservability
