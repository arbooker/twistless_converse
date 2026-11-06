module

public import QuantitativeSpectralExceptionalFrickeResidualV1
public import QuantitativeSpectralObservabilityOldResidualDataV1

set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp

def tailRow (N : ℕ) (hN : 0<N) (sign Y H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
    (sampledRow N hN sign Y hε ht x)

/-- Fixed geometric witnesses supplied by the actual signed Fricke
factorization, independent of every sampling and cap parameter. -/
structure ResidualData (N : ℕ) (hN : 0<N) (sign : ℝ) (S : Finset SL(2,ℤ)) where
  C : ℝ
  B : ℝ
  L : ℝ
  K : ℝ
  n : ℕ
  w : Fin n → Bool → List SL(2,ℤ)
  letters : ∀ j i a, a∈w j i → a∈signedGenerators S
  C_pos : 0<C
  B_pos : 0<B
  L_ge_one : 1≤L
  K_ge_one : 1≤K
  factor : ∀ Y : ℝ, B≤Y → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t) (x : ℍ),
    let D := commonResidualStack (signedGenerators S) (branches N hN) w (coefficients sign)
      (wideCompactCover_compact N hN (Y/C)) hε t x
    ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
      ‖R‖≤L*(1+ε*K*(Y/C+3)^2)^(2*t) ∧ ∀ v : ℓ²(OrbitGroup,ℂ),
        sampledRow N hN sign Y hε ht x v=R (D v)+tailRow N hN sign Y (Y/C) hε ht x v

def residualData (N : ℕ) (hN : 0<N) (sign : ℝ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    ResidualData N hN sign S := Classical.choice (by
  obtain ⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,hall⟩ := exists_weightedRow_residual N hN sign S hS
  exact ⟨⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,hall⟩⟩)

def ResidualData.cost {N : ℕ} {hN : 0<N} {sign : ℝ} {S : Finset SL(2,ℤ)}
    (d : ResidualData N hN sign S) (Y ε : ℝ) (t : ℕ) : ℝ :=
  d.L*(1+ε*d.K*(Y/d.C+3)^2)^(2*t)

theorem ResidualData.cost_nonneg {N : ℕ} {hN : 0<N} {sign : ℝ} {S : Finset SL(2,ℤ)}
    (d : ResidualData N hN sign S) (Y ε : ℝ) (t : ℕ) : 0≤d.cost Y ε t := by
  have hL := zero_le_one.trans d.L_ge_one
  unfold cost
  rw [Nat.mul_comm 2 t,pow_mul]
  exact mul_nonneg hL (sq_nonneg _)

theorem ResidualData.norm_le {N : ℕ} {hN : 0<N} {sign : ℝ} {S : Finset SL(2,ℤ)}
    (d : ResidualData N hN sign S) {Y : ℝ} (hY : d.B≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : tailRow N hN sign Y (Y/d.C) hε ht x v=0) :
    ‖sampledRow N hN sign Y hε ht x v‖≤d.cost Y ε t*
      ‖commonResidualStack (signedGenerators S) (branches N hN) d.w (coefficients sign)
        (wideCompactCover_compact N hN (Y/d.C)) hε t x v‖ := by
  obtain ⟨R,hR,hfac⟩ := d.factor Y hY ε hε t ht x
  rw [hfac v,hv,add_zero]
  exact R.le_of_opNorm_le hR _

#print axioms residualData
#print axioms ResidualData.norm_le

end QuantitativeSpectralExceptionalFricke
