module

public import QuantitativeEulerEndpointBoundedGramReplacementV1
public import QuantitativeEulerEndpointReconstructionComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra QuantitativeHolomorphic
open AsymptoticRegularCompactBranch AsymptoticFiniteBranch
open scoped Classical MatrixGroups

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The explicit block bounds control the original rows before either
exact or finite reconstruction is composed with them. -/
theorem actualBlock_uncomposed_norm (n j i : ℕ) (x : UpperHalfPlane) :
    let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    ‖uncomposedCombinedRows A P sector b.compact b.primes i x‖≤b.bound i := by
  dsimp only [actualBlock]
  apply uncomposed_combined_rows_wide_norm
  · exact div_pos (div_pos
      (lt_min (AsymptoticReconstructedCount.parameters A P).epsilon_pos (by norm_num : (0:ℝ)<1/4))
      (wideDistortion_pos _ _ _)) (wideDistortion_pos _ _ _)
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

/-- Replacing reconstruction in any actual block keeps the Gram a positive
contraction and changes it by at most twice the reconstruction error. -/
theorem actualBlock_replacement (n j : ℕ) (x : UpperHalfPlane)
    (V : Space →L[ℂ] Space) (hV : ‖V‖≤1) :
    let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    let T := replacementGram A P sector b.compact b.primes b.bound x V
    0≤T ∧ T≤1 ∧
      ‖T-rep A P (QuantitativeEulerEndpointBoundedTerminal.gram A P sector
        b.compact b.primes b.bound b.norm_bound) x‖≤
        2*‖V-normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector x‖ := by
  intro b T
  have hraw := actualBlock_uncomposed_norm A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
  have hord := replacementGram_order A P sector b.compact b.primes b.bound x (fun i => hraw i x) V hV
  refine ⟨hord.1,hord.2,?_⟩
  rw [replacementGram_exact]
  exact replacementGram_difference A P sector b.compact b.primes b.bound x (fun i => hraw i x)
    _ V (normalizedRegularAmbientCountReconstruction_norm_le A (NeZero.pos N) P sector x) hV

/-- The common reconstruction's paid error transfers directly to the exact
actual Gram, retaining its normalization and with no row-count loss. -/
theorem actualBlock_paid_replacement (n j : ℕ) (E : Expression)
    (hE : ∀ x,‖regularSum E x‖≤1) {M : ℝ} (hM : 0≤M)
    (hpaid : ∀ x,M*‖regularSum E x-normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector x‖≤1/(4:ℝ)^n)
    (x : UpperHalfPlane) :
    let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    M*‖replacementGram A P sector b.compact b.primes b.bound x (regularSum E x)-
      rep A P (QuantitativeEulerEndpointBoundedTerminal.gram A P sector
        b.compact b.primes b.bound b.norm_bound) x‖≤2/(4:ℝ)^n := by
  have hh := (actualBlock_replacement A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs
    n j x (regularSum E x) (hE x)).2.2
  have hm := mul_le_mul_of_nonneg_left hh hM
  have hp := hpaid x
  dsimp only
  rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
  nlinarith only [hm,hp]

#print axioms actualBlock_uncomposed_norm
#print axioms actualBlock_replacement
#print axioms actualBlock_paid_replacement
end QuantitativeEulerEndpointBoundedIteration
