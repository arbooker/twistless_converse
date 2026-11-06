module

public import QuantitativeSpectralPacketIntrinsicV1
public import QuantitativeSpectralSourceGramV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketDeterminantData

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularOrder
open QuantitativeSpectralPacketEmbedding QuantitativeSpectralRegularPacket
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralTriangularAssembly
open QuantitativeSpectralPacketIntrinsic QuantitativeSpectralSourceGram
open QuantitativeSpectralFiniteCornerDistribution
open MeasureTheory
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = corner s x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c) (hsource : ∀ i x, B i x * corner s x = B i x)

local notation "P" => projectionElement hact s hs U hU B hmB hcB C hC c hc
local notation "E" => rowElement hact s hs U hU B hmB hcB C hC c hc hsource
local notation "ρ" => representation G α hact s hs
local notation "A" => FiniteCorner G α hact s hs

local notation "Q" => blockElements hact s hs U hU B hmB hcB C hC c hc
local notation "L" => rowElements hact s hs U hU B hmB hcB C hC c hc hsource
local notation "D" => diagonalElement hact s hs U hU B hmB hcB C hC c hc
local notation "V" => strictElement hact s hs U hU B hmB hcB C hC c hc hsource
local notation "F" => fun i => gramElement hact s hs (B i) (hmB i) (hcB i) (C i) (hC i) (hsource i)

/-- The genuine source Gram sum with a scalar positive regularization.
Its spectral cutoff can subsequently be translated back to the unshifted sum. -/
def regularizedGram (n : ℕ) (d : ℝ) : A := (∑ i : Fin n, F i) + d^2 • 1
local notation "S" => regularizedGram hact s hs B hmB hcB C hC hsource

private theorem eval_mul (a b : A) (x : α) : ρ (a*b) x = ρ a x * ρ b x := rfl
private theorem eval_star (a : A) (x : α) : ρ (star a) x = star (ρ a x) := rfl

theorem eval_diagonalElement (n : ℕ) (d : ℝ) (x : α) :
    ρ (D n d) x = QuantitativeSpectralPacketFactorization.diagonalFactor (U x) (fun i => B i x) n c d := by
  simp only [diagonalElement, diagonal, map_sum, Finset.sum_apply, map_smul,
    Pi.smul_apply, eval_blockElements]
  rfl

theorem eval_rowSum (n : ℕ) (d : ℝ) (x : α) :
    ρ (∑ i, L n d i) x = ∑ i, rows (U x) (fun j => B j x) c n d i := by
  rw [map_sum, Finset.sum_apply]
  simp only [eval_rowElements]

theorem projectionElement_projection (n : ℕ) : IsStarProjection (P n) := by
  have hh := blockElements_projection hact s hs U hU B hmB hcB C hC c hc n (Fin.last n)
  simpa only [blockElements, Fin.lastCases_last] using hh

/-- Exact two-block diagonal Gram identity inside the actual finite corner. -/
theorem diagonalElement_gram (n : ℕ) (d : ℝ) :
    star (D n d) * D n d = c^2 • (1 : A) + (d^2-c^2) • P n := by
  apply representation_injective hact s hs
  funext x
  rw [eval_mul, eval_star, eval_diagonalElement,
    QuantitativeSpectralPacketDiagonal.diagonalFactor_gram]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, representation_one,
    representation_projectionElement]
  have he : projection (U x) (fun i => B i x) c 0 = corner s x := hU x
  rw [he]
  rfl

theorem rows_gram_le_partial (n : ℕ) (d : ℝ) :
    star (∑ i, L n d i) * (∑ i, L n d i) ≤ (∑ i : Fin n, F i) + d^2 • P n := by
  apply (pointwise_le_iff hact s hs _ _).mp
  intro x
  rw [eval_mul, eval_star, eval_rowSum]
  simp only [map_add, map_sum, map_smul, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    representation_gramElement, representation_projectionElement]
  exact QuantitativeSpectralPacketFactorization.rows_gram_le (U x) (fun i => B i x) hc n

theorem factor_gram_le (n : ℕ) {d : ℝ} (hd : 0 < d) :
    star (D n d * (1+V n d)) * (D n d * (1+V n d)) ≤ S n d := by
  rw [QuantitativeSpectralPacketIntrinsic.factorization hact s hs U hU B hmB hcB C hC c hc hsource n hd]
  apply (rows_gram_le_partial hact s hs U hU B hmB hcB C hC c hc hsource n d).trans
  exact add_le_add le_rfl (smul_le_smul_of_nonneg_left
    (projectionElement_projection hact s hs U hU B hmB hcB C hC c hc n).le_one (sq_nonneg d))

theorem sourceSum_nonneg (n : ℕ) : 0 ≤ ∑ i : Fin n, F i :=
  Finset.sum_nonneg (fun i _ => gramElement_nonneg hact s hs (B i) (hmB i) (hcB i)
    (C i) (hC i) (hsource i))

theorem regularizedGram_strictlyPositive (n : ℕ) {d : ℝ} (hd : 0 < d) :
    IsStrictlyPositive (S n d) := by
  apply IsStrictlyPositive.of_le (IsStrictlyPositive.smul (sq_pos_of_pos hd) isStrictlyPositive_one)
  exact le_add_of_nonneg_left (sourceSum_nonneg hact s hs B hmB hcB C hC hsource n)

theorem regularizedGram_norm_le (n : ℕ) (d : ℝ) : ‖S n d‖ ≤ (∑ i : Fin n, (C i)^2) + d^2 := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun i _ => gramElement_norm_le hact s hs (B i)
      (hmB i) (hcB i) (C i) (hC i) (hsource i))
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg d)]
    have hn1 : ‖(1 : A)‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
    exact (mul_le_mul_of_nonneg_left hn1 (sq_nonneg d)).trans_eq (mul_one _)

#print axioms projectionElement_projection
#print axioms diagonalElement_gram
#print axioms rows_gram_le_partial
#print axioms factor_gram_le
#print axioms regularizedGram_strictlyPositive
#print axioms regularizedGram_norm_le

end QuantitativeSpectralPacketDeterminantData
