module

public import QuantitativeEulerEndpointSubcornerEmbeddingV1
public import QuantitativeSpectralPacketDiagonalV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerIntrinsic

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointSubcornerEmbedding QuantitativeSpectralRegularPacket
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralTriangularAssembly
open MeasureTheory
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c) (hsource : ∀ i x, B i x * QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x = B i x)

local notation "P" => projectionElement hact s hs p hp U hU B hmB hcB C hC c hc
local notation "E" => rowElement hact s hs p hp U hU B hmB hcB C hC c hc hsource
local notation "ρ" => representation hact s hs p hp
local notation "A" => Subcorner hact s hs p hp

/-- The actual deflation partition, now inside the finite-corner algebra. -/
def blockElements (n : ℕ) : Fin (n+1) → A :=
  Fin.lastCases (P n) (fun i : Fin n => P i - P (i+1))

/-- The actual inverse-normalized residual rows with the final retained row. -/
def rowElements (n : ℕ) (d : ℝ) : Fin (n+1) → A :=
  Fin.lastCases (d • P n) (fun i : Fin n => E i)

local notation "Q" => blockElements hact s hs p hp U hU B hmB hcB C hC c hc
local notation "L" => rowElements hact s hs p hp U hU B hmB hcB C hC c hc hsource

theorem eval_blockElements (n : ℕ) (i : Fin (n+1)) (x : α) :
    ρ (Q n i) x = blocks (U x) (fun j => B j x) c n i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [blockElements, blocks, Fin.lastCases_last, representation_projectionElement]
    rfl
  · simp only [blockElements, blocks, Fin.lastCases_castSucc, map_sub,
      representation_projectionElement, Pi.sub_apply]
    exact (removed_eq_sub (U x) (fun j => B j x) c j).symm

theorem eval_rowElements (n : ℕ) (d : ℝ) (i : Fin (n+1)) (x : α) :
    ρ (L n d i) x = rows (U x) (fun j => B j x) c n d i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [rowElements, rows, Fin.lastCases_last, map_smul,
      representation_projectionElement, Pi.smul_apply]
    rfl
  · simp only [rowElements, rows, Fin.lastCases_castSucc, representation_rowElement]
    rfl

private theorem eval_mul (a b : A) (x : α) : ρ (a*b) x = ρ a x * ρ b x := rfl
private theorem eval_star (a : A) (x : α) : ρ (star a) x = star (ρ a x) := rfl
private theorem eval_smul (r : ℝ) (a : A) (x : α) : ρ (r • a) x = r • ρ a x := rfl

theorem blockElements_projection (n : ℕ) (i : Fin (n+1)) : IsStarProjection (Q n i) := by
  constructor
  · apply representation_injective hact s hs p hp
    funext x
    rw [eval_mul, eval_blockElements]
    exact (blocks_projection (U x) (fun j => B j x) c n i).isIdempotentElem.eq
  · apply representation_injective hact s hs p hp
    funext x
    rw [eval_star, eval_blockElements]
    exact (blocks_projection (U x) (fun j => B j x) c n i).isSelfAdjoint.star_eq

theorem blockElements_orthogonal (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) :
    Q n i * Q n j = 0 := by
  apply representation_injective hact s hs p hp
  funext x
  rw [eval_mul, eval_blockElements, eval_blockElements, map_zero]
  exact blocks_orthogonal (U x) (fun j => B j x) c n i j hij

theorem blockElements_sum (n : ℕ) : ∑ i, Q n i = 1 := by
  apply representation_injective hact s hs p hp
  funext x
  rw [map_sum, Finset.sum_apply]
  simp only [eval_blockElements]
  rw [sum_blocks, representation_one]
  exact hU x

theorem rowElements_left (n : ℕ) (d : ℝ) (i : Fin (n+1)) :
    Q n i * L n d i = L n d i := by
  apply representation_injective hact s hs p hp
  funext x
  rw [eval_mul, eval_blockElements, eval_rowElements]
  exact rows_left_supported (U x) (fun j => B j x) n hc d i

theorem rowElements_diagonal (n : ℕ) (d : ℝ) (i : Fin (n+1)) :
    L n d i * Q n i = weights c n d i • Q n i := by
  apply representation_injective hact s hs p hp
  funext x
  rw [eval_mul, eval_smul, eval_blockElements, eval_rowElements]
  exact rows_diagonal (U x) (fun j => B j x) n hc d i

theorem rowElements_upper (n : ℕ) (d : ℝ) (i j : Fin (n+1)) (hij : i < j) :
    L n d i * Q n j = 0 := by
  apply representation_injective hact s hs p hp
  funext x
  rw [eval_mul, eval_blockElements, eval_rowElements, map_zero]
  exact rows_upper (U x) (fun j => B j x) c n d i j hij

/-- Intrinsic diagonal and triangular factors of the actual regular packet. -/
def diagonalElement (n : ℕ) (d : ℝ) : A := diagonal (Q n) (weights c n d)
def strictElement (n : ℕ) (d : ℝ) : A := normalizedStrict (Q n) (L n d) (weights c n d)

local notation "D" => diagonalElement hact s hs p hp U hU B hmB hcB C hC c hc
local notation "V" => strictElement hact s hs p hp U hU B hmB hcB C hC c hc hsource

include hc in
private theorem weights_nonzero (n : ℕ) {d : ℝ} (hd : 0 < d) (i : Fin (n+1)) :
    weights c n d i ≠ 0 := by
  refine Fin.lastCases ?_ (fun _ => ?_) i
  · simpa only [weights, Fin.lastCases_last] using hd.ne'
  · simpa only [weights, Fin.lastCases_castSucc] using hc.ne'

theorem strictElement_below (n : ℕ) {d : ℝ} (hd : 0 < d) :
    QuantitativeSpectralBlockTriangular.Below (Q n) (V n d) 1 :=
  normalizedStrict_below (Q n)
    (fun i => (blockElements_projection hact s hs p hp U hU B hmB hcB C hC c hc n i).isIdempotentElem.eq)
    (blockElements_orthogonal hact s hs p hp U hU B hmB hcB C hC c hc n) (L n d)
    (rowElements_left hact s hs p hp U hU B hmB hcB C hC c hc hsource n d)
    (weights c n d) (weights_nonzero c hc n hd)
    (rowElements_diagonal hact s hs p hp U hU B hmB hcB C hC c hc hsource n d)
    (rowElements_upper hact s hs p hp U hU B hmB hcB C hC c hc hsource n d)

theorem diagonalElement_isUnit (n : ℕ) {d : ℝ} (hd : 0 < d) : IsUnit (D n d) :=
  diagonal_isUnit (Q n)
    (fun i => (blockElements_projection hact s hs p hp U hU B hmB hcB C hC c hc n i).isIdempotentElem.eq)
    (blockElements_orthogonal hact s hs p hp U hU B hmB hcB C hC c hc n)
    (blockElements_sum hact s hs p hp U hU B hmB hcB C hC c hc n)
    (weights c n d) (weights_nonzero c hc n hd)

theorem factorization (n : ℕ) {d : ℝ} (hd : 0 < d) : D n d * (1 + V n d) = ∑ i, L n d i :=
  diagonal_factor (Q n)
    (fun i => (blockElements_projection hact s hs p hp U hU B hmB hcB C hC c hc n i).isIdempotentElem.eq)
    (blockElements_orthogonal hact s hs p hp U hU B hmB hcB C hC c hc n) (L n d)
    (blockElements_sum hact s hs p hp U hU B hmB hcB C hC c hc n)
    (weights c n d) (weights_nonzero c hc n hd)

#print axioms blockElements_projection
#print axioms blockElements_orthogonal
#print axioms blockElements_sum
#print axioms rowElements_left
#print axioms rowElements_diagonal
#print axioms rowElements_upper
#print axioms strictElement_below
#print axioms diagonalElement_isUnit
#print axioms factorization

end QuantitativeEulerEndpointSubcornerIntrinsic
