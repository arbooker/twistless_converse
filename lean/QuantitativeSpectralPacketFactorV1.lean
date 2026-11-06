module

public import QuantitativeSpectralPacketAssemblyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketFactor

open ContinuousLinearMap InnerProductSpace
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralTriangularAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (c : ℝ) (n : ℕ)

theorem blocks_projection (i : Fin (n+1)) : IsStarProjection (blocks U B c n i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [blocks, Fin.lastCases_last]
    exact ⟨Submodule.isIdempotentElem_starProjection _,
      ContinuousLinearMap.isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)⟩
  · simpa only [blocks, Fin.lastCases_castSucc] using removed_isStarProjection U B c j

theorem blocks_orthogonal (i j : Fin (n+1)) (hij : i ≠ j) :
    blocks U B c n i * blocks U B c n j = 0 := by
  revert hij
  refine Fin.lastCases ?_ (fun ii => ?_) i
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · intro h; exact (h rfl).elim
    · intro _
      have hh := congrArg star (removed_later U B c jj n jj.isLt)
      have hs : IsSelfAdjoint (projection U B c n) :=
        ContinuousLinearMap.isSelfAdjoint_iff'.mpr (isSelfAdjoint_starProjection _)
      simpa only [blocks, Fin.lastCases_last, Fin.lastCases_castSucc, star_mul,
        hs.star_eq, (removed_isStarProjection U B c jj).isSelfAdjoint.star_eq, star_zero] using hh
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · intro _; simpa only [blocks, Fin.lastCases_castSucc, Fin.lastCases_last] using removed_later U B c ii n ii.isLt
    · intro h
      simpa only [blocks, Fin.lastCases_castSucc] using removed_orthogonal U B c ii jj (fun he => h (congrArg Fin.castSucc (Fin.ext he)))

/-- Append a final retained row of size `d`; all removed rows retain their
exact normalization `c`. -/
def rows (d : ℝ) : Fin (n+1) → H →L[ℂ] H :=
  Fin.lastCases (d • projection U B c n) (fun i : Fin n => packetRow U B c i)

def weights (d : ℝ) : Fin (n+1) → ℝ := Fin.lastCases d (fun _ : Fin n => c)

theorem rows_left_supported {c : ℝ} (hc : 0 < c) (d : ℝ) (i : Fin (n+1)) :
    blocks U B c n i * rows U B c n d i = rows U B c n d i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [blocks, rows, Fin.lastCases_last]
    change projection U B c n * (d • projection U B c n) = _
    rw [mul_smul_comm]
    exact congrArg (fun X => d • X) (Submodule.isIdempotentElem_starProjection (chain U B c n).toSubmodule).eq
  · simpa only [blocks, rows, Fin.lastCases_castSucc] using packetRow_left_supported U B hc j

theorem rows_diagonal {c : ℝ} (hc : 0 < c) (d : ℝ) (i : Fin (n+1)) :
    rows U B c n d i * blocks U B c n i = weights c n d i • blocks U B c n i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [blocks, rows, weights, Fin.lastCases_last]
    change (d • projection U B c n) * projection U B c n = _
    rw [smul_mul_assoc]
    exact congrArg (fun X => d • X) (Submodule.isIdempotentElem_starProjection (chain U B c n).toSubmodule).eq
  · simpa only [blocks, rows, weights, Fin.lastCases_castSucc] using packetRow_diagonal U B hc j

theorem rows_upper (d : ℝ) (i j : Fin (n+1)) (hij : i < j) :
    rows U B c n d i * blocks U B c n j = 0 := by
  revert hij
  refine Fin.lastCases ?_ (fun ii => ?_) i
  · intro h; exact (not_lt_of_ge (Fin.le_last j) h).elim
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · intro _; simpa only [rows, blocks, Fin.lastCases_castSucc, Fin.lastCases_last] using packetRow_later U B c ii n ii.isLt
    · intro h
      simpa only [rows, blocks, Fin.lastCases_castSucc] using packetRow_upper U B c ii jj h

#print axioms blocks_projection
#print axioms blocks_orthogonal
#print axioms rows_left_supported
#print axioms rows_diagonal
#print axioms rows_upper

end QuantitativeSpectralPacketFactor
