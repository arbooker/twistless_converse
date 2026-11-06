module

public import QuantitativeSpectralCornerCutRowV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralDeflationChain

open QuantitativeSpectralCornerCutRow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

/-- One actual threshold deflation step, bundled with closedness. -/
def step (U : ClosedSubmodule ℂ H) (B : H →L[ℂ] H) (c : ℝ) : ClosedSubmodule ℂ H where
  toSubmodule := nextSpace U.toSubmodule B c
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (nextSpace U.toSubmodule B c))).isClosed

/-- A packet of residual operators determines its cuts recursively. No
sequence of subspaces, ranks, or triangular factors is assumed. -/
def chain (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (c : ℝ) : ℕ → ClosedSubmodule ℂ H
  | 0 => U
  | n+1 => step (chain U B c n) (B n) c

variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (c : ℝ)

def projection (n : ℕ) : H →L[ℂ] H := (chain U B c n).toSubmodule.starProjection

def removedProjection (n : ℕ) : H →L[ℂ] H :=
  QuantitativeSpectralCutRow.removed (restricted (chain U B c n).toSubmodule (B n)) c

def packetRow (n : ℕ) : H →L[ℂ] H := row (chain U B c n).toSubmodule (B n) c

theorem chain_succ_le (n : ℕ) : chain U B c (n+1) ≤ chain U B c n :=
  nextSpace_le _ _ _

theorem chain_antitone : Antitone (chain U B c) :=
  antitone_nat_of_succ_le (chain_succ_le U B c)

theorem projection_sub_removed (n : ℕ) :
    projection U B c (n+1) = projection U B c n - removedProjection U B c n :=
  nextSpace_projection _ _ _

theorem removed_eq_sub (n : ℕ) :
    removedProjection U B c n = projection U B c n - projection U B c (n+1) := by
  rw [projection_sub_removed]
  abel

/-- The removed projections telescope exactly, without accumulated errors. -/
theorem sum_removed (n : ℕ) :
    ∑ i ∈ Finset.range n, removedProjection U B c i =
      projection U B c 0 - projection U B c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, removed_eq_sub]
    abel

theorem packetRow_gram_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    star (packetRow U B c n) * packetRow U B c n ≤ star (B n) * B n :=
  row_gram_le _ _ _ hc

theorem packetRow_diagonal {c : ℝ} (hc : 0 < c) (n : ℕ) :
    packetRow U B c n * removedProjection U B c n = c • removedProjection U B c n :=
  row_diagonal _ _ _ hc

theorem packetRow_left_supported {c : ℝ} (hc : 0 < c) (n : ℕ) :
    removedProjection U B c n * packetRow U B c n = packetRow U B c n :=
  row_left_supported _ _ _ hc

/-- Each row annihilates every later surviving corner, the source of
strict triangularity for the whole packet. -/
theorem packetRow_later (i j : ℕ) (hij : i < j) :
    packetRow U B c i * projection U B c j = 0 := by
  have hle := chain_antitone U B c (Nat.succ_le_of_lt hij)
  have hp : projection U B c (i+1) * projection U B c j = projection U B c j := by
    apply ContinuousLinearMap.ext
    intro x
    exact (chain U B c (i+1)).toSubmodule.starProjection_eq_self_iff.mpr
      (hle ((chain U B c j).toSubmodule.starProjection_apply_mem x))
  have hz : packetRow U B c i * projection U B c (i+1) = 0 := row_retained _ _ _
  calc
    packetRow U B c i * projection U B c j =
        packetRow U B c i * (projection U B c (i+1) * projection U B c j) := by rw [hp]
    _ = 0 := by rw [← mul_assoc, hz, zero_mul]

theorem packetRow_upper (i j : ℕ) (hij : i < j) :
    packetRow U B c i * removedProjection U B c j = 0 := by
  rw [removed_eq_sub, mul_sub, packetRow_later U B c i j hij,
    packetRow_later U B c i (j+1) (lt_trans hij (Nat.lt_succ_self j)), sub_self]

/-- Every common exact solution survives every stage of the constructed packet. -/
theorem kernel_survives {v : H} (hv : v ∈ U) (hB : ∀ n, B n v = 0) (n : ℕ) :
    v ∈ chain U B c n := by
  induction n with
  | zero => exact hv
  | succ n ih => exact QuantitativeSpectralCornerCutRow.kernel_survives _ _ _ ih (hB n)

#print axioms chain_antitone
#print axioms sum_removed
#print axioms packetRow_gram_le
#print axioms packetRow_diagonal
#print axioms packetRow_left_supported
#print axioms packetRow_later
#print axioms packetRow_upper
#print axioms kernel_survives

end QuantitativeSpectralDeflationChain
