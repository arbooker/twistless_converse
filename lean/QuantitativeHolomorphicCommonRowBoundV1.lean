module

public import AsymptoticFiniteBranchRowsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch

/-- The physical and regular row bounds are literally the same matrix-fold
bounds, so the single filter uses the same scalar normalization in both models. -/
theorem regular_rowBound_eq {N : ℕ} (hN : 0 < N)
    (r : AsymptoticCompactObservationCount.Row N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    AsymptoticRegularObservationRows.rowBound hN r hs hε t =
      AsymptoticCompactObservationCount.rowBound hN r hs hε t := by
  have ht (a : ℚ) : AsymptoticRegularBranchFamily.bound
      (AsymptoticRegularObservationRows.translation a) hs hε t =
      AsymptoticTwistObservation.branchBound (AsymptoticMobiusFold.translation (a : ℝ)) hs hε t :=
    congrArg (fun M => AsymptoticTwistObservation.branchBound M hs hε t)
      (observation_translation_matrix a)
  have hf (q : ℕ) (hq : 0 < q) (a : ℕ) : AsymptoticRegularBranchFamily.bound
      (AsymptoticRegularObservationRows.reflected N q hN hq a) hs hε t =
      AsymptoticTwistObservation.branchBound (AsymptoticTwistObservation.reflected N q hN hq a) hs hε t :=
    congrArg (fun M => AsymptoticTwistObservation.branchBound M hs hε t)
      (observation_reflected_matrix N q hN hq a)
  have hr (p : ℕ) (hp : 0 < p) (a : ℕ) : AsymptoticRegularBranchFamily.bound
      (AsymptoticRegularObservationRows.ramified p hp a) hs hε t =
      AsymptoticTwistObservation.branchBound
        (AsymptoticRamifiedBranch.branch (p : ℝ) (a : ℝ) (by exact_mod_cast hp.ne')) hs hε t :=
    congrArg (fun M => AsymptoticTwistObservation.branchBound M hs hε t)
      (observation_ramified_matrix p hp a)
  have hzero : AsymptoticRegularBranchFamily.bound
      (AsymptoticRegularObservationRows.translation 0) hs hε t =
      AsymptoticTwistObservation.branchBound 1 hs hε t :=
    congrArg (fun M => AsymptoticTwistObservation.branchBound M hs hε t)
      observation_identity_matrix
  cases r with
  | twist q hq =>
    simp only [AsymptoticRegularObservationRows.rowBound,
      AsymptoticCompactObservationCount.rowBound, Fintype.sum_sum_type,
      AsymptoticRegularObservationRows.twistBranches, Sum.elim_inl, Sum.elim_inr,
      AsymptoticTwistObservation.translationBound, AsymptoticTwistObservation.reflectionBound,
      ht, hf, Rat.cast_div, Rat.cast_natCast]
  | ramified p hp hpN =>
    simp only [AsymptoticRegularObservationRows.rowBound,
      AsymptoticCompactObservationCount.rowBound, Fintype.sum_sum_type,
      AsymptoticRegularObservationRows.ramifiedBranches, Sum.elim_inl, Sum.elim_inr,
      AsymptoticRamifiedObservation.bound, hr, hzero, Fintype.sum_unique]
    exact congrArg (fun x : ℝ => x + AsymptoticTwistObservation.branchBound 1 hs hε t)
      (Fin.sum_univ_eq_sum_range (fun a => AsymptoticTwistObservation.branchBound
        (AsymptoticRamifiedBranch.branch (p : ℝ) (a : ℝ) (by exact_mod_cast hp.pos.ne')) hs hε t) p)

theorem regular_row_norm_le_physical_bound {N : ℕ} (hN : 0 < N)
    (r : AsymptoticCompactObservationCount.Row N) (e : AsymptoticSectorSigns.Sector N)
    {s : Set UpperHalfPlane} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (z : UpperHalfPlane) :
    ‖AsymptoticRegularObservationRows.row hN r e hs hε t z‖ ≤
      AsymptoticCompactObservationCount.rowBound hN r hs hε t := by
  rw [← regular_rowBound_eq]
  exact AsymptoticRegularObservationRows.row_norm_le hN r e hs hε t z

#print axioms regular_rowBound_eq

end QuantitativeHolomorphic
