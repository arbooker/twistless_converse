module

public import AsymptoticFiniteBranchFamilyV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticRationalFreeness AsymptoticCylinderLift

theorem observation_translation_matrix (r : ℚ) :
    realMatrix (AsymptoticRegularObservationRows.translation r).matrix=
      AsymptoticMobiusFold.translation (r:ℝ) :=
  AsymptoticRationalBranches.realMatrix_translation r

theorem observation_reflected_matrix (N q : ℕ) (hN : 0<N) (hq : 0<q) (a : ℕ) :
    realMatrix (AsymptoticRegularObservationRows.reflected N q hN hq a).matrix=
      AsymptoticTwistObservation.reflected N q hN hq a := by
  unfold AsymptoticRegularObservationRows.reflected AsymptoticTwistObservation.reflected
  rw [AsymptoticRationalBranches.realMatrix_branch]
  simp only [Rat.cast_natCast,Rat.cast_zero,Rat.cast_div,AsymptoticTwistObservation.level]

theorem observation_ramified_matrix (p : ℕ) (hp : 0<p) (a : ℕ) :
    realMatrix (AsymptoticRegularObservationRows.ramified p hp a).matrix=
      AsymptoticRamifiedBranch.branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne') := by
  unfold AsymptoticRegularObservationRows.ramified
  rw [AsymptoticRegularObservationRows.realMatrix_ramified]
  simp only [Rat.cast_natCast]

theorem observation_identity_matrix :
    realMatrix (AsymptoticRegularObservationRows.translation 0).matrix=1 := by
  rw [observation_translation_matrix,Rat.cast_zero]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem compactFamilyHolomorphic_twist (N q : ℕ) (hN : 0<N) (hq : 0<q) (χ : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    compactFamilyHolomorphic (AsymptoticRegularObservationRows.twistBranches N q hN hq)
      (Sum.elim (fun _ => 1) (fun _ => -χ)) hs hε t m=
        AsymptoticTwistObservation.residual N q hN hq hs hε t m χ := by
  simp only [compactFamilyHolomorphic,Fintype.sum_sum_type,AsymptoticRegularObservationRows.twistBranches,
    Sum.elim_inl,Sum.elim_inr,one_smul,observation_translation_matrix,observation_reflected_matrix,
    Rat.cast_div,Rat.cast_natCast,← Finset.smul_sum,
    AsymptoticTwistObservation.residual,AsymptoticTwistObservation.translations,
    AsymptoticTwistObservation.reflections,sub_eq_add_neg]
  exact congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space =>
    AsymptoticTwistObservation.translations q hs hε t m+T)
      (neg_smul χ (AsymptoticTwistObservation.reflections N q hN hq hs hε t m))

theorem compactFamilyHolomorphic_ramified (p : ℕ) (hp : 0<p) (δ : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    compactFamilyHolomorphic (AsymptoticRegularObservationRows.ramifiedBranches p hp)
      (Sum.elim (fun _ => 1) (fun _ => -δ)) hs hε t m=
        AsymptoticRamifiedObservation.residual p hp hs hε t m δ := by
  simp only [compactFamilyHolomorphic,Fintype.sum_sum_type,AsymptoticRegularObservationRows.ramifiedBranches,
    Sum.elim_inl,Sum.elim_inr,one_smul,observation_ramified_matrix,observation_identity_matrix,
    Fintype.sum_unique,AsymptoticRamifiedObservation.residual,
    AsymptoticRamifiedObservation.average,sub_eq_add_neg]
  exact congrArg₂ (·+·)
    (Fin.sum_univ_eq_sum_range (fun a => AsymptoticCompactBranch.compactOperator
      (AsymptoticRamifiedBranch.branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne')) hs hε t m) p)
    (neg_smul δ (AsymptoticCompactBranch.compactOperator 1 hs hε t m))

/-- The common row expression evaluates to the actual cylinder twist or
ramified observation, with its prescribed complex sector coefficient. -/
theorem cylinder_rowExpression {N : ℕ} (hN : 0<N) (r : AsymptoticCompactObservationCount.Row N)
    (e : AsymptoticSectorSigns.Sector N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    (holomorphicSum (rowExpression hN r e hs hε t) m).comp lift.toContinuousLinearMap=
      AsymptoticCompactObservationCount.rowOperator hN r e hs hε t m := by
  cases r with
  | twist q hq =>
    rw [rowExpression,cylinder_compactFamilyExpression,compactFamilyHolomorphic_twist]
    rfl
  | ramified p hp hpN =>
    rw [rowExpression,cylinder_compactFamilyExpression,compactFamilyHolomorphic_ramified]
    rfl

#print axioms observation_translation_matrix
#print axioms observation_reflected_matrix
#print axioms observation_ramified_matrix
#print axioms observation_identity_matrix
#print axioms compactFamilyHolomorphic_twist
#print axioms compactFamilyHolomorphic_ramified
#print axioms cylinder_rowExpression

end AsymptoticFiniteBranch
