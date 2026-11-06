module

public import AsymptoticRegularBranchFamilyV1
public import AsymptoticCompactObservationCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservationRows

open UpperHalfPlane MeasureTheory Set AsymptoticRegularTrace
open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCertificateBranches (residues)
open AsymptoticSectorSigns AsymptoticCompactObservationCount

noncomputable def translation (r : ℚ) : Branch :=
  ⟨AsymptoticMobiusFold.translation r,by rw [realMatrix_translation,AsymptoticMobiusFold.translation_det]; norm_num⟩

noncomputable def reflected (N q : ℕ) (hN : 0<N) (hq : 0<q) (a : ℕ) : Branch :=
  ⟨AsymptoticReconstructionBranch.branch (Nat.lcm N (q^2):ℚ) 0 ((a:ℚ)/q)
    (by exact_mod_cast (Nat.lcm_pos hN (pow_pos hq 2)).ne'),by
      rw [realMatrix_branch,AsymptoticReconstructionBranch.branch_det]
      exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)⟩

theorem realMatrix_ramified (p a : ℚ) (hp : p≠0) :
    realMatrix (AsymptoticRamifiedBranch.branch p a hp)=
      AsymptoticRamifiedBranch.branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrix,AsymptoticRamifiedBranch.branch,
      Matrix.GeneralLinearGroup.map,Matrix.GeneralLinearGroup.mkOfDetNeZero]

noncomputable def ramified (p : ℕ) (hp : 0<p) (a : ℕ) : Branch :=
  ⟨AsymptoticRamifiedBranch.branch (p:ℚ) (a:ℚ) (by exact_mod_cast hp.ne'),by
    rw [realMatrix_ramified,AsymptoticRamifiedBranch.branch_det]
    exact_mod_cast hp⟩

noncomputable def twistBranches (N q : ℕ) (hN : 0<N) (hq : 0<q) :
    (residues q ⊕ residues q) → Branch :=
  Sum.elim (fun a => translation ((a.val:ℚ)/q)) (fun a => reflected N q hN hq a.val)

noncomputable def twist (N q : ℕ) (hN : 0<N) (hq : 0<q) (χ : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  family (twistBranches N q hN hq) (Sum.elim (fun _ => 1) (fun _ => -χ)) hs hε t z

noncomputable def ramifiedBranches (p : ℕ) (hp : 0<p) : (Fin p ⊕ Unit) → Branch :=
  Sum.elim (fun a => ramified p hp a.val) (fun _ => translation 0)

noncomputable def bad (p : ℕ) (hp : 0<p) (δ : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  family (ramifiedBranches p hp) (Sum.elim (fun _ => 1) (fun _ => -δ)) hs hε t z

/-- Literal twist and ramified residuals on counting coordinates. Branches
are rational and phases have been removed by the checked orbit gauge. -/
noncomputable def row {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  match r with
  | .twist q hq => twist N q hN hq (multiplier e q) hs hε t z
  | .ramified p hp _ => bad p hp.pos (AsymptoticCylinderRamified.eigenvalue e p) hs hε t z

noncomputable def rowBound {N : ℕ} (hN : 0<N) (r : Row N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  match r with
  | .twist q hq => ∑ i,bound (twistBranches N q hN hq i) hs hε t
  | .ramified p hp _ => ∑ i,bound (ramifiedBranches p hp.pos i) hs hε t

theorem rowBound_nonneg {N : ℕ} (hN : 0<N) (r : Row N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : 0≤rowBound hN r hs hε t := by
  cases r <;> exact Finset.sum_nonneg (fun _ _ => bound_nonneg _ hs hε t)

theorem row_norm_le {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    ‖row hN r e hs hε t z‖≤rowBound hN r hs hε t := by
  cases r with
  | twist q hq =>
    apply family_norm_le_unit
    intro i
    cases i <;> simp [multiplier_norm]
  | ramified p hp hpN =>
    apply family_norm_le_unit
    intro i
    cases i
    · simp
    · simpa only [Sum.elim_inr,norm_neg] using AsymptoticCylinderRamified.eigenvalue_norm_le e p

theorem row_covariant {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    Covariant (row hN r e hs hε t) := by
  cases r <;> exact family_covariant _ _ hs hε t

theorem row_matrix_measurable {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (a b : AsymptoticRationalGroup.Group) : Measurable (fun z => matrix (row hN r e hs hε t z) a b) := by
  cases r <;> exact family_matrix_measurable _ _ hs hε t a b

#print axioms realMatrix_ramified
#print axioms row_norm_le
#print axioms row_covariant
#print axioms row_matrix_measurable

end AsymptoticRegularObservationRows
