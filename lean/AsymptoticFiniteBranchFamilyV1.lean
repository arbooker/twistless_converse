module

public import AsymptoticFiniteBranchCompactV1
public import AsymptoticRegularObservationRowsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap
open AsymptoticRationalFreeness AsymptoticCylinderLift

variable {ι : Type*} [Fintype ι]

noncomputable def compactFamilyExpression (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : Expression :=
  sumExpressions Finset.univ (fun i => scaleExpression (c i)
    (compactExpression (b i).matrix (b i).positive hs.measurableSet hε t
      (AsymptoticCompactBranch.data (realMatrix (b i).matrix) hs hε t)))

noncomputable def compactFamilyHolomorphic (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  ∑ i,c i • AsymptoticCompactBranch.compactOperator (realMatrix (b i).matrix) hs hε t m

theorem holomorphicSum_compactFamilyExpression (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    holomorphicSum (compactFamilyExpression b c hs hε t) m=
      (compactFamilyHolomorphic b c hs hε t m).comp
        (AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable) := by
  rw [compactFamilyExpression,holomorphicSum_sumExpressions]
  simp only [holomorphicSum_scale,holomorphicSum_compactExpression,
    compactFamilyHolomorphic,AsymptoticCompactBranch.compactOperator]
  ext1 f
  simp only [comp_apply,sum_apply,smul_apply]

theorem regularSum_compactFamilyExpression (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    regularSum (compactFamilyExpression b c hs hε t) z=
      AsymptoticRegularBranchFamily.family b c hs hε t z := by
  rw [compactFamilyExpression,regularSum_sumExpressions]
  simp only [regularSum_scale,regularSum_compactExpression,AsymptoticRegularBranchFamily.family,
    AsymptoticRegularBranchFamily.compact]

theorem strip_projection_lift (f : AsymptoticCylinder.Space) :
    AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
      AsymptoticMassTransport.strip_measurable (lift f)=lift f := by
  apply Lp.ext
  filter_upwards [AsymptoticRegionL2.projection_coeFn volume AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable (lift f),lift_zero_off_strip f] with z hp hz
  rw [hp]
  classical
  by_cases hs : z∈AsymptoticMassTransport.strip
  · exact indicator_of_mem hs _
  · rw [indicator_of_notMem hs,hz hs]

theorem cylinder_compactFamilyExpression (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    (holomorphicSum (compactFamilyExpression b c hs hε t) m).comp lift.toContinuousLinearMap=
      (compactFamilyHolomorphic b c hs hε t m).comp lift.toContinuousLinearMap := by
  rw [holomorphicSum_compactFamilyExpression]
  ext1 f
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,strip_projection_lift]

noncomputable def rowExpression {N : ℕ} (hN : 0<N) (r : AsymptoticCompactObservationCount.Row N)
    (e : AsymptoticSectorSigns.Sector N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Expression :=
  match r with
  | .twist q hq => compactFamilyExpression (AsymptoticRegularObservationRows.twistBranches N q hN hq)
      (Sum.elim (fun _ => 1) (fun _ => -AsymptoticSectorSigns.multiplier e q)) hs hε t
  | .ramified p hp _ => compactFamilyExpression (AsymptoticRegularObservationRows.ramifiedBranches p hp.pos)
      (Sum.elim (fun _ => 1) (fun _ => -AsymptoticCylinderRamified.eigenvalue e p)) hs hε t

theorem regularSum_rowExpression {N : ℕ} (hN : 0<N) (r : AsymptoticCompactObservationCount.Row N)
    (e : AsymptoticSectorSigns.Sector N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    regularSum (rowExpression hN r e hs hε t) z=
      AsymptoticRegularObservationRows.row hN r e hs hε t z := by
  cases r <;> exact regularSum_compactFamilyExpression _ _ hs hε t z

#print axioms holomorphicSum_compactFamilyExpression
#print axioms regularSum_compactFamilyExpression
#print axioms strip_projection_lift
#print axioms cylinder_compactFamilyExpression
#print axioms regularSum_rowExpression

end AsymptoticFiniteBranch
