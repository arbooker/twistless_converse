module

public import QuantitativeArithmeticRetainedFiniteExtensionV1
public import AsymptoticFiniteBranchSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteExpressions
open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators (cell)
open AsymptoticHyperbolicSlash (Space)

private theorem fixed_sum {ι : Type*} (I : Finset ι) (F : ι → Space →L[ℂ] Space)
    (hF : ∀ i∈I,stripProjection.comp (F i)=F i) :
    stripProjection.comp (∑ i∈I,F i)=∑ i∈I,F i := by
  ext1 f
  simp only [comp_apply,sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i hi => congrArg (fun T : Space →L[ℂ] Space => T f) (hF i hi))

private theorem fixed_scale (c : ℂ) (F : Space →L[ℂ] Space)
    (hF : stripProjection.comp F=F) : stripProjection.comp (c • F)=c • F := by
  rw [comp_smul,hF]

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

include hQ in
private theorem cell_strip {ε : ℝ} (j : Fin Q) {z : ℍ} (hz : z∈cell ε j) :
    z∈AsymptoticMassTransport.strip := by
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hj : (j:ℝ)+1≤Q := by exact_mod_cast j.isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hQr.le).trans hz.1.1,
    hz.1.2.trans_le ((div_le_one hQr).mpr hj)⟩

private theorem primitiveLow_left (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : SpanningIntegerRows.RowIndex N Q) (t : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (primitiveLowExpression A hN P j i t I) m)=
      holomorphicSum (primitiveLowExpression A hN P j i t I) m := by
  rw [primitiveLowExpression,holomorphicSum_sumExpressions]
  apply fixed_sum
  intro d _
  rw [holomorphicSum_ofFinset]
  apply fixed_sum
  intro n _
  apply holomorphic_left_corner
  intro z hz
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_strip (hQ:=hQ) j hr.1.1)

private theorem primitiveTerminal_left (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : SpanningIntegerRows.RowIndex N Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (primitiveTerminalExpression A hN P j i ht I) m)=
      holomorphicSum (primitiveTerminalExpression A hN P j i ht I) m := by
  rw [primitiveTerminalExpression,holomorphicSum_sumExpressions]
  apply fixed_sum
  intro d _
  rw [holomorphicSum_ofFinset]
  apply fixed_sum
  intro n _
  apply holomorphic_left_corner
  intro z hz
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_strip (hQ:=hQ) j hr.1)

variable (hS : ∀p∈S,p.Prime)

private theorem retainedLow_left (P : Parameters A) (j : Fin Q)
    (p : S) (u : ℤ) (t m : ℕ) :
    stripProjection.comp (holomorphicSum (retainedLowExpression A hS P j p u t) m)=
      holomorphicSum (retainedLowExpression A hS P j p u t) m := by
  rw [retainedLowExpression,holomorphicSum_ofFinset]
  apply fixed_sum
  intro n _
  rw [QuantitativeArithmeticRetainedDilationBranches.lowBranch,holomorphic_scale]
  apply fixed_scale
  apply holomorphic_left_corner
  intro z hz
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_strip (hQ:=hQ) j hr.1)

private theorem retainedTerminal_left (P : Parameters A) (j : Fin Q)
    (p : S) (u : ℤ) (t m : ℕ) :
    stripProjection.comp (holomorphicSum (retainedTerminalExpression A hS P j p u t) m)=
      holomorphicSum (retainedTerminalExpression A hS P j p u t) m := by
  rw [retainedTerminalExpression,holomorphicSum_ofFinset]
  apply fixed_sum
  intro n _
  apply holomorphic_left_corner
  intro z hz
  change _ * QuantitativeArithmeticRetainedDilationOperator.coefficient _ _ _ _ _ _ z=0
  suffices hc : QuantitativeArithmeticRetainedDilationOperator.coefficient _ _ _ _ _ _ z=0 by rw [hc,mul_zero]
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_strip (hQ:=hQ) j hr.1)

theorem low_left_strip (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (t : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (lowExpression A hS hN P χ β t I) m)=
      holomorphicSum (lowExpression A hS hN P χ β t I) m := by
  rw [lowExpression,holomorphicSum_sumExpressions]
  apply fixed_sum
  intro j _
  rw [holomorphicSum_sumExpressions]
  apply fixed_sum
  intro i _
  rw [holomorphicSum_scale]
  apply fixed_scale
  cases i with
  | inl i =>
    rw [rowLowExpression,holomorphicSum_scale]
    exact fixed_scale _ _ (primitiveLow_left A hN P j i t I m)
  | inr i =>
    rw [rowLowExpression,holomorphicSum_scale]
    exact fixed_scale _ _ (retainedLow_left A hS P j i.1 i.2 t m)

theorem terminal_left_strip (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (terminalExpression A hS hN P χ β ht I) m)=
      holomorphicSum (terminalExpression A hS hN P χ β ht I) m := by
  rw [terminalExpression,holomorphicSum_sumExpressions]
  apply fixed_sum
  intro j _
  rw [holomorphicSum_sumExpressions]
  apply fixed_sum
  intro i _
  rw [holomorphicSum_scale]
  apply fixed_scale
  cases i with
  | inl i =>
    rw [rowTerminalExpression,holomorphicSum_scale]
    exact fixed_scale _ _ (primitiveTerminal_left A hN P j i ht I m)
  | inr i =>
    rw [rowTerminalExpression,holomorphicSum_scale]
    exact fixed_scale _ _ (retainedTerminal_left A hS P j i.1 i.2 t m)

theorem full_left_strip (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (fullExpression A hS hN P χ β ht n I) m)=
      holomorphicSum (fullExpression A hS hN P χ β ht n I) m := by
  let H := QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P
  let K := holomorphicSum (lowExpression A hS hN P χ β t I) m
  let T := holomorphicSum (terminalExpression A hS hN P χ β ht I) m
  have hH : stripProjection.comp H=H := by
    have ha := congrArg ContinuousLinearMap.adjoint
      (AsymptoticRegionL2.projection_comp_of_subset volume
        (AsymptoticCertificateOperators.highStrip P.ε)
        (AsymptoticCertificateOperators.highStrip_measurable P.ε)
        AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable (fun _ hz => hz.1))
    simpa only [adjoint_comp,AsymptoticRegionL2.projection_adjoint,stripProjection,H,
      QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection] using ha
  have hT : stripProjection.comp T=T := terminal_left_strip A hS hN P χ β ht I m
  have hF : stripProjection.comp ((1+T).comp H)=(1+T).comp H := by
    ext1 f
    simp only [comp_apply,add_apply,map_add]
    exact congrArg₂ (·+·) (congrArg (fun R : Space →L[ℂ] Space => R f) hH)
      (congrArg (fun R : Space →L[ℂ] Space => R (H f)) hT)
  have hneumann := finiteLow_left_fixed stripProjection K ((1+T).comp H)
    (low_left_strip A hS hN P χ β t I m) hF n
  rw [holomorphic_fullExpression]
  simpa only [AsymptoticReconstruction.finiteLow,comp_assoc] using hneumann

theorem full_right_terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    (holomorphicSum (fullExpression A hS hN P χ β ht n I) m).comp
      (QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P)=
      holomorphicSum (fullExpression A hS hN P χ β ht n I) m := by
  rw [holomorphic_fullExpression]
  ext1 f
  simp only [comp_apply]
  rw [show QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P
    (QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P f)=
    QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P f from
      AsymptoticRegionL2.projection_idempotent _ _ _ f]

theorem regular_full_right_terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    (regularSum (fullExpression A hS hN P χ β ht n I) z).comp
      (QuantitativeArithmeticRetainedRegularExtension.highProjection A P z)=
      regularSum (fullExpression A hS hN P χ β ht n I) z := by
  rw [regular_fullExpression]
  ext1 f
  simp only [comp_apply]
  rw [show QuantitativeArithmeticRetainedRegularExtension.highProjection A P z
    (QuantitativeArithmeticRetainedRegularExtension.highProjection A P z f)=
    QuantitativeArithmeticRetainedRegularExtension.highProjection A P z f from
      congrArg (fun R : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space => R f)
        (AsymptoticOrbitDiagonal.corner_idempotent _ _)]

#print axioms full_left_strip
#print axioms full_right_terminal
#print axioms regular_full_right_terminal
end QuantitativeArithmeticRetainedFiniteExpressions
