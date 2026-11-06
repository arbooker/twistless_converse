module

public import AsymptoticFiniteBranchWeightV1
public import AsymptoticCylinderTerminalLiftV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Filter Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches AsymptoticCertificateOperators
open AsymptoticHyperbolicSlash (Space)

noncomputable def stripProjection : Space →L[ℂ] Space :=
  AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable

theorem holomorphic_left_corner (b : Branch) (m : ℕ) (s : Set ℍ) (hs : MeasurableSet s)
    (hb : ∀ z,z∉s → b.coefficient z=0) :
    (AsymptoticRegionL2.projection volume s hs).comp (holomorphic b m)=holomorphic b m := by
  ext1 f
  apply (AsymptoticRegionL2.projection_eq_self_iff volume s hs _).mpr
  filter_upwards [AsymptoticConcreteRationalBranch.operator_coeFn b.label b.coefficient b.measurable b.norm_le m f]
    with z hz hzs
  change AsymptoticConcreteRationalBranch.operator b.label b.coefficient b.measurable b.norm_le m f z=0
  rw [hz,hb z hzs,zero_mul,zero_mul]

theorem holomorphic_left_corner_apply (b : Branch) (m : ℕ) (s : Set ℍ) (hs : MeasurableSet s)
    (hb : ∀ z,z∉s → b.coefficient z=0) (f : Space) :
    AsymptoticRegionL2.projection volume s hs (holomorphic b m f)=holomorphic b m f :=
  congrArg (fun T : Space →L[ℂ] Space => T f) (holomorphic_left_corner b m s hs hb)

theorem finiteLow_left_fixed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P K B : E →L[ℂ] E)
    (hK : P.comp K=K) (hB : P.comp B=B) (n : ℕ) :
    P.comp (AsymptoticReconstruction.finiteLow K B n)=AsymptoticReconstruction.finiteLow K B n := by
  ext1 f
  have hpow (j : ℕ) : P ((K^j) (B f))=(K^j) (B f) := by
    cases j with
    | zero =>
      change P (B f)=B f
      exact congrArg (fun T : E →L[ℂ] E => T f) hB
    | succ j =>
      rw [pow_succ']
      exact congrArg (fun T : E →L[ℂ] E => T ((K^j) (B f))) hK
  simp only [AsymptoticReconstruction.finiteLow,comp_apply,sum_apply,map_sum,hpow]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem holomorphicSum_lowPart_left_strip (hN : 0<N) (P : Parameters A) (t m : ℕ)
    (v : Index A) (I : Finset ℤ) :
    stripProjection.comp (holomorphicSum (lowPartExpression A hN P t v I) m)=
      holomorphicSum (lowPartExpression A hN P t v I) m := by
  rw [lowPartExpression,holomorphicSum_ofFinset]
  ext1 f
  simp only [comp_apply,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply holomorphic_left_corner_apply _ m _ AsymptoticMassTransport.strip_measurable _ f
  intro z hz
  change AsymptoticFoldedLow.coefficient _ _ _ _ _ _ _ _ z=0
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_subset_strip A v hr.1.1.1)

theorem holomorphicSum_terminalPart_left_strip (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) (I : Finset ℤ) :
    stripProjection.comp (holomorphicSum (terminalPartExpression A hN P ht v I) m)=
      holomorphicSum (terminalPartExpression A hN P ht v I) m := by
  rw [terminalPartExpression,holomorphicSum_ofFinset]
  ext1 f
  simp only [comp_apply,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply holomorphic_left_corner_apply _ m _ AsymptoticMassTransport.strip_measurable _ f
  intro z hz
  change AsymptoticFoldedTerminal.coefficient _ _ _ _ _ _ _ _ z=0
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_subset_strip A v hr.1.1)

theorem holomorphicSum_low_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (t : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (lowExpression A hN P χ t I) m)=
      holomorphicSum (lowExpression A hN P χ t I) m := by
  rw [lowExpression,holomorphicSum_sumExpressions]
  simp only [holomorphicSum_scale]
  ext1 f
  simp only [comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun u : Space => amplitude A χ v • u)
    (congrArg (fun T : Space →L[ℂ] Space => T f) (holomorphicSum_lowPart_left_strip A hN P t m v I))

theorem holomorphicSum_terminal_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (terminalExpression A hN P χ ht I) m)=
      holomorphicSum (terminalExpression A hN P χ ht I) m := by
  rw [terminalExpression,holomorphicSum_sumExpressions]
  simp only [holomorphicSum_scale]
  ext1 f
  simp only [comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun u : Space => amplitude A χ v • u)
    (congrArg (fun T : Space →L[ℂ] Space => T f) (holomorphicSum_terminalPart_left_strip A hN P ht m v I))

theorem holomorphicSum_full_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (fullExpression A hN P χ n I) m)=
      holomorphicSum (fullExpression A hN P χ n I) m := by
  have hK := holomorphicSum_low_left_strip A hN P χ (P.s+3) I m
  have hB := holomorphicSum_terminal_left_strip A hN P χ (by omega : 2≤P.s+3) I m
  rw [holomorphicSum_lowExpression] at hK
  rw [holomorphicSum_terminalExpression] at hB
  have hF := finiteLow_left_fixed stripProjection _ _ hK hB n
  have hP : stripProjection.comp (highProjection A P)=highProjection A P := by
    have hh := AsymptoticRegionL2.projection_comp_of_subset volume (highStrip P.ε)
      (highStrip_measurable P.ε) AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable
      (fun _ hz => hz.1)
    have ha := congrArg ContinuousLinearMap.adjoint hh
    simpa only [adjoint_comp,AsymptoticRegionL2.projection_adjoint,stripProjection,highProjection] using ha
  rw [holomorphicSum_fullExpression]
  ext1 f
  simp only [comp_apply,add_apply,map_add]
  exact congrArg₂ (·+·) (congrArg (fun T : Space →L[ℂ] Space => T f) hP)
    (congrArg (fun T : Space →L[ℂ] Space => T (highProjection A P f)) hF)

theorem holomorphicSum_full_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    (holomorphicSum (fullExpression A hN P χ n I) m).comp (highProjection A P)=
      holomorphicSum (fullExpression A hN P χ n I) m := by
  rw [holomorphicSum_fullExpression]
  ext1 f
  simp only [comp_apply]
  rw [show highProjection A P (highProjection A P f)=highProjection A P f from
    AsymptoticRegionL2.projection_idempotent _ _ _ f]

#print axioms holomorphic_left_corner
#print axioms finiteLow_left_fixed
#print axioms holomorphicSum_lowPart_left_strip
#print axioms holomorphicSum_terminalPart_left_strip
#print axioms holomorphicSum_low_left_strip
#print axioms holomorphicSum_terminal_left_strip
#print axioms holomorphicSum_full_left_strip
#print axioms holomorphicSum_full_right_terminal

end AsymptoticFiniteBranch
