module

public import AsymptoticFiniteBranchSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches AsymptoticCertificateOperators

noncomputable def regularStripProjection (z : ℍ) : RegularSpace →L[ℂ] RegularSpace :=
  AsymptoticOrbitDiagonal.corner AsymptoticMassTransport.strip z

theorem regular_left_corner (b : Branch) (z : ℍ) (s : Set ℍ)
    (hb : ∀ w,w∉s → b.coefficient w=0) :
    (AsymptoticOrbitDiagonal.corner s z).comp (regular b z)=regular b z := by
  ext1 f
  apply lp.ext
  funext g
  simp only [comp_apply,AsymptoticOrbitDiagonal.corner_apply]
  classical
  by_cases hg : g • z∈s
  · simp [hg]
  · simp only [hg,ite_false,regular,AsymptoticOrbitBranch.operator_apply,hb (g • z) hg,zero_mul]

theorem regular_left_corner_apply (b : Branch) (z : ℍ) (s : Set ℍ)
    (hb : ∀ w,w∉s → b.coefficient w=0) (f : RegularSpace) :
    AsymptoticOrbitDiagonal.corner s z (regular b z f)=regular b z f :=
  congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T f) (regular_left_corner b z s hb)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem regularSum_lowPart_left_strip (hN : 0<N) (P : Parameters A) (t : ℕ) (z : ℍ)
    (v : Index A) (I : Finset ℤ) :
    (regularStripProjection z).comp (regularSum (lowPartExpression A hN P t v I) z)=
      regularSum (lowPartExpression A hN P t v I) z := by
  rw [lowPartExpression,regularSum_ofFinset]
  ext1 f
  simp only [comp_apply,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply regular_left_corner_apply _ z _ _ f
  intro w hz
  change AsymptoticFoldedLow.coefficient _ _ _ _ _ _ _ _ w=0
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_subset_strip A v hr.1.1.1)

theorem regularSum_terminalPart_left_strip (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (z : ℍ) (v : Index A) (I : Finset ℤ) :
    (regularStripProjection z).comp (regularSum (terminalPartExpression A hN P ht v I) z)=
      regularSum (terminalPartExpression A hN P ht v I) z := by
  rw [terminalPartExpression,regularSum_ofFinset]
  ext1 f
  simp only [comp_apply,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply regular_left_corner_apply _ z _ _ f
  intro w hz
  change AsymptoticFoldedTerminal.coefficient _ _ _ _ _ _ _ _ w=0
  apply Set.indicator_of_notMem
  intro hr
  exact hz (cell_subset_strip A v hr.1.1)

theorem regularSum_low_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (t : ℕ) (I : Finset ℤ) (z : ℍ) :
    (regularStripProjection z).comp (regularSum (lowExpression A hN P χ t I) z)=
      regularSum (lowExpression A hN P χ t I) z := by
  rw [lowExpression,regularSum_sumExpressions]
  simp only [regularSum_scale]
  ext1 f
  simp only [comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun u : RegularSpace => amplitude A χ v • u)
    (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T f) (regularSum_lowPart_left_strip A hN P t z v I))

theorem regularSum_terminal_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) :
    (regularStripProjection z).comp (regularSum (terminalExpression A hN P χ ht I) z)=
      regularSum (terminalExpression A hN P χ ht I) z := by
  rw [terminalExpression,regularSum_sumExpressions]
  simp only [regularSum_scale]
  ext1 f
  simp only [comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun u : RegularSpace => amplitude A χ v • u)
    (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T f) (regularSum_terminalPart_left_strip A hN P ht z v I))

theorem regularSum_full_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    (regularStripProjection z).comp (regularSum (fullExpression A hN P χ n I) z)=
      regularSum (fullExpression A hN P χ n I) z := by
  have hK := regularSum_low_left_strip A hN P χ (P.s+3) I z
  have hB := regularSum_terminal_left_strip A hN P χ (by omega : 2≤P.s+3) I z
  have hF := finiteLow_left_fixed (regularStripProjection z) _ _ hK hB n
  have hP : (regularStripProjection z).comp
      (AsymptoticOrbitDiagonal.corner (highStrip P.ε) z)=
      AsymptoticOrbitDiagonal.corner (highStrip P.ε) z := by
    ext1 f
    apply lp.ext
    funext g
    simp only [regularStripProjection,comp_apply,AsymptoticOrbitDiagonal.corner_apply]
    by_cases hg : g • z∈highStrip P.ε
    · simp [hg,hg.1]
    · simp [hg]
  rw [fullExpression,regularSum_compose,regularSum_append,regularSum_neumann]
  have hid : regularSum [identity] z=(1:RegularSpace →L[ℂ] RegularSpace) :=
    (add_zero _).trans (regular_identity z)
  have hc : regularSum [corner (highStrip P.ε) (highStrip_measurable P.ε)] z=
      AsymptoticOrbitDiagonal.corner (highStrip P.ε) z :=
    (add_zero _).trans (regular_corner _ _ z)
  rw [hid,hc]
  ext1 f
  simp only [comp_apply,add_apply,map_add]
  exact congrArg₂ (·+·) (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T f) hP)
    (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T
      (AsymptoticOrbitDiagonal.corner (highStrip P.ε) z f)) hF)

#print axioms regular_left_corner
#print axioms regularSum_lowPart_left_strip
#print axioms regularSum_terminalPart_left_strip
#print axioms regularSum_low_left_strip
#print axioms regularSum_terminal_left_strip
#print axioms regularSum_full_left_strip

end AsymptoticFiniteBranch
