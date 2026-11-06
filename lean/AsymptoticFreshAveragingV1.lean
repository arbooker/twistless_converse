module

public import AsymptoticFreshResiduesV1
public import AsymptoticPrimeMixingV1
public import AsymptoticIntegralBranchSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshAveraging

open Matrix AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticIntegralSubgroup AsymptoticReconstructionBranch AsymptoticFreshResidues
open AsymptoticSubgroupSupport AsymptoticMixing ContinuousLinearMap
open scoped lp

theorem branch_cancel_translation (L b d : ℚ) (hL : L≠0) :
    branch L (-b) d hL*AsymptoticMobiusFold.translation b=branch L 0 d hL := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  ring

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

noncomputable def defectLabel (i : Fin (q-1)) : AsymptoticRationalGroup.Group :=
  AsymptoticFreshMatrices.label N q hN (Fact.out : q.Prime).pos
    ((permutation q N hq i).val+1) (i.val+1)

noncomputable def reflectedLabel (i : Fin (q-1)) : AsymptoticRationalGroup.Group :=
  ofMatrix (branch ((N:ℚ)*q^2) 0 (((i.val+1:ℕ):ℚ)/q) (by
    exact mul_ne_zero (by exact_mod_cast hN.ne') (pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero))))
    (by
      rw [realMatrix_branch,branch_det]
      have hqp : 0<q := (Fact.out : q.Prime).pos
      positivity)

theorem defectLabel_integral (i : Fin (q-1)) : defectLabel N q hN hq i∈integralGroup q :=
  AsymptoticFreshMatrices.label_integral N q hN hq _ _ (quotient q N hq i) (quotient_relation q N hq i)

theorem defectLabel_translation (i : Fin (q-1)) :
    defectLabel N q hN hq i*primeLabels q i=reflectedLabel N q hN (permutation q N hq i) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (AsymptoticFreshMatrices.branchMatrix N q hN.ne' (Fact.out : q.Prime).ne_zero
    ((permutation q N hq i).val+1) (i.val+1))*
    rationalMap (AsymptoticMobiusFold.translation (((i.val+1:ℕ):ℚ)/q))=_
  rw [← map_mul]
  congr 1
  simp only [AsymptoticFreshMatrices.branchMatrix,Int.cast_add,Int.cast_natCast,Int.cast_one,
    Nat.cast_add,Nat.cast_one,neg_div]
  exact branch_cancel_translation _ _ _ _

theorem translation_comp {G : Type*} [Group G] (a b : G) :
    (translation a).comp (translation b)=translation (b*a) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  change v (b*(a*g))=v ((b*a)*g)
  rw [mul_assoc]

theorem translation_supported {G : Type*} [Group G] (S : Subgroup G) (a : G) (ha : a∈S) :
    Supported S (translation a) := by
  intro g h hh
  have hne : a*g≠h := by
    intro he
    apply hh
    rw [← he]
    simpa [mul_assoc] using S.inv_mem ha
  classical
  simp [AsymptoticRegularTrace.matrix,translation_apply,AsymptoticRegularTrace.delta,hne]

/-- The actual individual full-orbit defect w times the g_b branch,
minus the identity. No separate individual equation is assumed. -/
noncomputable def defect (w : ℂ) (i : Fin (q-1)) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  w • translation (defectLabel N q hN hq i)-1

theorem defect_supported (w : ℂ) (i : Fin (q-1)) :
    Supported (integralGroup q) (defect N q hN hq w i) :=
  supported_sub _ _ _ (supported_smul _ _
    (translation_supported _ _ (defectLabel_integral N q hN hq i)) w) (supported_one _)

/-- Reindexing by the proved residue permutation turns the sum of
translated individual defects into the original two branch sums. -/
theorem averaged_defects (w : ℂ) :
    mixed (primeLabels q) (defect N q hN hq w)=
      w • (∑ i,translation (reflectedLabel N q hN i))-
        ∑ i,translation (primeLabels q i) := by
  simp only [mixed,defect,comp_sub,comp_smul,one_def,comp_id,translation_comp,defectLabel_translation]
  rw [Finset.sum_sub_distrib,← Finset.smul_sum]
  congr 1
  exact congrArg (fun B => w • B) (Equiv.sum_comp (permutation q N hq)
    (fun i => translation (reflectedLabel N q hN i)))

#print axioms branch_cancel_translation
#print axioms defectLabel_integral
#print axioms defectLabel_translation
#print axioms translation_comp
#print axioms translation_supported
#print axioms defect_supported
#print axioms averaged_defects

end AsymptoticFreshAveraging
