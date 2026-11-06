module

public import QuantitativeNewGapTreeHeckeLabelsV1
public import QuantitativeNewGapTreeHeckeSymmetryV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open QuantitativeMaass AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticRegularTrace
open scoped BigOperators lp

attribute [local instance] Classical.propDecidable

theorem regularHecke_apply_option (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (f : ℓ²(Classes (gamma M),ℂ)) (g : AsymptoticRationalGroup.Group) :
    regularHecke M p f (classOf (gamma M) g)=((p+1 : ℕ) : ℂ)⁻¹ *
      ∑ j : Option (ZMod p), f (classOf (gamma M) (heckeBranchLabel p (Fact.out : p.Prime).pos j*g)) := by
  rw [regularHecke_apply_prime M p hpM,Fintype.sum_option]
  congr 1
  congr 1
  have hv (a : Fin p) : ((ZMod.finEquiv p).toEquiv a).val=a.val := by
    cases p with
    | zero => exact Fin.elim0 a
    | succ p => rfl
  simpa only [heckeBranchLabel,hv] using (ZMod.finEquiv p).toEquiv.sum_comp
    (fun a : ZMod p => f (classOf (gamma M) (upperHeckeLabel p (Fact.out : p.Prime).pos a.val*g)))

/-- The actual quotient delta vector tests exactly the projective identity
condition used by the integral returning-word count. -/
theorem word_delta (M : ℕ) (R : HeckeUpper) (hR : 0 < R.det) :
    delta (classOf (gamma M) 1) (classOf (gamma M) (wordLabel R hR)) =
      if HeckeUpper.projectiveGamma M R then 1 else 0 := by
  classical
  have he : classOf (gamma M) (wordLabel R hR)=classOf (gamma M) 1 ↔
      HeckeUpper.projectiveGamma M R := by
    rw [classOf_eq_iff,inv_one,mul_one,wordLabel_mem_gamma_iff]
  by_cases h : HeckeUpper.projectiveGamma M R
  · simp [delta,(he.mpr h),h]
  · have hn := mt he.mp h
    simp [delta,h,hn]

/-- Every power of the literal arithmetic Hecke operator has the checked
integral-word expansion, at all positive upper-triangular word labels. -/
theorem regularHecke_power_word (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬p ∣ M)
    (n : ℕ) (R : HeckeUpper) (hR : 0 < R.det) :
    ((regularHecke M p)^n) (delta (classOf (gamma M) 1))
      (classOf (gamma M) (wordLabel R hR)) =
        (((p+1 : ℕ) : ℂ)⁻¹)^n * (HeckeUpper.cosetWalks M p n R : ℂ) := by
  induction n generalizing R with
  | zero =>
    change delta (classOf (gamma M) 1) (classOf (gamma M) (wordLabel R hR)) = _
    rw [word_delta]
    simp only [pow_zero,one_mul,HeckeUpper.cosetWalks]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ']
    change regularHecke M p (((regularHecke M p)^n) (delta (classOf (gamma M) 1)))
      (classOf (gamma M) (wordLabel R hR)) = _
    rw [regularHecke_apply_option M p hpM]
    simp_rw [← wordLabel_left p (Fact.out : p.Prime).pos _ R hR,ih]
    rw [← Finset.mul_sum,← mul_assoc,← pow_succ']
    simp only [HeckeUpper.cosetWalks,Nat.cast_sum]

theorem wordLabel_root : wordLabel HeckeUpper.root (by norm_num [HeckeUpper.root_det])=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change AsymptoticRationalGroup.rationalMap (wordGL HeckeUpper.root _)=1
  have he : wordGL HeckeUpper.root (by norm_num [HeckeUpper.root_det])=1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wordGL,HeckeUpper.root,HeckeUpper.matrix,Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [he,map_one]

/-- Exact rooted moments of the actual arithmetic operator. The subsequent
full norm estimate uses separately proved quotient faithfulness. -/
theorem regularHecke_power_root (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬p ∣ M)
    (n : ℕ) :
    ((regularHecke M p)^n) (delta (classOf (gamma M) 1)) (classOf (gamma M) 1)=
      (((p+1 : ℕ) : ℂ)⁻¹)^n*(treeWalkCount (p+1) n 0 : ℂ) := by
  have hh := regularHecke_power_word M p hpM n HeckeUpper.root (by norm_num [HeckeUpper.root_det])
  rwa [wordLabel_root,HeckeUpper.cosetWalks_root_eq_tree] at hh

#print axioms word_delta
#print axioms regularHecke_power_word
#print axioms regularHecke_power_root

end QuantitativeNewGap
