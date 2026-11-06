module

public import AsymptoticIntegralTranslationsV1
public import AsymptoticMixingGlobalV1
public import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open AsymptoticRationalGroup AsymptoticMobiusFold Matrix

theorem translationLabel_mul (r s : ℚ) :
    translationLabel r*translationLabel s=translationLabel (r+s) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (translation r)*rationalMap (translation s)=rationalMap (translation (r+s))
  rw [← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translation,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

theorem translationLabel_inv (r : ℚ) : (translationLabel r)⁻¹=translationLabel (-r) := by
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap (translation r))⁻¹=rationalMap (translation (-r))
  rw [← map_inv,translation_inv]

theorem translationLabel_sub (r s : ℚ) :
    translationLabel r*(translationLabel s)⁻¹=translationLabel (r-s) := by
  rw [translationLabel_inv,translationLabel_mul,sub_eq_add_neg]

/-- The q-1 translated residue labels in the actual rational group. -/
noncomputable def primeLabels (q : ℕ) (i : Fin (q-1)) : AsymptoticRationalGroup.Group :=
  translationLabel (((i.val+1:ℕ):ℚ)/q)

theorem primeLabels_separated (q : ℕ) [Fact q.Prime] (i j : Fin (q-1)) (hij : i≠j) :
    primeLabels q j*(primeLabels q i)⁻¹∉integralGroup q := by
  have hn : ¬(q:ℤ)∣(j.val:ℤ)-(i.val:ℤ) := by
    intro hd
    have he := Int.modEq_iff_dvd.mpr hd
    change (i.val:ℤ)%(q:ℤ)=(j.val:ℤ)%(q:ℤ) at he
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (lt_of_lt_of_le i.isLt (Nat.sub_le q 1))),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (lt_of_lt_of_le j.isLt (Nat.sub_le q 1)))] at he
    exact hij (Fin.ext (by exact_mod_cast he))
  have he : (((j.val+1:ℕ):ℚ)/q)-(((i.val+1:ℕ):ℚ)/q)=(((j.val:ℤ)-(i.val:ℤ):ℤ):ℚ)/q := by
    push_cast
    ring
  simpa only [primeLabels,translationLabel_sub,he] using translationLabel_fraction_not_mem q _ hn

#print axioms translationLabel_mul
#print axioms translationLabel_inv
#print axioms translationLabel_sub
#print axioms primeLabels_separated

end AsymptoticIntegralSubgroup

namespace AsymptoticMixing

open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticObservationStack
open AsymptoticCornerKernel AsymptoticRegularTrace MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

/-- One-prime loss for the actual rational projective group and its
q-integral subgroup. The only support input is integrality of the
original defect rows; separation and polar regularity are proved. -/
theorem prime_corner_rank_loss (q : ℕ) [Fact q.Prime]
    (P : UpperHalfPlane → Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ))
    [∀ x,CompleteSpace (P x)]
    (L : UpperHalfPlane → Fin (q-1) → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (hL : ∀ x i,Supported (integralGroup q) (L x i))
    (hP : ∀ x i,(L x i).comp (P x).starProjection=L x i)
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) (hf : trace volume (fun x => (P x).starProjection)<∞) :
    ((trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (remaining (P x) (stack (L x))).starProjection)).toReal)/(q-1:ℕ)≤
    (trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (remaining (P x) (mixed (primeLabels q) (L x))).starProjection)).toReal := by
  have hi : 0<Fintype.card (Fin (q-1)) := by
    rw [Fintype.card_fin]
    exact Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  simpa only [Fintype.card_fin] using corner_rank_loss volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hi P L hm hc hL hP M hM hf

#print axioms prime_corner_rank_loss

end AsymptoticMixing
