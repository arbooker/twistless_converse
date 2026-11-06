module

public import AsymptoticFreshEquationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshRank

open AsymptoticFreshCompactDefects AsymptoticFreshEquation AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticObservationStack
open AsymptoticMixing AsymptoticCornerKernel AsymptoticRegularObservationRows
open UpperHalfPlane MeasureTheory ContinuousLinearMap
open scoped ENNReal

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)

noncomputable def observed (R : ℍ → Space →L[ℂ] Space) (x : ℍ) (i : Fin (q-1)) : Space →L[ℂ] Space :=
  (AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x).comp (R x)

theorem observed_regular (R : ℍ → Space →L[ℂ] Space)
    (hm : ∀ g h,Measurable (fun x => matrix (R x) g h)) (hc : Covariant R) (i : Fin (q-1)) :
    (∀ g h,Measurable (fun x => matrix (observed N q hN hq w hs hε t R x i) g h)) ∧
      Covariant (fun x => observed N q hN hq w hs hε t R x i) :=
  ⟨matrix_comp_measurable _ _ (row_regular N q hN hq w hs hε t i).1 hm,
    covariant_comp _ _ (row_regular N q hN hq w hs hε t i).2 hc⟩

theorem observed_supported (R : ℍ → Space →L[ℂ] Space)
    (hi : ∀ x,Supported (integralGroup q) (R x)) (x : ℍ) (i : Fin (q-1)) :
    Supported (integralGroup q) (observed N q hN hq w hs hε t R x i) :=
  supported_comp _ _ _ (AsymptoticFreshCompactDefects.row_supported N q hN hq w hs hε t i x) (hi x)

noncomputable def stackBound (C : ℝ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (q-1) => Space)).symm.toContinuousLinearMap‖*
    ∑ i,AsymptoticFreshCompactDefects.rowBound N q hN hq w hs hε t i*C

theorem observed_stack_norm (R : ℍ → Space →L[ℂ] Space) (C : ℝ) (hC : 0≤C)
    (hR : ∀ x,‖R x‖≤C) (x : ℍ) :
    ‖stack (observed N q hN hq w hs hε t R x)‖≤stackBound N q hN hq w hs hε t C := by
  apply stack_norm_le _ _
    (fun i => mul_nonneg (AsymptoticFreshCompactDefects.rowBound_nonneg N q hN hq w hs hε t i) hC)
  intro i
  exact (opNorm_comp_le _ _).trans (mul_le_mul
    (AsymptoticFreshCompactDefects.row_norm_le N q hN hq w hs hε t i x) (hR x)
    (norm_nonneg _) (AsymptoticFreshCompactDefects.rowBound_nonneg N q hN hq w hs hε t i))

/-- The mixed individual observations have exactly the kernel of the
existing twist observation after the same reconstruction map. -/
theorem observed_mixed_ker (R : ℍ → Space →L[ℂ] Space) (x : ℍ) :
    (mixed (primeLabels q) (observed N q hN hq w hs hε t R x)).ker=
      ((twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp (R x)).ker := by
  have he : mixed (primeLabels q) (observed N q hN hq w hs hε t R x)=
      -(twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp (R x) := by
    change (∑ i,(translation (primeLabels q i)).comp
      ((AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x).comp (R x)))=_
    rw [show (∑ i,(translation (primeLabels q i)).comp
      ((AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x).comp (R x)))=
        (mixed (primeLabels q) (fun i => AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x)).comp (R x) by
          simp only [mixed,finsetSum_comp,comp_assoc]]
    rw [averaged_eq_negative_twist,neg_comp]
  rw [he]
  ext v
  change -((twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp (R x) v)=0 ↔ _
  exact neg_eq_zero

/-- The fresh-prime rank estimate now applies to the original compact
twist equation and the explicitly constructed individual defects. All
operator regularity, bounds, support and averaging facts are discharged
from the input reconstruction map and terminal corner. -/
theorem rank_loss (P : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (P x)]
    (R : ℍ → Space →L[ℂ] Space)
    (hm : ∀ g h,Measurable (fun x => matrix (R x) g h)) (hc : Covariant R)
    (hi : ∀ x,Supported (integralGroup q) (R x))
    (hr : ∀ x,(R x).comp (P x).starProjection=R x)
    (C : ℝ) (hC : 0≤C) (hR : ∀ x,‖R x‖≤C)
    (hf : trace volume (fun x => (P x).starProjection)<∞) :
    ((trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (remaining (P x) (stack (observed N q hN hq w hs hε t R x))).starProjection)).toReal)/
      (q-1:ℕ)≤
    (trace volume (fun x => (P x).starProjection)).toReal-
      (trace volume (fun x => (remaining (P x)
        ((twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp (R x))).starProjection)).toReal := by
  have hreg := observed_regular N q hN hq w hs hε t R hm hc
  have hp (x : ℍ) (i : Fin (q-1)) :
      (observed N q hN hq w hs hε t R x i).comp (P x).starProjection=
        observed N q hN hq w hs hε t R x i := by
    simp only [observed,comp_assoc,hr]
  have he := prime_corner_rank_loss q P (observed N q hN hq w hs hε t R)
    (fun i => (hreg i).1) (fun i => (hreg i).2)
    (observed_supported N q hN hq w hs hε t R hi) hp (stackBound N q hN hq w hs hε t C)
    (observed_stack_norm N q hN hq w hs hε t R C hC hR) hf
  simpa only [remaining,observed_mixed_ker] using he

#print axioms observed_regular
#print axioms observed_supported
#print axioms observed_stack_norm
#print axioms observed_mixed_ker
#print axioms rank_loss

end AsymptoticFreshRank
