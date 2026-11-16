module

public import QuantitativeMaassCountingAdmissibleApproximationV1
public import QuantitativeMaassCountingSectorProjectionV1
public import QuantitativeMaassOperatorProductApproximationV1
public import QuantitativeMaassStrongMomentScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter AsymptoticSectorSigns
open scoped Topology
namespace QuantitativeMaass.Counting

theorem localNewFilter_norm_two (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (m : ℕ) (p : ↥N.primeFactors) :
    ‖localNewFilter N hN m p‖≤2 := by
  obtain ⟨ρ,hρ,hρ1,hh⟩ := localNewFilter_approximation N hN hAd p
  let P := (AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection
  calc
    _ = ‖(localNewFilter N hN m p-P)+P‖ := by rw [sub_add_cancel]
    _ ≤ ‖localNewFilter N hN m p-P‖+‖P‖ := norm_add_le _ _
    _ ≤ ρ^m+1 := add_le_add (hh m) (Submodule.starProjection_norm_le _)
    _ ≤ 2 := by have hp := pow_le_one₀ (n:=m) hρ hρ1.le; linarith

theorem localNewFilter_weighted_limit (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (p : ↥N.primeFactors)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖localNewFilter N hN (growingLVDegree t) p-
        (AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection‖/ε t) atTop (𝓝 0) := by
  obtain ⟨ρ,hρ,hρ1,hh⟩ := localNewFilter_approximation N hN hAd p
  let q := (ρ+1)/2
  have hq : 0<q := by dsimp only [q]; linarith
  have hq1 : q<1 := by dsimp only [q]; linarith
  have hρq : ρ≤q := by dsimp only [q]; linarith
  have hl := Strong.weighted_growingMomentDegree_decay ε q W hq hq1 hε hp
  apply squeeze_zero' (hε.mono (fun t ht => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ht.le)) _ hl
  filter_upwards [hε] with t ht
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((hh _).trans (pow_le_pow_left₀ hρ hρq _)) (Real.exp_pos _).le) ht.le

/-- The ordered product of the actual local counting filters converges
to the actual total-new projection with all fixed strong-scale weights. -/
theorem totalNewFilter_weighted_limit (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖totalNewFilter N hN (growingLVDegree t)-(AsymptoticTotalNewCorner.space N hN).starProjection‖/ε t)
      atTop (𝓝 0) := by
  let P := fun p : ↥N.primeFactors => (AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection
  let L := (Finset.univ : Finset ↥N.primeFactors).toList
  let err := fun t p => ‖localNewFilter N hN (growingLVDegree t) p-P p‖
  have hs (l : List ↥N.primeFactors) :
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*(l.map (err t)).sum/ε t) atTop (𝓝 0) := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hh := (localNewFilter_weighted_limit N hN hAd p ε hε hp W).add ih
      rw [add_zero] at hh
      convert hh using 1
      funext t
      simp only [List.map_cons,List.sum_cons,err]
      ring
  have hl := (hs L).const_mul ((2:ℝ)^L.length)
  rw [mul_zero] at hl
  apply squeeze_zero' (hε.mono (fun t ht => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ht.le)) _ hl
  filter_upwards [hε] with t ht
  have hb := operator_list_product_difference (localNewFilter N hN (growingLVDegree t)) P
    (localNewFilter_norm_two N hN hAd _) (fun p => Submodule.starProjection_norm_le _) L
  change ‖totalNewFilter N hN (growingLVDegree t)-(L.map P).prod‖≤_ at hb
  rw [localProjection_product N hN] at hb
  calc
    _ ≤ Real.exp (W*Strong.strongScale t)*
        ((2:ℝ)^L.length*(L.map (err t)).sum)/ε t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb
        (Real.exp_pos (W*Strong.strongScale t)).le) ht.le
    _ = _ := by ring

#print axioms localNewFilter_norm_two
#print axioms localNewFilter_weighted_limit
#print axioms totalNewFilter_weighted_limit
end QuantitativeMaass.Counting
