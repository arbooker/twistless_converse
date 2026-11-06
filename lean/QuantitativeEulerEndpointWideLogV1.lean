module

public import QuantitativeEulerEndpointWideGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerEndpointNormalizedThreshold

 theorem widePacketBound_nonneg (N q : ℕ) (w : ℂ) (R Y H : ℝ) (t : ℕ) :
    0≤widePacketBound N q w R Y H t := by
  have hh := (wideDistortion_pos (N*q^3:ℕ) R H).le
  unfold widePacketBound
  positivity

theorem wide_square_sum_polynomial (N : ℕ) (w : ℂ) (R Y H U : ℝ) (t : ℕ)
    (l : List (EligiblePrime N)) (hU : 1≤U) (hN : (N:ℝ)≤U)
    (hq : ∀ p∈l, (p.val:ℝ)≤U) (hw : ‖w‖≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) (hlen : (l.length:ℝ)≤U) :
    squareSum (wideSequenceBound N w R Y H t l) l.length≤
      (72*9^t)^2*U^(1+2*(9+10*t)) := by
  have hU0 : 0≤U := by linarith
  have hrow (i : Fin l.length) :
      0≤wideSequenceBound N w R Y H t l i ∧
      wideSequenceBound N w R Y H t l i≤72*9^t*U^(9+10*t) := by
    unfold wideSequenceBound
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
    simp only [List.getElem_map]
    exact ⟨widePacketBound_nonneg _ _ _ _ _ _ _,
      widePacketBound_polynomial N l[i.val].val w R Y H U t hU hN
        (hq _ (List.getElem_mem _)) hw hR0 hR hH0 hH hY hYinv⟩
  calc
    _ ≤ ∑ _i : Fin l.length, (72*9^t*U^(9+10*t))^2 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hrow i).1 (hrow i).2 2)
    _ = (l.length:ℝ)*(72*9^t*U^(9+10*t))^2 := by simp
    _ ≤ U*(72*9^t*U^(9+10*t))^2 := mul_le_mul_of_nonneg_right hlen (sq_nonneg _)
    _ = _ := by rw [mul_pow,←pow_mul,pow_add]; simp only [pow_one]; ring

/-- Logarithmic normalization grows linearly in log U. Both the
actual finite row family and its cardinality are included. -/
theorem wide_normalization_log (N : ℕ) (w : ℂ) (R Y H U A : ℝ) (t r : ℕ)
    (l : List (EligiblePrime N)) (hU : 1≤U) (hN : (N:ℝ)≤U)
    (hq : ∀ p∈l, (p.val:ℝ)≤U) (hw : ‖w‖≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) (hlen : (l.length:ℝ)≤U)
    (hA0 : 0≤A) (hA : A≤U^r) :
    Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor
      (wideSequenceBound N w R Y H t l) l.length*threshold A)^2)≤
      Real.log 4+Real.log 3+2*Real.log (1+(72*9^t)^2)+
        ((r:ℝ)+2*(1+2*(9+10*t)))*Real.log U := by
  have hUpos : 0<U := by linarith
  let d : ℕ := 1+2*(9+10*t)
  let M : ℝ := (72*9^t)^2
  let C := wideSequenceBound N w R Y H t l
  have hS : squareSum C l.length≤M*U^d :=
    wide_square_sum_polynomial N w R Y H U t l hU hN hq hw hR0 hR hH0 hH hY hYinv hlen
  have hSpos : 0<1+squareSum C l.length := by linarith [squareSum_nonneg C l.length]
  have hM : 0≤M := sq_nonneg _
  have hSlog : Real.log (1+squareSum C l.length)≤Real.log (1+M)+(d:ℝ)*Real.log U := by
    have hh : 1+squareSum C l.length≤(1+M)*U^d := by
      nlinarith [one_le_pow₀ hU (n:=d)]
    have hhlog := Real.log_le_log hSpos hh
    rwa [Real.log_mul (by positivity) (pow_pos hUpos d).ne',Real.log_pow] at hhlog
  have hAlog : Real.log (1+2*A)≤Real.log 3+(r:ℝ)*Real.log U := by
    have hh : 1+2*A≤3*U^r := by linarith [one_le_pow₀ hU (n:=r)]
    have hhlog := Real.log_le_log (show 0<1+2*A by positivity) hh
    rwa [Real.log_mul (by norm_num) (pow_pos hUpos r).ne',Real.log_pow] at hhlog
  rw [logarithmic_cost _ _ hA0]
  have hd : (d:ℝ)=1+2*(9+10*(t:ℝ)) := by dsimp only [d]; push_cast; ring
  rw [hd] at hSlog
  dsimp only [C,M] at hSlog
  linarith

#print axioms wide_square_sum_polynomial
#print axioms wide_normalization_log
end QuantitativeEulerEndpointPrepared
