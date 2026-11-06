module

public import QuantitativeHolomorphicSharpTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCertificateBranches AsymptoticCertificateOperators AsymptoticRegularCertificate
open AsymptoticFoldMajorant

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem expressionBound_ofFinset {ι : Type*} (I : Finset ι) (f : ι → Branch) :
    expressionBound (ofFinset I f)=∑ i∈I, (f i).bound := by
  simp [expressionBound,ofFinset,List.map_map,Function.comp_def,Finset.sum_map_toList]

theorem lowPartExpression_mass_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (v : Index A) (I : Finset ℤ) :
    expressionBound (lowPartExpression A hN P t v I)≤P.ρ^(t-1)*(3*P.ρ+16/level A v) := by
  rw [lowPartExpression,expressionBound_ofFinset]
  change (∑ n∈I, majorant P.ρ (4/(levelQ A v:ℝ)) n^t)≤_
  rw [levelQ_cast]
  have hD : 0≤4/level A v := div_nonneg (by norm_num) (level_pos A hN v).le
  have hb := power_summable_bound P.rho_pos.le hD ht
  have hs := Summable.sum_le_tsum I (fun n _ => pow_nonneg (majorant_nonneg P.rho_pos.le hD n) t) hb.1
  apply hs.trans
  convert hb.2 using 1
  ring

theorem terminalPartExpression_mass_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (I : Finset ℤ) :
    expressionBound (terminalPartExpression A hN P ht v I)≤3+4*((P.ε*level A v)^2)⁻¹ := by
  rw [terminalPartExpression,expressionBound_ofFinset]
  change (∑ n∈I, majorant 1 ((P.ε*(levelQ A v:ℝ))^2)⁻¹ n)≤_
  rw [levelQ_cast]
  have hD : 0≤((P.ε*level A v)^2)⁻¹ := by positivity
  have hb := majorant_summable_bound zero_le_one hD
  have hs := Summable.sum_le_tsum I (fun n _ => majorant_nonneg zero_le_one hD n) hb.1
  exact hs.trans (by simpa using hb.2)

theorem lowExpression_mass_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) :
    expressionBound (lowExpression A hN P χ t I)≤P.ρ^(t-1)*lowConstant A P := by
  rw [lowExpression,expressionBound_sumExpressions,lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [expressionBound_scale,amplitude_norm A χ hχ]
  have hh := mul_le_mul_of_nonneg_left (lowPartExpression_mass_le A hN P ht v I) (abs_nonneg (scalar A v:ℝ))
  convert hh using 1
  ring

theorem terminalExpression_mass_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) :
    expressionBound (terminalExpression A hN P χ ht I)≤terminalConstant A P := by
  rw [terminalExpression,expressionBound_sumExpressions]
  apply Finset.sum_le_sum
  intro v _
  rw [expressionBound_scale,amplitude_norm A χ hχ]
  exact mul_le_mul_of_nonneg_left (terminalPartExpression_mass_le A hN P ht v I) (abs_nonneg _)

theorem half_geometric_sum_le_two (n : ℕ) :
    (∑ j∈Finset.range n, (1/2:ℝ)^j)≤2 := by
  have hh : (∑ j∈Finset.range n, (1/2:ℝ)^j)=2*(1-(1/2:ℝ)^n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [hh]
  have hp : 0≤(1/2:ℝ)^n := by positivity
  linarith

/-- The actual scaled raw reconstruction has coefficient mass at most one,
uniformly in sector, cutoffs, and Neumann depth. -/
theorem scaledCutCountExpression_mass_le_one (hN : 0<N) (P : Parameters A)
    (e : Sector N) (Y : ℝ) (j J : ℕ) :
    expressionBound (scaledCutCountExpression A hN P e Y j J)≤1 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let I := Finset.Icc (-(J:ℤ)) J
  have hlow : expressionBound (lowExpression A hN P' (multiplier e) (P'.s+3) I)≤1/2 :=
    (lowExpression_mass_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) (by omega) I).trans
      (AsymptoticReconstructedCount.parameters_bound A P).le
  have ht := terminalExpression_mass_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) (by omega : 2≤P'.s+3) I
  have hg : (∑ l∈Finset.range j, expressionBound (lowExpression A hN P' (multiplier e) (P'.s+3) I)^l)≤2 := by
    apply le_trans _ (half_geometric_sum_le_two j)
    exact Finset.sum_le_sum (fun l _ => pow_le_pow_left₀ (expressionBound_nonneg _) hlow l)
  have hb : expressionBound (cutFullExpression A hN P' (multiplier e) Y j I)≤countReconstructionBound A P := by
    rw [expressionBound_cutFullExpression,expressionBound_fullExpression]
    change 1+_≤1+2*terminalConstant A P'
    exact add_le_add le_rfl (mul_le_mul hg ht (expressionBound_nonneg _) (by norm_num))
  rw [scaledCutCountExpression,expressionBound_scale]
  have hC := zero_lt_one.trans_le (countReconstructionBound_one_le A P)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')

/-- Exact raw branch count, with every cutoff and Neumann depth explicit. -/
def rawReconstructionLength (j J : ℕ) : ℕ :=
  let M := Fintype.card (Index A)*(2*J+1)
  1+(∑ l∈Finset.range j, M^l)*M

theorem scaledCutCountExpression_length (hN : 0<N) (P : Parameters A)
    (e : Sector N) (Y : ℝ) (j J : ℕ) :
    (scaledCutCountExpression A hN P e Y j J).length=rawReconstructionLength A j J := by
  have hI : (Finset.Icc (-(J:ℤ)) J).card=2*J+1 := by
    rw [Int.card_Icc]
    omega
  simp [scaledCutCountExpression,scaleExpression,cutFullExpression,length_composeExpression,
    fullExpression,length_neumannExpression,lowExpression,terminalExpression,length_sumExpressions,
    lowPartExpression,terminalPartExpression,ofFinset,hI,rawReconstructionLength,Nat.add_comm]

#print axioms scaledCutCountExpression_mass_le_one
#print axioms scaledCutCountExpression_length

end QuantitativeHolomorphic
