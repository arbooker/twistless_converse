module

public import QuantitativeArithmeticRetainedCountUpperV1
public import QuantitativeEulerEndpointRadicalCountBoundaryV1
public import QuantitativeArithmeticAugmentedSpanningV1
public import QuantitativeEulerEndpointLevelOneCountV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRadicalCountTheorem
open Filter Asymptotics FinitenessOriginalInput AsymptoticSectorComparison
open QuantitativeConcreteGoals QuantitativeHolomorphic
open QuantitativeArithmeticRetainedIteration QuantitativeEulerEndpointRadicalBoundary

/-- The literal Euler-count excess over the actual classical total-newspace
dimension is O_N(k/loglog(2k)), through even weights, when rad(N)>sqrt(N).
All arithmetic, prime-block, physical, regular-trace, and dimension inputs
are supplied by checked theorems; no quantitative count hypothesis remains. -/
theorem radical_level_endpoint (N : ℕ) (hN : 0<N)
    (hrad : N<(∏p∈N.primeFactors,p)^2) :
    HolomorphicCountClaim N hN 1 := by
  by_cases h1 : N=1
  · subst N
    exact QuantitativeEulerEndpointLevelOne.level_one_endpoint
  have hN2 : 2≤N := by have hpos := hN; omega
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨Q,hQ,hNQ,⟨A⟩⟩ := QuantitativeArithmeticAugmentedSpanning.radical_certificate hN hrad
  obtain ⟨P⟩ := QuantitativeArithmeticRetainedGlobalHeight.parameters_exist hN hQ A
  obtain ⟨B,hB,hupper⟩ := actual_count_endpoint_upper A P
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => (Nat.dvd_of_mem_primeFactors hp).trans hNQ)
    (fun _ hp => Nat.dvd_of_mem_primeFactors hp) hN2
  obtain ⟨C,hsqueeze⟩ := literal_count_squeeze N hN hrad
  apply (isBigO_shiftedRemainderScale_iff inf_le_left (holomorphicError N hN) 1).mp
  apply IsBigO.of_bound (B+abs C)
  have hL : Tendsto (fun k : ℕ => Real.log (Real.log (k:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hupper,hsqueeze,(hL.eventually (eventually_ge_atTop 1)).filter_mono inf_le_left,
    (eventually_ge_atTop 2).filter_mono inf_le_left] with k hup hsq hlog hk
  have hk2 : (2:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hlogk : 0<Real.log (k:ℝ) := Real.log_pos (by linarith)
  have hLp : 0<Real.log (Real.log (k:ℝ)) := by linarith
  have hone : 1≤(k:ℝ)/Real.log (Real.log (k:ℝ)) := by
    apply (le_div_iff₀ hLp).mpr
    linarith [Real.log_le_sub_one_of_pos hk0,Real.log_le_sub_one_of_pos hlogk]
  have hCb : C≤abs C*((k:ℝ)/Real.log (Real.log (k:ℝ))) := by
    apply (le_abs_self C).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (abs_nonneg C)
  have herr : holomorphicError N hN k≤B*(k:ℝ)/Real.log (Real.log (k:ℝ))+C := by
    linarith only [hup,hsq.2]
  have hbound : holomorphicError N hN k≤(B+abs C)*((k:ℝ)/Real.log (Real.log (k:ℝ))) := by
    calc
      _ ≤ B*(k:ℝ)/Real.log (Real.log (k:ℝ))+C := herr
      _ ≤ B*(k:ℝ)/Real.log (Real.log (k:ℝ))+abs C*((k:ℝ)/Real.log (Real.log (k:ℝ))) := add_le_add le_rfl hCb
      _ = _ := by ring
  have he : remainderScale 1 (k:ℝ)=(k:ℝ)/Real.log (Real.log (k:ℝ)) := by
    simp only [remainderScale,Real.rpow_neg_one,div_eq_mul_inv]
  rw [Real.norm_eq_abs,abs_of_nonneg hsq.1,he,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hk0.le hLp.le)]
  exact hbound

/-- Expanded form of the endpoint, naming the original set and actual newspace. -/
theorem literal_endpoint (N : ℕ) (hN : 0<N)
    (hrad : N<(∏p∈N.primeFactors,p)^2) :
    (fun k : ℕ => ((S N k).ncard:ℝ)-
      (Module.finrank ℂ (AsymptoticClassicalCusp.newSpace N hN (k:ℤ)):ℝ))
      =O[evenWeights] (fun k : ℕ => (k:ℝ)/Real.log (Real.log (2*(k:ℝ)))) := by
  have hh := radical_level_endpoint N hN hrad
  unfold HolomorphicCountClaim holomorphicError at hh
  simpa only [shiftedRemainderScale,Real.rpow_neg_one,div_eq_mul_inv] using hh

#print axioms radical_level_endpoint
#print axioms literal_endpoint
end QuantitativeArithmeticRadicalCountTheorem
