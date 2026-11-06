module

public import QuantitativeHolomorphicGrowingTraceRateV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open AsymptoticUnweightedKernel

def periodizationCutoff (Y H : ℝ) : ℕ := Nat.ceil (2*compactBaseBound Y H 1)

def periodizationSet (Y H : ℝ) : Finset ℤ :=
  Finset.Icc (-(periodizationCutoff Y H:ℤ)) (periodizationCutoff Y H)

theorem periodizationSet_far (Y H : ℝ) :
    ∀ n : ℤ,n∉periodizationSet Y H →2*compactBaseBound Y H 1≤1+|(n:ℝ)| :=
  periodization_far_of_cutoff _ (Nat.le_ceil _)

theorem periodizationSet_card_le {Y H M : ℝ} (hY : 0<Y) (hH : 0≤H)
    (hM : 1≤M) (hHM : H≤M) (hYM : Y⁻¹≤M) :
    ((periodizationSet Y H).card:ℝ)≤19*M^2 := by
  have hbase0 : 0≤compactBaseBound Y H 1 := by unfold compactBaseBound; positivity
  have hbaseEq : compactBaseBound Y H 1=2*H*(1+Y⁻¹) := by
    unfold compactBaseBound
    congr 2
    field_simp
    norm_num
  have hbase : compactBaseBound Y H 1≤4*M^2 := by
    rw [hbaseEq]
    calc
      _ ≤2*M*(1+M) := by gcongr
      _ ≤4*M^2 := by nlinarith
  have hceil : (periodizationCutoff Y H:ℝ)≤8*M^2+1 := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0≤2*compactBaseBound Y H 1)
    dsimp [periodizationCutoff]
    linarith
  have hcard : (periodizationSet Y H).card=2*periodizationCutoff Y H+1 := by
    unfold periodizationSet
    rw [Int.card_Icc]
    omega
  rw [hcard]
  push_cast
  nlinarith

theorem growing_periodization_card {Y H K s : ℝ} (hY : 0<Y) (hH : 0≤H)
    (hK : 0≤K) (hs : 1≤s)
    (hHM : H≤Real.exp (Real.exp (K*s^2)))
    (hYM : Y⁻¹≤Real.exp (Real.exp (K*s^2))) :
    ((periodizationSet Y H).card:ℝ)≤Real.exp (Real.exp ((K+21)*s^2)) := by
  apply (periodizationSet_card_le hY hH (Real.one_le_exp (Real.exp_nonneg _)) hHM hYM).trans
  convert polynomial_double_exp_le 2 (c:=19) (by norm_num) hK hs using 1
  congr 2
  ring

#print axioms growing_periodization_card
#print axioms periodizationSet_far

end QuantitativeHolomorphic.Schedule
