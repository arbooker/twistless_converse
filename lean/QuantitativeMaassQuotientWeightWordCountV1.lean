module

public import QuantitativeMaassQuotientWeightWordEnergyV1
public import QuantitativeMaassCutoffWordCountV1
public import QuantitativeMaassFullBandWideCountV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand cutoffWordRadius_mono cutoffWordRadius_cost cutoffWordRadius_eq)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

/-- A word of n actual normalized weighted Gram operators has an explicit actual compression
error at most C_N G 8^n t/L when its outer band stays below t/4. -/
theorem quotientWeight_word_count_energy (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν),
      ∀ (t L : ℝ),6≤t → 1≤L → ∀ n : ℕ,cutoffWordRadius L n≤t/4 →
      ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)),
      finiteSourceEnergy v (quotientWeightAmbientPath S hδ hν t L n-quotientWeightBandPathAmbient S hδ hν t L n)≤
        64*C*(4*quotientWeightBound δ*(2*ν:ℝ))^2*(8:ℝ)^n*t/L := by
  obtain ⟨C,hC,hcount⟩ := fullBand_wide_finrank_bound N hN
  refine ⟨C,hC,?_⟩
  intro S δ hδ ν hν t L ht hL n hn ι _ v
  let G : ℝ := (4*quotientWeightBound δ*(2*ν:ℝ))^2
  have hG : 0≤G := sq_nonneg _
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have ht0 : 0≤t := by linarith
  have hR (j : ℕ) : 1≤cutoffWordRadius L j := by
    rw [cutoffWordRadius_eq]
    linarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ)≤j) (show 0≤L+2 by linarith)]
  have hsep (j : ℕ) (hj : j<n) : cutoffWordRadius L j+L+2≤t := by
    have hh := cutoffWordRadius_mono hL0.le (Nat.succ_le_of_lt hj)
    change cutoffWordRadius L j+L+2≤cutoffWordRadius L n at hh
    linarith
  have he := quotientWeight_word_energy S hδ hν t L hL0 v n hsep
  have hterm (j : ℕ) (hj : j∈Finset.range n) :
      16*G*(Module.finrank ℂ (cutoffWordBand S t L j):ℝ)/L^2≤
        (16*G*C*t/L^2)*cutoffWordRadius L n := by
    have hmono := cutoffWordRadius_mono hL0.le (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hd := (hcount S t (cutoffWordRadius L j) ht (hR j) (hmono.trans hn)).trans
      (mul_le_mul_of_nonneg_left hmono (mul_nonneg hC.le ht0))
    calc
      _ ≤ 16*G*(C*t*cutoffWordRadius L n)/L^2 := by
        have hm := mul_le_mul (le_refl G) hd (Nat.cast_nonneg _) hG
        have hp := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤16)
        simpa only [mul_assoc] using div_le_div_of_nonneg_right hp (sq_nonneg L)
      _ = _ := by ring
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤2^n)).trans
  have hc := mul_le_mul_of_nonneg_left (cutoffWordRadius_cost hL n)
    (show 0≤16*G*C*t/L^2 by positivity)
  have hid : (16*G*C*t/L^2)*(4*(8:ℝ)^n*L)=64*C*G*(8:ℝ)^n*t/L := by
    field_simp
    ring
  rw [hid] at hc
  change _ ≤64*C*G*(8:ℝ)^n*t/L
  nlinarith only [hc]

#print axioms quotientWeight_word_count_energy

end QuantitativeMaass
