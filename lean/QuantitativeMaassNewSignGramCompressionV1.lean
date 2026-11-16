module

public import QuantitativeMaassNewSignGramPathsV1
public import QuantitativeMaassCutoffWordGrowthV1
public import QuantitativeMaassCutoffWordCountV1
public import QuantitativeMaassFullBandWideCountV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass
open scoped Topology

namespace QuantitativeMaass
open Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

/-- A fixed-band compression of n actual normalized new/sign weighted Gram factors has explicit
error at most C_N G 8^n t/L when its outer band stays below t/4. -/
theorem newSignGram_fixed_count_energy (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ),
      ∀ (t L B : ℝ),6≤t → 1≤L → ∀ n : ℕ,cutoffWordRadius L n≤t/4 →
      cutoffWordRadius L n≤B →
      ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)),
      finiteSourceEnergy v (newSignGramAmbientPath S hδ hν χ t L n-newSignGramFixedPath S hδ hν χ t L B n)≤
        256*C*(4*quotientWeightBound δ*(2*ν:ℝ))^2*(8:ℝ)^n*t/L := by
  obtain ⟨C,hC,hcount⟩ := fullBand_wide_finrank_bound N hN
  refine ⟨C,hC,?_⟩
  intro S δ hδ ν hν χ t L B ht hL n hn hB ι _ v
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
  have he := newSignGram_fixed_energy S hδ hν χ t L B hL0 v n hB hsep
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
  apply (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤4*2^n)).trans
  have hc := mul_le_mul_of_nonneg_left (cutoffWordRadius_cost hL n)
    (show 0≤64*G*C*t/L^2 by positivity)
  have hid : (64*G*C*t/L^2)*(4*(8:ℝ)^n*L)=256*C*G*(8:ℝ)^n*t/L := by
    field_simp
    ring
  rw [hid] at hc
  change _ ≤256*C*G*(8:ℝ)^n*t/L
  calc
    _ = (64*G*C*t/L^2)*((2:ℝ)^n*(n:ℝ)*cutoffWordRadius L n) := by ring
    _ ≤ _ := hc

/-- Compression to one fixed outer band of actual normalized new/sign weighted Gram words remains negligible for
growing word length and every prescribed exponential error weight. The
conclusion is uniform in the source basis. -/
theorem weighted_newSignGram_fixed_compression (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (a W : ℝ) (ha : 0≤a)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,0<D ∧ ∃ M : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*fourthRootScale t)*M t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ n : ℕ,(n:ℝ)≤a*fourthRootScale t →
        ∀ B : ℝ,cutoffWordRadius (Real.exp (D*fourthRootScale t)) n≤B →
        ∀ {ι : Type*} [Fintype ι]
          (v : OrthonormalBasis ι ℂ (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0)),
        finiteSourceEnergy v
          (newSignGramAmbientPath S hδ hν χ t (Real.exp (D*fourthRootScale t)) n-
            newSignGramFixedPath S hδ hν χ t (Real.exp (D*fourthRootScale t)) B n)≤M t := by
  obtain ⟨C,hC,hcount⟩ := newSignGram_fixed_count_energy N hN
  let G : ℝ := (4*quotientWeightBound δ*(2*ν:ℝ))^2
  have hG : 0≤G := sq_nonneg _
  let p := a*Real.log 8
  have hp : 0≤p := mul_nonneg ha (Real.log_nonneg (by norm_num))
  let D := |W|+p+1
  have hD : 0<D := by dsimp only [D]; linarith [abs_nonneg W]
  let K := 256*C*G
  have hK : 0≤K := by dsimp only [K]; positivity
  let M := fun t => K*t*Real.exp ((p-D)*fourthRootScale t)
  refine ⟨D,hD,M,?_,?_⟩
  · have hlim := (fourthRoot_exponential_div_width ε hε hproduct).const_mul K
    simp only [mul_zero] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
      dsimp only [M]
      positivity
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
      have hroot : 0≤fourthRootScale t := Real.sqrt_nonneg _
      have he : W*fourthRootScale t+(p-D)*fourthRootScale t≤-fourthRootScale t := by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self W) hroot
        dsimp only [D]
        nlinarith only [hh]
      have hid : Real.exp (W*fourthRootScale t)*M t/(t*ε t)=
          K*(Real.exp (W*fourthRootScale t+(p-D)*fourthRootScale t)/ε t) := by
        dsimp only [M]
        rw [Real.exp_add]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) heps.le) hK
  · filter_upwards [cutoffWordRadius_uniform_quarter a D ha hD.le,
      eventually_ge_atTop (6:ℝ)] with t ht ht6
    intro n hn B hB ι _ v
    have hL : 1≤Real.exp (D*fourthRootScale t) :=
      Real.one_le_exp (mul_nonneg hD.le (Real.sqrt_nonneg _))
    have hh := hcount S hδ hν χ t (Real.exp (D*fourthRootScale t)) B ht6 hL n (ht n hn) hB v
    apply hh.trans
    have he := eight_pow_le_root_exponential a t n hn
    calc
      _ ≤ K*Real.exp (p*fourthRootScale t)*t/Real.exp (D*fourthRootScale t) := by
        apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) (by linarith)
      _ = M t := by
        dsimp only [M]
        rw [sub_mul,Real.exp_sub]
        ring

#print axioms newSignGram_fixed_count_energy
#print axioms weighted_newSignGram_fixed_compression

end QuantitativeMaass
