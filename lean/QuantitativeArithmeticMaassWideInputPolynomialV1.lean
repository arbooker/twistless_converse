module

public import QuantitativeArithmeticMaassWideInputGramV1
public import QuantitativeMaassFullBandWideCountV1
public import QuantitativeMaassSourcePolynomialEnergyV1
public import QuantitativeHolomorphicNewtonCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open QuantitativeNinaMaass QuantitativeHolomorphic ContinuousLinearMap
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem radius_eq (B L : ℝ) (n : ℕ) : radius B L n=B+(n:ℝ)*(L+2) := by
  induction n with
  | zero => simp [radius]
  | succ n ih => rw [radius,ih]; push_cast; ring

/-- All words of length at most m admit a common error bound. The input
band can be wide; its radius B is retained explicitly. -/
theorem fixed_count_energy (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ)
      {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
      (t B L Bouter : ℝ),6≤t → 1≤B → 0<L → ∀ m : ℕ,
      radius B L m≤t/4 → radius B L m≤Bouter → ∀ n : ℕ,n≤m →
      ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))),
      finiteSourceEnergy v (ambientPath S hδ hν χ t B n-fixedPath S hδ hν χ t B Bouter n) ≤
        64*C*(4*quotientWeightBound δ*(2*ν:ℝ))^2*(2:ℝ)^m*(m:ℝ)*t*radius B L m/L^2 := by
  obtain ⟨C,hC,hcount⟩ := fullBand_wide_finrank_bound N hN
  refine ⟨C,hC,?_⟩
  intro S δ hδ ν hν χ t B L Bouter ht hB hL m hm hout n hn ι _ v
  let G : ℝ := (4*quotientWeightBound δ*(2*ν:ℝ))^2
  have hG : 0≤G := sq_nonneg _
  have ht0 : 0≤t := by linarith
  have hr0 (j : ℕ) : 1≤radius B L j := by
    have hh := radius_mono B L hL.le (Nat.zero_le j)
    exact hB.trans hh
  have hsep (j : ℕ) (hj : j<n) : radius B L j+L+2≤t := by
    have hh := radius_mono B L hL.le ((Nat.succ_le_of_lt hj).trans hn)
    change radius B L j+L+2≤radius B L m at hh
    linarith
  have he := fixed_energy S hδ hν χ t B L v Bouter n hL
    ((radius_mono B L hL.le hn).trans hout) hsep
  have hterm (j : ℕ) (hj : j∈Finset.range n) :
      16*G*(Module.finrank ℂ (S.band (t-radius B L j) (t+radius B L j)):ℝ)/L^2 ≤
        16*G*(C*t*radius B L m)/L^2 := by
    have hmono := radius_mono B L hL.le ((Nat.le_of_lt (Finset.mem_range.mp hj)).trans hn)
    have hd := (hcount S t (radius B L j) ht (hr0 j) (hmono.trans hm)).trans
      (mul_le_mul_of_nonneg_left hmono (mul_nonneg hC.le ht0))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by positivity)) (sq_nonneg L)
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤4*2^n)).trans
  have hpow : (2:ℝ)^n≤2^m := pow_le_pow_right₀ (by norm_num) hn
  have hnm : (n:ℝ)≤m := by exact_mod_cast hn
  have hc : 0≤16*G*(C*t*radius B L m)/L^2 := by
    have := hr0 m
    positivity
  calc
    _ ≤ (4*(2:ℝ)^m)*((m:ℝ)*(16*G*(C*t*radius B L m)/L^2)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num))
        (mul_le_mul_of_nonneg_right hnm hc) (mul_nonneg (Nat.cast_nonneg _) hc) (by positivity)
    _ = _ := by dsimp only [G]; ring

variable {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
  (t B : ℝ)

theorem ambientPath_power (n : ℕ) : ambientPath S hδ hν χ t B n=
    ((newSignWeightedGram N hN hδ hν χ)^n).comp (S.band (t-B) (t+B)).subtypeL := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ambientPath,ih,pow_succ']; rfl

theorem fixedPath_power (Bouter : ℝ) (n : ℕ) : fixedPath S hδ hν χ t B Bouter n=
    (((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ))^n).comp
      (S.band (t-B) (t+B)).subtypeL := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fixedPath,ih,pow_succ']; rfl

/-- The literal polynomial in the Gram can be evaluated in one fixed outer
band, with a quantified energy error for every finite input band. -/
theorem polynomial_energy :
    ∃ C : ℝ,0<C ∧ ∀ (L Bouter : ℝ),6≤t → 1≤B → 0<L → ∀ m : ℕ,
      radius B L m≤t/4 → radius B L m≤Bouter → ∀ p : Polynomial ℝ,p.natDegree≤m →
      ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))),
      finiteSourceEnergy v
        ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp (S.band (t-B) (t+B)).subtypeL-
        (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ)) p).comp
          (S.band (t-B) (t+B)).subtypeL) ≤
        ((p.support.card:ℝ)*∑ j∈p.support,(p.coeff j)^2)*
          (64*C*(4*quotientWeightBound δ*(2*ν:ℝ))^2*(2:ℝ)^m*(m:ℝ)*t*radius B L m/L^2) := by
  obtain ⟨C,hC,hbound⟩ := fixed_count_energy N hN
  refine ⟨C,hC,?_⟩
  intro L Bouter ht hB hL m hm hout p hp ι _ v
  have hid :
      (Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp (S.band (t-B) (t+B)).subtypeL-
      (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ)) p).comp
        (S.band (t-B) (t+B)).subtypeL=
      (∑ j∈p.support,p.coeff j • ambientPath S hδ hν χ t B j)-
        (∑ j∈p.support,p.coeff j • fixedPath S hδ hν χ t B Bouter j) := by
    simp only [polynomial_aeval_sum,finsetSum_comp,smul_comp,ambientPath_power,fixedPath_power]
  rw [hid]
  apply finiteSourceEnergy_combination_difference
  intro j hj
  exact hbound S hδ hν χ t B L Bouter ht hB hL m hm hout j
    ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hp) v

#print axioms fixed_count_energy
#print axioms polynomial_energy
end QuantitativeMaass.WideInput
