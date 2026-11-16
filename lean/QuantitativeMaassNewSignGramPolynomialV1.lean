module

public import QuantitativeMaassNewSignGramCompressionV1
public import QuantitativeMaassNewtonSourceCostV1
public import QuantitativeMaassSourcePolynomialEnergyV1
public import QuantitativeHolomorphicNewtonCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass QuantitativeHolomorphic
open scoped Topology

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem newSignGramAmbientPath_power {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L : ℝ) (n : ℕ) :
    newSignGramAmbientPath S hδ hν χ t L n=
      ((newSignWeightedGram N hN hδ hν χ)^n).comp (cutoffWordBand S t L 0).subtypeL := by
  induction n with
  | zero => rfl
  | succ n ih => rw [newSignGramAmbientPath,ih,pow_succ']; rfl

theorem newSignGramFixedPath_power {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (n : ℕ) :
    newSignGramFixedPath S hδ hν χ t L B n=
      (((quotientWeightOuterProjection S t B).comp
        (newSignWeightedGram N hN hδ hν χ))^n).comp (cutoffWordBand S t L 0).subtypeL := by
  induction n with
  | zero => rfl
  | succ n ih => rw [newSignGramFixedPath,ih,pow_succ']; rfl

/-- Exact polynomial expansion on the original unit input band. -/
theorem newSignGram_polynomial_difference {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ) (t L B : ℝ) (p : Polynomial ℝ) :
    (Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp
        (cutoffWordBand S t L 0).subtypeL-
      (Polynomial.aeval ((quotientWeightOuterProjection S t B).comp
        (newSignWeightedGram N hN hδ hν χ)) p).comp (cutoffWordBand S t L 0).subtypeL=
      (∑ j∈p.support,p.coeff j • newSignGramAmbientPath S hδ hν χ t L j)-
        (∑ j∈p.support,p.coeff j • newSignGramFixedPath S hδ hν χ t L B j) := by
  simp only [polynomial_aeval_sum,ContinuousLinearMap.finsetSum_comp,ContinuousLinearMap.smul_comp,
    newSignGramAmbientPath_power,newSignGramFixedPath_power]

/-- Actual polynomial compression, with explicit degree and coefficient
costs and the original finite input band. -/
theorem newSignGram_polynomial_energy (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ),
      ∀ (t L B : ℝ),6≤t → 1≤L → ∀ m : ℕ,cutoffWordRadius L m≤t/4 →
      cutoffWordRadius L m≤B → ∀ p : Polynomial ℝ,p.natDegree≤m →
      ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)),
      finiteSourceEnergy v
        ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp
          (cutoffWordBand S t L 0).subtypeL-
        (Polynomial.aeval ((quotientWeightOuterProjection S t B).comp
          (newSignWeightedGram N hN hδ hν χ)) p).comp (cutoffWordBand S t L 0).subtypeL)≤
        ((p.support.card:ℝ)*∑ j∈p.support,(p.coeff j)^2)*
          (256*C*(4*quotientWeightBound δ*(2*ν:ℝ))^2*(8:ℝ)^m*t/L) := by
  obtain ⟨C,hC,hbound⟩ := newSignGram_fixed_count_energy N hN
  refine ⟨C,hC,?_⟩
  intro S δ hδ ν hν χ t L B ht hL m hm hB p hp ι _ v
  rw [newSignGram_polynomial_difference]
  apply finiteSourceEnergy_combination_difference
  intro j hj
  have hjm : j≤m := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hp
  have hR := Weighted.cutoffWordRadius_mono (zero_le_one.trans hL) hjm
  have hh := hbound S hδ hν χ t L B ht hL j (hR.trans hm) (hR.trans hB) v
  apply hh.trans
  have hpow : (8:ℝ)^j≤8^m := pow_le_pow_right₀ (by norm_num) hjm
  apply div_le_div_of_nonneg_right _ (zero_le_one.trans hL)
  apply mul_le_mul_of_nonneg_right _ (by linarith : 0≤t)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Polynomial degree and coefficient growth are absorbed by the proved
weighted fixed-band leakage estimate. Both operators are the literal actual
Gram and its fixed outer-band compression. -/
theorem weighted_newSignGram_polynomial_compression (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (a c W : ℝ) (ha : 0≤a)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,0<D ∧ ∃ F : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*fourthRootScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ p : Polynomial ℝ,(p.natDegree:ℝ)≤a*fourthRootScale t →
        (p.support.card:ℝ)*(∑ j∈p.support,(p.coeff j)^2)≤Real.exp (c*fourthRootScale t) →
        ∀ B : ℝ,cutoffWordRadius (Real.exp (D*fourthRootScale t)) p.natDegree≤B →
        ∀ {ι : Type*} [Fintype ι]
          (v : OrthonormalBasis ι ℂ (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0)),
        finiteSourceEnergy v
          ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) p).comp
            (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0).subtypeL-
          (Polynomial.aeval ((quotientWeightOuterProjection S t B).comp
            (newSignWeightedGram N hN hδ hν χ)) p).comp
              (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0).subtypeL)≤F t := by
  obtain ⟨D,hD,M,hM,hbound⟩ := weighted_newSignGram_fixed_compression N hN S hδ hν χ a (W+c)
    ha ε hε hproduct
  let F := fun t => Real.exp (c*fourthRootScale t)*|M t|
  refine ⟨D,hD,F,?_,?_⟩
  · have hh := hM.abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    dsimp only [F]
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht he),add_mul,Real.exp_add]
    ring
  · filter_upwards [hbound] with t ht
    intro p hp hc B hB ι _ v
    rw [newSignGram_polynomial_difference]
    have hjbound (j : ℕ) (hj : j∈p.support) :
        finiteSourceEnergy v
          (newSignGramAmbientPath S hδ hν χ t (Real.exp (D*fourthRootScale t)) j-
            newSignGramFixedPath S hδ hν χ t (Real.exp (D*fourthRootScale t)) B j)≤|M t| := by
      have hjp := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
      have hjr : (j:ℝ)≤a*fourthRootScale t := (by exact_mod_cast hjp : (j:ℝ)≤p.natDegree).trans hp
      have hRB := (Weighted.cutoffWordRadius_mono (Real.exp_pos _).le hjp).trans hB
      exact (ht j hjr B hRB v).trans (le_abs_self _)
    exact (finiteSourceEnergy_combination_difference v p.support p.coeff _ _ |M t| hjbound).trans
      (mul_le_mul_of_nonneg_right hc (abs_nonneg _))

/-- The scheduled Newton polynomial of the literal normalized Gram can be
computed in one fixed outer band with negligible weighted energy error.
Its degree and coefficient bounds are proved, not assumed. -/
theorem weighted_newSignGram_newton_compression (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (W : ℝ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,0<D ∧ ∃ F : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*fourthRootScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,
        ∀ B : ℝ,cutoffWordRadius (Real.exp (D*fourthRootScale t)) (inverseSqrtPolynomial (bandNewtonDepth t)).natDegree≤B →
        ∀ {ι : Type*} [Fintype ι]
          (v : OrthonormalBasis ι ℂ (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0)),
        finiteSourceEnergy v
          ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) (inverseSqrtPolynomial (bandNewtonDepth t))).comp
            (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0).subtypeL-
          (Polynomial.aeval ((quotientWeightOuterProjection S t B).comp
            (newSignWeightedGram N hN hδ hν χ)) (inverseSqrtPolynomial (bandNewtonDepth t))).comp
              (cutoffWordBand S t (Real.exp (D*fourthRootScale t)) 0).subtypeL)≤F t := by
  obtain ⟨D,hD,F,hF,hbound⟩ := weighted_newSignGram_polynomial_compression N hN S hδ hν χ
    2 (2*Real.log 48) W (by norm_num) ε hε hproduct
  refine ⟨D,hD,F,hF,?_⟩
  filter_upwards [hbound,bandNewtonDepth_source_cost] with t ht hc
  exact ht (inverseSqrtPolynomial (bandNewtonDepth t)) hc.1 hc.2

#print axioms newSignGramAmbientPath_power
#print axioms newSignGramFixedPath_power
#print axioms newSignGram_polynomial_difference
#print axioms newSignGram_polynomial_energy
#print axioms weighted_newSignGram_polynomial_compression
#print axioms weighted_newSignGram_newton_compression

end QuantitativeMaass
