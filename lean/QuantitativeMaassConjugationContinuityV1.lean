module

public import QuantitativeMaassBoundedConjugationV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem bandPropagation_sub (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (hS : HasBandPropagation μ l hl S J) :
    HasBandPropagation μ l hl (T-S) J := by
  intro n m hnm f
  simp only [sub_apply,map_sub,hT n m hnm f,hS n m hnm f,sub_self]

/-- A fixed propagation radius is preserved by operator-norm limits. -/
theorem bandPropagation_limit {ι : Type*} {L : Filter ι} [NeBot L]
    (T : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : ∀ i,HasBandPropagation μ l hl (T i) J) (hlim : Tendsto T L (𝓝 S)) :
    HasBandPropagation μ l hl S J := by
  intro n m hnm f
  have hh := (projection μ l hl n).continuous.tendsto _ |>.comp
    (((ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) (projection μ l hl m f)).continuous.tendsto _).comp hlim)
  have he : (fun i => projection μ l hl n (T i (projection μ l hl m f)))=fun _ => 0 :=
    funext (fun i => hT i n m hnm f)
  change Tendsto (fun i => projection μ l hl n (T i (projection μ l hl m f))) L
    (𝓝 (projection μ l hl n (S (projection μ l hl m f)))) at hh
  rw [he] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

theorem conjugationLinear_sub (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (hS : HasBandPropagation μ l hl S J)
    (f : finiteBandSpace μ l hl) :
    conjugationLinear μ l hl (T-S) J (bandPropagation_sub μ l hl T S J hT hS) f=
      conjugationLinear μ l hl T J hT f-conjugationLinear μ l hl S J hS f := by
  have h (g : finiteBandSpace μ l hl) :
      finitePropagationMap μ l hl (T-S) J (bandPropagation_sub μ l hl T S J hT hS) g=
        finitePropagationMap μ l hl T J hT g-finitePropagationMap μ l hl S J hS g := by
    apply Subtype.ext
    rfl
  simp only [conjugationLinear,LinearMap.comp_apply,h,map_sub]

/-- The bounded weight conjugation is linear on each fixed-propagation class. -/
theorem boundedConjugation_sub (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (hS : HasBandPropagation μ l hl S J) :
    boundedConjugation μ l hl (T-S) J (bandPropagation_sub μ l hl T S J hT hS)=
      boundedConjugation μ l hl T J hT-boundedConjugation μ l hl S J hS := by
  apply boundedConjugation_unique
  intro f
  simp only [sub_apply,boundedConjugation_on_finite]
  exact (conjugationLinear_sub μ l hl T S J hT hS f).symm

theorem boundedConjugation_sub_norm (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (hS : HasBandPropagation μ l hl S J) :
    ‖boundedConjugation μ l hl T J hT-boundedConjugation μ l hl S J hS‖≤
      ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T-S‖ := by
  rw [←boundedConjugation_sub]
  exact boundedConjugation_norm_bound μ l hl (T-S) J _

/-- Uniform finite propagation makes the unbounded weight conjugation
continuous in the bounded operator norm. -/
theorem boundedConjugation_tendsto {ι : Type*} {L : Filter ι}
    (T : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : ∀ i,HasBandPropagation μ l hl (T i) J) (hS : HasBandPropagation μ l hl S J)
    (hlim : Tendsto T L (𝓝 S)) :
    Tendsto (fun i => boundedConjugation μ l hl (T i) J (hT i)) L
      (𝓝 (boundedConjugation μ l hl S J hS)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul
    (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))
  simp only [mul_zero] at hh
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i =>
    boundedConjugation_sub_norm μ l hl (T i) S J (hT i) hS) hh

#print axioms bandPropagation_sub
#print axioms bandPropagation_limit
#print axioms boundedConjugation_sub
#print axioms boundedConjugation_sub_norm
#print axioms boundedConjugation_tendsto

end QuantitativeMaass.LogBands
