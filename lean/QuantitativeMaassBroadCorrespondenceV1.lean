module

public import QuantitativeMaassBroadTranslatedDecayV1
public import QuantitativeMaassProfileHeightBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

def broadTranslatedSquare (L : ℝ) (hL : 0<L) (t τ : ℝ) : ℝ → ℂ :=
  evenTimeTranslate τ (timeConvolution (broadTimeSchwartz L hL t) (broadTimeSchwartz L hL t))

theorem broadTranslatedSquare_regular (L : ℝ) (hL : 0<L) (t τ : ℝ) :
    ContDiff ℝ ∞ (broadTranslatedSquare L hL t τ) ∧
    Function.Even (broadTranslatedSquare L hL t τ) ∧
    HasCompactSupport (broadTranslatedSquare L hL t τ) :=
  ⟨evenTimeTranslate_smooth _ _ ((timeConvolution _ _).smooth ⊤),
    evenTimeTranslate_even _ _ (timeConvolution_even _ _
      (broadTimeWeight_even L t) (broadTimeWeight_even L t)),
    evenTimeTranslate_compact _ _ (timeConvolution_compact _ _
      (broadTimeWeight_compact L hL t) (broadTimeWeight_compact L hL t))⟩

theorem broadTranslatedSquare_support (L : ℝ) (hL : 1≤L) (t τ : ℝ) :
    Function.support (broadTranslatedSquare L (lt_of_lt_of_le zero_lt_one hL) t τ) ⊆
      Icc (-(2+|τ|)) (2+|τ|) := by
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hs : Function.support (broadTimeSchwartz L hLp t) ⊆ Icc (-1:ℝ) 1 := by
    apply (broadTimeWeight_support L hLp t).trans
    have hd : 1/L≤1 := (div_le_one hLp).mpr hL
    exact Icc_subset_Icc (by linarith) hd
  have hsq := timeConvolution_support _ _ 1 1 hs hs
  norm_num only at hsq
  exact evenTimeTranslate_support τ 2 _ hsq

def broadTranslatedProfile (L : ℝ) (hL : 0<L) (t τ : ℝ) : ℝ → ℂ :=
  abelProfile (evenCoshLift (broadTranslatedSquare L hL t τ))

theorem broadTranslatedProfile_continuous (L : ℝ) (hL : 0<L) (t τ : ℝ) :
    ContinuousOn (broadTranslatedProfile L hL t τ) (Ici 1) := by
  have hh := broadTranslatedSquare_regular L hL t τ
  exact evenTime_abel_continuous _ hh.1 hh.2.1 hh.2.2

theorem broadTranslatedProfile_support (L : ℝ) (hL : 1≤L) (t τ : ℝ) :
    Function.support (broadTranslatedProfile L (lt_of_lt_of_le zero_lt_one hL) t τ) ⊆
      Iic (Real.cosh (2+|τ|)) :=
  abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity)
    (broadTranslatedSquare_support L hL t τ))

/-- The actual broad packet profile satisfies a uniform correspondence
trace remainder bound. Matrix height, translation and central frequency
are all quantified after the fixed geometric constant. -/
theorem broadTranslatedProfile_remainder_bound (o : ℍ) :
    ∃ C : ℝ,0≤C ∧ ∀ (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (S L t τ : ℝ) (hL : 1≤L),0≤S → 1≤t →
      IntegrableOn (radialIntegralRemainder N M hM
        (broadTranslatedProfile L (lt_of_lt_of_le zero_lt_one hL) t τ)) (Metric.closedBall o S) ∧
      (∫ z in Metric.closedBall o S,‖radialIntegralRemainder N M hM
        (broadTranslatedProfile L (lt_of_lt_of_le zero_lt_one hL) t τ) z‖)≤
        C*(integralMatrixHeight M)^40*(1+|τ|)*Real.sqrt t*L^6*Real.exp (30*S+10*|τ|) := by
  obtain ⟨A,hA,hdecay⟩ := broadTranslatedSquare_abel_decay
  obtain ⟨G,hG,hgeom⟩ := radialIntegralRemainder_uniform_height_bound o
  refine ⟨G*A*Real.exp 20,by positivity,?_⟩
  intro N _ M hM S L t τ hL hS ht
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hh := hgeom N M hM S (2+|τ|) hS (by positivity)
    (broadTranslatedProfile L hLp t τ) (broadTranslatedProfile_continuous L hLp t τ)
    (broadTranslatedProfile_support L hL t τ) (A*(1+|τ|)*Real.sqrt t*L^6) (by positivity)
    (fun d hd => hdecay L t τ d hL ht hd)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw [show 10*(2+|τ|)+30*S=20+(30*S+10*|τ|) by ring,Real.exp_add]
  ring

#print axioms broadTranslatedProfile_continuous
#print axioms broadTranslatedProfile_support
#print axioms broadTranslatedProfile_remainder_bound

end QuantitativeMaass
