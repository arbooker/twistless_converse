module

public import QuantitativeMaassPositiveTimeCauchyV1
public import QuantitativeMaassWaveWeakEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

theorem shiftedQuotientWave_neg (N : ℕ) (t : ℝ) :
    shiftedQuotientWave N (-t)=shiftedQuotientWave N t :=
  shiftedRangeCosine_neg _ t

theorem quotientSine_neg (N : ℕ) (v : AutomorphicSpace N) (t : ℝ) :
    quotientSine N (-t) v= -quotientSine N t v := by
  let f := fun s => quotientSine N (-s) v+quotientSine N s v
  have hd (s : ℝ) : HasDerivAt f 0 s := by
    have hn := (quotientSine_hasDerivAt N v (-s)).scomp s (hasDerivAt_id s).neg
    have h := hn.add (quotientSine_hasDerivAt N v s)
    convert! h using 1
    simp only [neg_smul,one_smul,shiftedQuotientWave_neg,neg_add_cancel]
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hf : f t=0 := by simpa only [f,neg_zero,quotientSine_zero,add_zero] using he
  exact eq_neg_of_add_eq_zero_left hf

end QuantitativeMaass.Wave

namespace QuantitativeMaass

private theorem inner_two_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) : inner ℂ ((2:ℂ) • x) y=2*inner ℂ x y := by
  simp only [inner_smul_left,map_ofNat]

/-- Symmetric translations of an actual Abel test have exactly the spectral
cosine action. The displacement is restricted to keep both test supports
inside positive time; no global spectral identity is assumed. -/
theorem positiveTimeAbelOperator_cosine_pairing (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (f : AutomorphicSpace N)
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b)
    (t : ℝ) (ht : |t|<ψ.left) :
    inner ℂ (translatedPositiveTimeAbelOperator N ψ t f+
      translatedPositiveTimeAbelOperator N ψ (-t) f) a=
      2*inner ℂ (Wave.shiftedQuotientWave N t (positiveTimeAbelOperator N ψ f)) a := by
  have hp : 0<ψ.left+t := by have h := (abs_lt.mp ht).1; linarith
  have hn : 0<ψ.left+ -t := by have h := (abs_lt.mp ht).2; linarith
  have h1 := positiveTimeAbelOperator_cauchy_pairing N ψ f hab t hp
  have h2 := positiveTimeAbelOperator_cauchy_pairing N ψ f hab (-t) hn
  rw [Wave.quotientSine_neg,Wave.shiftedQuotientWave_neg,inner_neg_right] at h2
  rw [inner_add_left,h1,h2,Wave.shiftedWave_inner]
  ring

/-- The pairing identity extends from the full resolvent domain to all L2
vectors by density, giving a literal equality of the actual operators. -/
theorem positiveTimeAbelOperator_cosine_action (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (t : ℝ) (ht : |t|<ψ.left) :
    translatedPositiveTimeAbelOperator N ψ t+translatedPositiveTimeAbelOperator N ψ (-t)=
      (2:ℂ) • (Wave.shiftedQuotientWave N t).comp (positiveTimeAbelOperator N ψ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  have he : (fun a : AutomorphicSpace N =>
      inner ℂ (translatedPositiveTimeAbelOperator N ψ t f+
        translatedPositiveTimeAbelOperator N ψ (-t) f) a)=
      (fun a => inner ℂ ((2:ℂ) • Wave.shiftedQuotientWave N t (positiveTimeAbelOperator N ψ f)) a) := by
    apply (friedrichsResolvent_denseRange N).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    funext z
    have h := positiveTimeAbelOperator_cosine_pairing N ψ f (friedrichsGraph_resolvent N z) t ht
    change inner ℂ _ (friedrichsResolvent N z)=inner ℂ ((2:ℂ) • _) (friedrichsResolvent N z)
    exact h.trans (inner_two_smul _ _).symm
  intro a
  exact congrFun he a

#print axioms positiveTimeAbelOperator_cosine_pairing
#print axioms positiveTimeAbelOperator_cosine_action

end QuantitativeMaass
