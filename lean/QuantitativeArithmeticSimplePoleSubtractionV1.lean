module
public import SmallLevelSimplePoleCancellationV1
public import Mathlib.Analysis.Analytic.Order
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSimplePoleSubtraction
open Complex Filter Set
open scoped Topology

/-- Remove a possible simple pole at zero, producing an entire remainder
without imposing a value for the meromorphic function at the pole. -/
theorem exists_entire_remainder (J : ℂ → ℂ) (hJ0 : MeromorphicAt J 0)
    (hJa : ∀ z : ℂ, z≠0 → AnalyticAt ℂ J z)
    (hord : (-1:WithTop ℤ)≤meromorphicOrderAt J 0) :
    ∃ c : ℂ, ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ z : ℂ, z≠0 → J z=F z+c/z := by
  classical
  obtain ⟨Q,hQ,hq⟩ := SmallLevelFiniteShift.simple_pole_cancellation
    (fun z : ℂ => z) J 0 analyticAt_id rfl hJ0 hord
  obtain ⟨G,hG,hg⟩ := hQ.exists_eventuallyEq_sum_add_pow_mul 1
  have hg' : ∀ᶠ z in 𝓝 (0:ℂ), Q z=Q 0+z*G z := by
    simpa only [Finset.range_one,Finset.sum_singleton,pow_zero,Nat.factorial_zero,
      Nat.cast_one,div_one,one_smul,iteratedDeriv_zero,pow_one,smul_eq_mul,one_mul] using hg
  let F : ℂ → ℂ := Function.update (fun z => J z-Q 0/z) 0 (G 0)
  have hlocal : F =ᶠ[𝓝 (0:ℂ)] G := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [hq,hg'.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hz hgz hnz
      have hn : z≠0 := hnz
      have he : z*J z=Q 0+z*G z := hz.trans hgz
      dsimp [F]
      rw [Function.update_of_ne hn]
      apply (mul_left_cancel₀ hn)
      calc
        z*(J z-Q 0/z)=z*J z-Q 0 := by field_simp
        _ = z*G z := by rw [he]; ring
    · simp only [F,Function.update_self]
  refine ⟨Q 0,F,?_,?_⟩
  · intro z
    by_cases hz : z=0
    · subst z
      exact ((analyticAt_congr hlocal).mpr hG).differentiableAt
    · have he : F =ᶠ[𝓝 z] (fun w => J w-Q 0/w) := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        exact Function.update_of_ne hw _ _
      exact ((analyticAt_congr he).mpr
        ((hJa z hz).sub (analyticAt_const.div analyticAt_id hz))).differentiableAt
  · intro z hz
    dsimp [F]
    rw [Function.update_of_ne hz]
    ring

#print axioms exists_entire_remainder
end QuantitativeArithmeticSimplePoleSubtraction
