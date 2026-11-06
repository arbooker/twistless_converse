module

public import AsymptoticClassicalDiscriminantOrbitV1
public import Mathlib.LinearAlgebra.Vandermonde

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Filter
open scoped Topology Manifold

/-- A finite family of distinct holomorphic functions stays separated on
 a neighborhood of some point. -/
theorem eventually_injective {ι : Type*} [Fintype ι] (f : ι → ℍ → ℂ)
    (hf : ∀ i, MDiff (f i)) (hinj : Function.Injective f) :
    ∃ z₀ : ℍ, ∀ᶠ z in 𝓝 z₀, Function.Injective (fun i => f i z) := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_separating_point f hf hinj
  refine ⟨z₀, ?_⟩
  have hp : ∀ i j, ∀ᶠ z in 𝓝 z₀, i ≠ j → f i z ≠ f j z := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (by simp [hij])
    · have hh : f i z₀ - f j z₀ ≠ 0 := sub_ne_zero.mpr (fun he => hij (hz₀ he))
      filter_upwards [((hf i).continuous.sub (hf j).continuous).continuousAt.eventually_ne hh]
        with z hz
      exact fun _ => sub_ne_zero.mp hz
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hp i))] with z hz
  intro i j he
  by_contra hij
  exact hz i j hij he

/-- Holomorphic coefficients of a Vandermonde system vanish identically.
 The matrix only needs to be invertible on one open neighborhood. -/
theorem coefficients_eq_zero {n : ℕ} (f v : Fin n → ℍ → ℂ)
    (hf : ∀ i, MDiff (f i)) (hv : ∀ j, MDiff (v j))
    (hinj : Function.Injective f)
    (he : ∀ z i, ∑ j : Fin n, f i z ^ (j : ℕ) * v j z = 0) :
    ∀ j, v j = 0 := by
  obtain ⟨z₀, hz₀⟩ := eventually_injective f hf hinj
  have hzero : ∀ᶠ z in 𝓝 z₀, ∀ j, v j z = 0 := by
    filter_upwards [hz₀] with z hz
    have hh := Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hz (he z)
    exact fun j => congrFun hh j
  intro j
  apply UpperHalfPlane.eq_zero_of_frequently (hv j) (τ := z₀)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  exact hzero.mono (fun _ hz => hz j)

#print axioms eventually_injective
#print axioms coefficients_eq_zero

end AsymptoticClassicalDiscriminant
