module

public import FinitenessAllLevelCompactIndexV1
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFredholmReduction

open ContinuousLinearMap Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {T₀ : X →L[ℂ] X} (P : T₀.FredholmPackage)

/-- Projection onto the finite kernel coordinate at the base point. -/
def coordinate : X →L[ℂ] P.decDom.X₀ :=
  P.decDom.X₀.projectionOntoL P.decDom.X₁ P.decDom.isTopCompl.symm

/-- Projection onto the finite cokernel coordinate at the base point. -/
def obstruction : X →L[ℂ] P.decCodom.X₀ :=
  P.decCodom.X₀.projectionOntoL P.decCodom.X₁ P.decCodom.isTopCompl.symm

def block (T : X →L[ℂ] X) : P.decDom.X₁ →L[ℂ] P.decCodom.X₁ :=
  P.decCodom.proj ∘L T ∘L P.decDom.X₁.subtypeL

def offBlock (T : X →L[ℂ] X) : P.decDom.X₀ →L[ℂ] P.decCodom.X₁ :=
  P.decCodom.proj ∘L T ∘L P.decDom.X₀.subtypeL

/-- Solve the infinite-dimensional block using its actual bounded inverse. -/
def lift (T : X →L[ℂ] X) : P.decDom.X₀ →L[ℂ] X :=
  P.decDom.X₀.subtypeL -
    P.decDom.X₁.subtypeL ∘L (block P T).inverse ∘L offBlock P T

/-- The remaining finite-dimensional matrix after solving the large block. -/
def matrix (T : X →L[ℂ] X) : P.decDom.X₀ →L[ℂ] P.decCodom.X₀ :=
  obstruction P ∘L T ∘L lift P T

theorem split (x : X) : (P.decDom.proj x : X) + (coordinate P x : X) = x :=
  Submodule.projection_add_projection_eq_self P.decDom.isTopCompl.isCompl x

theorem coordinate_lift (T : X →L[ℂ] X) (v : P.decDom.X₀) :
    coordinate P (lift P T v) = v := by
  simp [coordinate, lift, Submodule.projectionOnto_apply_right]

theorem projected_lift (T : X →L[ℂ] X) (h : (block P T).IsInvertible)
    (v : P.decDom.X₀) : P.decCodom.proj (T (lift P T v)) = 0 := by
  simp only [lift, sub_apply, comp_apply, map_sub]
  change offBlock P T v - block P T ((block P T).inverse (offBlock P T v)) = 0
  rw [h.self_apply_inverse, sub_self]

theorem eq_lift_of_projected_zero (T : X →L[ℂ] X) (h : (block P T).IsInvertible)
    (x : X) (hx : P.decCodom.proj (T x) = 0) : x = lift P T (coordinate P x) := by
  have hs : block P T (P.decDom.proj x) + offBlock P T (coordinate P x) = 0 := by
    change P.decCodom.proj (T (P.decDom.proj x)) +
      P.decCodom.proj (T (coordinate P x)) = 0
    rw [← map_add, ← map_add, split, hx]
  have he : P.decDom.proj x = -(block P T).inverse (offBlock P T (coordinate P x)) := by
    apply h.injective
    rw [map_neg, h.self_apply_inverse]
    exact eq_neg_of_add_eq_zero_left hs
  calc
    x = (P.decDom.proj x : X) + (coordinate P x : X) := (split P x).symm
    _ = lift P T (coordinate P x) := by rw [he]; simp [lift, sub_eq_add_neg, add_comm]

/-- Exact finite reduction of the fixed-point equation on the invertible
block neighborhood. This statement concerns the pencil, not yet the Euler locus. -/
theorem kernel_iff (T : X →L[ℂ] X) (h : (block P T).IsInvertible) (x : X) :
    T x = 0 ↔ ∃ v : P.decDom.X₀, matrix P T v = 0 ∧ x = lift P T v := by
  constructor
  · intro hx
    have he := eq_lift_of_projected_zero P T h x (by rw [hx, map_zero])
    refine ⟨coordinate P x, ?_, he⟩
    change obstruction P (T (lift P T (coordinate P x))) = 0
    rw [← he, hx, map_zero]
  · rintro ⟨v, hv, rfl⟩
    have he : (P.decCodom.proj (T (lift P T v)) : X) +
        (obstruction P (T (lift P T v)) : X) = T (lift P T v) :=
      Submodule.projection_add_projection_eq_self P.decCodom.isTopCompl.isCompl _
    rw [projected_lift P T h v, show obstruction P (T (lift P T v)) = 0 from hv] at he
    simpa using he.symm

theorem lift_injective (T : X →L[ℂ] X) : Function.Injective (lift P T) := by
  intro v w h
  have hh := congrArg (coordinate P) h
  simpa only [coordinate_lift] using hh

theorem eventually_block [CompleteSpace X] (T : ℂ → X →L[ℂ] X) {z : ℂ}
    (hT : ContinuousAt T z) (h₀ : T z = T₀) :
    ∀ᶠ w in 𝓝 z, (block P (T w)).IsInvertible := by
  have hh := P.eventually_nhds_isInvertible
  have hT' : Filter.Tendsto T (𝓝 z) (𝓝 T₀) := by simpa only [ContinuousAt, h₀] using hT
  exact hT'.eventually hh

#print axioms kernel_iff
#print axioms lift_injective
#print axioms eventually_block

end FinitenessAllLevelFredholmReduction
