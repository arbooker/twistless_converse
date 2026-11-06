module

public import SmallLevelContinuedRegularTailV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter
open scoped Topology

/-- A rightmost-pole hypothesis makes every higher shifted Taylor term
analytic at each lower point of the finite stack. -/
theorem regular_pole_tail {ι κ : Type*}
    (C : ℕ→ℂ→Matrix κ ι ℂ)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (G : ℂ→ι→ℂ) (hG : ∀ j z, MeromorphicNFAt (fun s => G s j) z)
    (x : ℂ) (d : ℕ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (b : ℕ) (hb : d≤b) (i : κ) (j : ι) :
    ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => C b z i j*G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R := by
  have he : x-(d:ℂ)+((b:ℂ)+1)=x+((b-d+1:ℕ):ℂ) := by
    rw [Nat.cast_add,Nat.cast_sub hb]
    push_cast
    ring
  have ha : AnalyticAt ℂ (fun z => G z j) (x-(d:ℂ)+((b:ℂ)+1)) := by
    rw [he]
    exact (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hshift (b-d+1) (by omega) j)
  exact ⟨_,(hC b (x-d) i j).mul (ha.comp (f:=fun z : ℂ => z+((b:ℂ)+1))
    (analyticAt_id.add analyticAt_const)),Filter.EventuallyEq.rfl⟩

#print axioms regular_pole_tail
end SmallLevelFiniteShift
