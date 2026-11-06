module

public import SmallLevelSimplePoleCancellationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter
open scoped Topology

/-- A complete Taylor tail is analytic as a germ even if a simple pole at
one permitted point is canceled by the vanishing Taylor coefficient. -/
theorem allowed_simple_pole_tail {ι κ : Type*}
    (C : ℕ → ℂ → Matrix κ ι ℂ) (k : ℂ)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hCzero : ∀ (n : ℕ) (s : ℂ), s+((n:ℂ)+1)=k → ∀ i j, C n s i j=0)
    (G : ℂ → ι → ℂ) (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (x : ℂ) (d : ℕ)
    (hshift : ∀ n : ℕ, 0<n → x+n≠k → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hk : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) k)
    (a : ℕ) (ha : d≤a) (r : κ) (j : ι) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => C a z r j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R := by
  have he : x-(d:ℂ)+((a:ℂ)+1)=x+((a-d+1:ℕ):ℂ) := by
    rw [Nat.cast_add,Nat.cast_sub ha,Nat.cast_one]
    ring
  have hc := hC a (x-d) r j
  by_cases hs : x-(d:ℂ)+((a:ℂ)+1)=k
  · have hc0 := hCzero a (x-d) hs r j
    have hg : MeromorphicAt (fun z => G (z+((a:ℂ)+1)) j) (x-d) :=
      (hG j (x-d+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
        (g:=fun z : ℂ => z+((a:ℂ)+1)) (analyticAt_id.add analyticAt_const)
    apply simple_pole_cancellation _ _ (x-d) hc hc0 hg
    change (-1:WithTop ℤ)≤meromorphicOrderAt
      ((fun z => G z j) ∘ (fun z : ℂ => z+((a:ℂ)+1))) (x-d)
    rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt,hs]
    exact hk j
  · have han : AnalyticAt ℂ (fun z => G z j) (x-d+((a:ℂ)+1)) := by
      apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [he]
      exact hshift (a-d+1) (by omega) (by simpa only [he] using hs) j
    exact ⟨_,hc.mul (han.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
      (analyticAt_id.add analyticAt_const)),Filter.EventuallyEq.rfl⟩

#print axioms allowed_simple_pole_tail
end SmallLevelFiniteShift
