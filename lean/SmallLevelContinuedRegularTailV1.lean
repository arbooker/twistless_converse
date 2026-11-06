module

public import SmallLevelContinuedFiniteShiftSourceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

/-- Taylor truncation with analytic extensions of the complete tail terms.
This permits a shifted simple pole when its Taylor coefficient vanishes. -/
theorem continued_regular_tail {ι κ : Type*} [Fintype ι]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (htail : ∀ a : ℕ, d≤a → ∀ i j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R x ∧
      (fun z => C a z i j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] x] R)
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) :
    ∃ R : ℂ → κ → ℂ, (∀ i, AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ i, (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => R z i+∑ a∈Finset.range d, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j) := by
  classical
  have htail' (a : ℕ) := htail (d+a) (by omega)
  choose E hE he using htail'
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-(((d+n:ℕ):ℝ)+1)<x.re := by
    push_cast
    have hd : (0:ℝ)≤d := Nat.cast_nonneg d
    linarith
  let R : ℂ → κ → ℂ := fun z i => H (d+n) z i+∑ a∈Finset.range n, ∑ j, E a i j z
  refine ⟨R,?_,?_⟩
  · intro i
    exact (hH (d+n) i x hx).add
      (Finset.analyticAt_fun_sum _ (fun a _ => Finset.analyticAt_fun_sum _ (fun j _ => hE a i j)))
  · intro i
    have he' : ∀ᶠ z in 𝓝[≠] x, ∀ a∈Finset.range n, ∀ j,
        C (d+a) z i j*G (z+(((d+a:ℕ):ℂ)+1)) j=E a i j z := by
      apply (Finset.eventually_all (Finset.range n)).mpr
      intro a _
      exact Filter.eventually_all.mpr (fun j => he a i j)
    filter_upwards [hrow (d+n) i x hx,he'] with z hz hez
    rw [Finset.sum_range_add] at hz
    have hs : (∑ a∈Finset.range n, ∑ j, C (d+a) z i j*G (z+(((d+a:ℕ):ℂ)+1)) j)=
        ∑ a∈Finset.range n, ∑ j, E a i j z := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun j _ => hez a ha j)
    rw [hs] at hz
    simpa only [R,add_assoc,add_comm,add_left_comm] using hz

#print axioms continued_regular_tail
end SmallLevelFiniteShift
