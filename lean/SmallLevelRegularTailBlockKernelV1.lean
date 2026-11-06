module

public import SmallLevelFiniteShiftBlockV1
public import SmallLevelContinuedRegularShiftedV1
public import SmallLevelAllowedSimplePoleTailV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology
variable {ι κ : Type*} [Fintype ι]

/-- Finite block pole detection only needs the complete tail products to
have analytic germs; individual shifted functions may have canceled poles. -/
theorem continued_regular_block_kernel
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (htail : ∀ n : Fin (d+1), ∀ a : ℕ, n.val≤a → ∀ i j,
      ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-n.val) ∧
        (fun z => C a z i j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-n.val)] R)
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (hpole : ∃ i, meromorphicOrderAt (fun z => G z i) x<0) :
    ∃ w : Fin (d+1)×ι → ℂ, w≠0 ∧
      ∀ r, ∑ b, blockLeading d A C x r b*w b=0 := by
  classical
  have hsrc (n : Fin (d+1)) :=
    continued_regular_shifted_source B G A C H x n.val hH (htail n) hrow
  choose R hR he using hsrc
  have hstack (b : Fin (d+1)×ι) : MeromorphicAt (fun z => stackGrid d G z b) x :=
    (hG b.2 (x-b.1.val)).meromorphicAt.comp_analyticAt
      (g:=fun z : ℂ => z-(b.1.val:ℂ)) (analyticAt_id.sub analyticAt_const)
  have hpstack : ∃ b : Fin (d+1)×ι, meromorphicOrderAt (fun z => stackGrid d G z b) x<0 := by
    obtain ⟨i,hi⟩ := hpole
    exact ⟨(0,i),by simpa only [stackGrid,Fin.val_zero,Nat.cast_zero,sub_zero] using hi⟩
  apply SmallLevelPoleGrid.leading_kernel hstack hpstack (blockLeading d A C)
    (fun r z => R r.1 z r.2) (blockLeading_analytic d A C hA hC x)
    (fun r => hR r.1 r.2)
  intro r
  simpa only [Filter.EventuallyEq,blockLeading_apply,stackGrid,lowerIndex] using he r.1 r.2

#print axioms blockLeading_apply
#print axioms continued_regular_block_kernel
end SmallLevelFiniteShift
