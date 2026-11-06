module

public import SmallLevelContinuedRegularTailV1
public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Matrix Filter
open scoped Topology

theorem IsLeadingVector.regular_tail_leading {ι κ : Type*} [Fintype ι]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (v : ι → ℂ) (hv : IsLeadingVector G x v)
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (htail : ∀ a i j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R x ∧
      (fun z => C a z i j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] x] R)
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) : A x *ᵥv=0 := by
  obtain ⟨R,hR,he⟩ := SmallLevelFiniteShift.continued_regular_tail B G A C H x 0
    hH (fun a _ i j => htail a i j) hrow
  funext i
  exact hv.2 (fun z => A z i) (fun z => R z i) (hA i) (hR i)
    (by simpa only [Finset.range_zero,Finset.sum_empty,add_zero] using he i)

#print axioms IsLeadingVector.regular_tail_leading
end QuantitativeArithmeticUniversalPoleVector
