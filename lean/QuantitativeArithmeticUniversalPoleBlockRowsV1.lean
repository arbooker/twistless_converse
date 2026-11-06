module
public import QuantitativeArithmeticUniversalPoleProjectionV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Matrix Filter Set SmallLevelFiniteShift
open scoped Topology
variable {ι κ : Type*} [Fintype ι]

/-- Apply every continued row to the SAME universal principal vector of a
finite stack. This retains compatibility with additional rows and projections;
the lower points need not have the same pole order. -/
theorem IsLeadingVector.block_rows
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (v : Fin (d+1) × ι → ℂ) (hv : IsLeadingVector (stackGrid d G) x v)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ n : ℕ, 0<n → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+n))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) :
    ∀ r, ∑ b, blockLeading d A C x r b*v b=0 := by
  classical
  have hsrc (n : Fin (d+1)) :=
    continued_shifted_source B G A C H x n.val hG hC hH hshift hrow
  choose R hR he using hsrc
  intro r
  apply hv.2 (fun z b => blockLeading d A C z r b) (fun z => R r.1 z r.2)
    (blockLeading_analytic d A C hA hC x r) (hR r.1 r.2)
  simpa only [Filter.EventuallyEq,blockLeading_apply,stackGrid,lowerIndex] using he r.1 r.2

#print axioms IsLeadingVector.block_rows
end QuantitativeArithmeticUniversalPoleVector
