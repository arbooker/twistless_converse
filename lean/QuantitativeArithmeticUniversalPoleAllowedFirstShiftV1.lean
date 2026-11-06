module

public import QuantitativeArithmeticUniversalPoleVectorV1
public import QuantitativeArithmeticSmallLevelFirstShiftKernelV2
public import SmallLevelContinuedRegularTailV1
public import SmallLevelAllowedSimplePoleTailV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Matrix Filter Set
open QuantitativeArithmeticSmallLevelFirstShiftRectangular
open scoped Topology

/-- A first-shift syzygy constrains ANY universal principal-part vector.
The lower-point Laurent coefficients are eliminated at the level of germs,
so this can be combined with arbitrarily many previously established rows
without choosing another vector or assuming equal pole orders. -/
theorem IsLeadingVector.allowed_first_shift {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (L : ℂ → Matrix ρ κ ℂ)
    (hG : ∀ i x, MeromorphicNFAt (fun z => G z i) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hL : ∀ x r i, AnalyticAt ℂ (fun z => L z r i) x)
    (hLA : ∀ z, L z*A z=0)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ a∈Finset.range n, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (x k : ℂ) (v : ι → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ j : ℕ, 0<j → x+j≠k → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j))
    (hk : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) k)
    (hCzero : ∀ (n : ℕ) (s : ℂ), s+((n:ℂ)+1)=k → ∀ i j, C n s i j=0) :
    (L (x-1)*C 0 (x-1)) *ᵥ v=0 := by
  classical
  obtain ⟨R,hR,heR⟩ := SmallLevelFiniteShift.continued_regular_tail B G A C H (x-1) 1
    hH (fun a ha i j => by
      simpa only [Nat.cast_one] using
        (SmallLevelFiniteShift.allowed_simple_pole_tail C k hC hCzero
          G hG x 1 hshift hk a ha i j)) hrow
  have heR' : ∀ i, (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] (x-1)]
      (fun z => R z i+∑ j, C 0 z i j*G (z+1) j) := by
    intro i
    simpa only [Finset.sum_range_one,Nat.cast_zero,zero_add] using heR i
  have heRall : (fun z => A z *ᵥ G z)=ᶠ[𝓝[≠] (x-1)]
      (fun z => R z+C 0 z *ᵥ G (z+1)) := by
    filter_upwards [Filter.eventually_all.mpr heR'] with z hz
    funext i
    exact hz i
  choose E hE heE using eliminate_lower_germ A (C 0) L G (fun z => G (z+1)) R
    (x-1) (hL (x-1)) hR hLA heRall
  have hEshift (r : ρ) : AnalyticAt ℂ (fun z => E r (z-1)) x :=
    (hE r).comp (f:=fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)
  have heEshift (r : ρ) :
      (fun z => ((L (z-1)*C 0 (z-1)) *ᵥ G z) r)=ᶠ[𝓝[≠] x]
        (fun z => E r (z-1)) := by
    simpa only [Function.comp_def,sub_add_cancel] using
      (heE r).comp_tendsto (tendsto_sub_one_punctured x)
  funext r
  apply hv.2 (fun z => (L (z-1)*C 0 (z-1)) r) (fun z => E r (z-1)) _
    (hEshift r) (heEshift r)
  intro j
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((hL (x-1) r i).comp (f:=fun z : ℂ => z-1)
    (analyticAt_id.sub analyticAt_const)).mul
    ((hC 0 (x-1) i j).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const))

#print axioms IsLeadingVector.allowed_first_shift
end QuantitativeArithmeticUniversalPoleVector
