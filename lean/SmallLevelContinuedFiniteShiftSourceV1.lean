module

public import QuantitativeArithmeticSmallLevelFirstShiftKernelV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

theorem tendsto_sub_punctured (x c : ℂ) :
    Tendsto (fun z : ℂ => z-c) (𝓝[≠] x) (𝓝[≠] (x-c)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,sub_left_inj] using hz

/-- Isolate any finite initial segment of the Taylor recurrence. Only the
strictly higher shifts are required to be analytic. -/
theorem continued_finite_shift_source
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (hC : ∀ n i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ j : ℕ, d<j → ∀ i, AnalyticAt ℂ (fun z => G z i) (x+j))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) :
    ∃ R : ℂ → κ → ℂ, (∀ i, AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ i, (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => R z i+∑ a∈Finset.range d, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j) := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-(((d+n:ℕ):ℝ)+1)<x.re := by push_cast; have hd : (0:ℝ)≤d := Nat.cast_nonneg d; linarith
  let R : ℂ → κ → ℂ := fun z i => H (d+n) z i+
    ∑ a∈Finset.range n, ∑ j, C (d+a) z i j*G (z+(((d+a:ℕ):ℂ)+1)) j
  refine ⟨R,?_,?_⟩
  · intro i
    apply (hH (d+n) i x hx).add
    apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro j _
    have hs : AnalyticAt ℂ (fun z => G z j) (x+(((d+a:ℕ):ℂ)+1)) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (d+a+1) (by omega) j
    exact (hC (d+a) i j).mul (hs.comp (f:=fun z : ℂ => z+(((d+a:ℕ):ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  · intro i
    filter_upwards [hrow (d+n) i x hx] with z hz
    rw [Finset.sum_range_add] at hz
    simpa only [R,add_assoc,add_comm,add_left_comm] using hz

#print axioms continued_finite_shift_source
end SmallLevelFiniteShift
