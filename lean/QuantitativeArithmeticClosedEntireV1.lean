module
public import SmallLevelContinuationTheoryV4
public import SmallLevelPoleGridTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticClosedEntire
open Complex Filter Set Matrix SmallLevelContinuation
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A closed Taylor system whose leading matrix is everywhere nonsingular
continues to an entire vector. No growth or pole-order bound on the
continued functions is assumed. -/
theorem closed_system_entire (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∀ y, (A y).det≠0)
    (hC : ∀ m x i j, AnalyticAt ℂ (fun z => C m z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re →
      A z *ᵥ F z=H n z+∑ a∈Finset.range n, C a z *ᵥ F (z+((a:ℂ)+1))) :
    ∃ G : ℂ → ι → ℂ, (∀ i, Differentiable ℂ (fun z => G z i)) ∧
      ∀ z, B<z.re → G z=F z := by
  obtain ⟨G,hG,hGF⟩ := closed_system_continuation B F A C H hF hA ⟨0,hd 0⟩ hC hH (by
    intro n z hz i
    simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using congrFun (hrow n z hz) i)
  have hright (i : ι) (z : ℂ) (hz : B<z.re) : AnalyticAt ℂ (fun w => G w i) z := by
    apply (hF i z hz).congr
    have hn : ∀ᶠ w in 𝓝 z, B<w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hn] with w hw
    exact (congrFun (hGF w hw) i).symm
  have hgerms := continued_rows B F G A C H
    (fun i z => (hG i z).meromorphicAt) hGF hA hC hH hrow
  refine ⟨G,?_,hGF⟩
  intro i x
  suffices han : AnalyticAt ℂ (fun z => G z i) x from han.differentiableAt
  apply (hG i x).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  obtain ⟨n,hp,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
    (fun j z => G z j) (x:=x) ⟨i,hp⟩ B hright
  exact hd (x+n) (det_zero_of_kernel (A (x+n))
    (continued_leading_kernel B G A C H hG hA hC hH hgerms (x+n) hp hshift))

#print axioms closed_system_entire
end QuantitativeArithmeticClosedEntire
