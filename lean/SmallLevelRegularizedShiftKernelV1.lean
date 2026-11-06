module

public import SmallLevelRegularizedShiftBlockV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

/-- A regularized top pole gives a kernel vector for the block whose top
Taylor coefficients have had their known local factor removed. The other
components are the original lower-point germs, with arbitrary pole orders. -/
theorem regularized_block_kernel {ι κ : Type*} [Fintype ι]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (k : ℂ) (d : ℕ)
    (Q : Fin (d+1) → ℂ → Matrix κ ι ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hQ : ∀ n i j, AnalyticAt ℂ (fun z => Q n z i j) k)
    (hfactor : ∀ n : Fin (d+1), n≠0 → ∀ z i j,
      C (n.val-1) (z-n.val) i j=(z-k)*Q n z i j)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (k+j))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (hpole : ∃ i, meromorphicOrderAt (fun z => (z-k)*G z i) k<0) :
    ∃ w : Fin (d+1)×ι → ℂ, w≠0 ∧
      ∀ r, ∑ b, regularizedBlock d A C Q k r b*w b=0 := by
  classical
  have hsrc (n : Fin (d+1)) := continued_shifted_source B G A C H k n.val hG hC hH hshift hrow
  choose R hR he using hsrc
  let rhs : (Fin (d+1)×κ) → ℂ → ℂ := fun r z =>
    if r.1=0 then (z-k)*R r.1 z r.2 else R r.1 z r.2
  have hrhs (r : Fin (d+1)×κ) : AnalyticAt ℂ (rhs r) k := by
    by_cases hn : r.1=0
    · simp only [rhs,hn,ite_true]
      exact (analyticAt_id.sub analyticAt_const).mul (hR 0 r.2)
    · simpa only [rhs,hn,ite_false] using hR r.1 r.2
  have hstack (b : Fin (d+1)×ι) : MeromorphicAt (fun z => regularizedStack d G k z b) k := by
    by_cases hb : b.1=0
    · simp only [regularizedStack,hb,ite_true]
      exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul (hG b.2 k).meromorphicAt
    · simp only [regularizedStack,hb,ite_false]
      exact (hG b.2 (k-b.1.val)).meromorphicAt.comp_analyticAt
        (g:=fun z : ℂ => z-(b.1.val:ℂ)) (analyticAt_id.sub analyticAt_const)
  have hpstack : ∃ b : Fin (d+1)×ι,
      meromorphicOrderAt (fun z => regularizedStack d G k z b) k<0 := by
    obtain ⟨i,hi⟩ := hpole
    exact ⟨(0,i),by simpa only [regularizedStack,ite_true] using hi⟩
  apply SmallLevelPoleGrid.leading_kernel hstack hpstack (regularizedBlock d A C Q) rhs
    (regularizedBlock_analytic d A C Q hA hC k hQ) hrhs
  intro r
  by_cases hn : r.1=0
  · filter_upwards [he r.1 r.2] with z hz
    have hz' : (∑ j, A z r.2 j*G z j)=R r.1 z r.2 := by
      simpa only [hn,Fin.val_zero,Nat.cast_zero,sub_zero,Finset.range_zero,Finset.sum_empty] using hz
    simp only [regularizedBlock_apply,hn,ite_true,regularizedStack,rhs]
    calc
      (∑ j, A z r.2 j*((z-k)*G z j))=(z-k)*(∑ j, A z r.2 j*G z j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hz',hn]
  · filter_upwards [he r.1 r.2] with z hz
    rw [regularizedBlock_recurrence d A C Q G k z r.1 r.2 hn (hfactor r.1 hn z r.2)]
    simpa only [rhs,hn,ite_false] using hz

#print axioms regularized_block_kernel
end SmallLevelFiniteShift
