module
public import QuantitativeArithmeticAnalyticDivisorContinuationV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCancelledTaylorRows
open Complex Filter
open scoped Topology
open QuantitativeArithmeticAnalyticGerm

/-- Cancel the unwanted left-hand additive twists on the initial half-plane
before continuation. Only the observed positive-shift vector needs a
meromorphic continuation. The first surviving shift is then an analytic germ
when all higher shifts are regular. -/
theorem first_shift {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (B : ℝ) (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hC : ∀ n i z, AnalyticAt ℂ (fun w => C n w i) z)
    (hE : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (E n) z)
    (hrow : ∀ (n : ℕ) z, B<z.re →
      0=E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i)
    (x : ℂ) (hshift : ∀ n : ℕ, 2≤n → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) (x+n)) :
    HasAnalyticGerm (fun z => ∑ i, C 0 z i*G (z+1) i) x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-(((n+1:ℕ):ℝ)+1)<x.re := by push_cast; linarith
  let T : ℂ → ℂ := fun z => E (n+1) z+
    ∑ a∈Finset.range (n+1), ∑ i, C a z i*G (z+((a:ℂ)+1)) i
  have hT (z : ℂ) (hz : B-(((n+1:ℕ):ℝ)+1)<z.re) : MeromorphicAt T z := by
    apply (hE (n+1) z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro i _
    exact (hC a i z).meromorphicAt.mul ((hG i (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
      (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : (fun _ : ℂ => (0:ℂ))=ᶠ[𝓝[≠] x] T := by
    apply QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity
      (fun _ : Unit => fun _ : ℂ => (1:ℂ))
      (by intro _ _; exact analyticAt_const) x (by intro _; norm_num)
      (B-(((n+1:ℕ):ℝ)+1)) B (fun z _ => MeromorphicAt.const 0 z) hT _ hx
    intro z hz _
    exact hrow (n+1) z hz
  let R : ℂ → ℂ := fun z => E (n+1) z+
    ∑ a∈Finset.range n, ∑ i, C (a+1) z i*G (z+(((a+1:ℕ):ℂ)+1)) i
  have hR : AnalyticAt ℂ R x := by
    apply (hE (n+1) x hx).add
    apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro i _
    have hs : AnalyticAt ℂ (fun z => G z i) (x+(((a+1:ℕ):ℂ)+1)) := by
      apply (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1+1) (by omega) i
    exact (hC (a+1) i x).mul (hs.comp (f:=fun z : ℂ => z+(((a+1:ℕ):ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  refine ⟨fun z => -R z,hR.neg,?_⟩
  filter_upwards [he] with z hz
  change 0=E (n+1) z+∑ a∈Finset.range (n+1), ∑ i, C a z i*G (z+((a:ℂ)+1)) i at hz
  rw [Finset.sum_range_succ'] at hz
  simp only [Nat.cast_zero,zero_add] at hz
  dsimp only [R]
  linear_combination -hz

#print axioms first_shift
end QuantitativeArithmeticCancelledTaylorRows
