module

public import SmallLevelRegularizedShiftBlockV1
public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Matrix Filter Set SmallLevelFiniteShift
open scoped Topology

/-- Apply the regularized Taylor block to the same universal vector for
all rows. Lower-point pole orders are unrestricted. -/
theorem IsLeadingVector.regularized_block_rows {ι κ : Type*} [Fintype ι]
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
    (w : Fin (d+1) × ι → ℂ) (hw : IsLeadingVector (regularizedStack d G k) k w) :
    ∀ r, ∑ b, regularizedBlock d A C Q k r b*w b=0 := by
  classical
  have hsrc (n : Fin (d+1)) := continued_shifted_source B G A C H k n.val hG hC hH hshift hrow
  choose R hR he using hsrc
  let rhs : (Fin (d+1)×κ) → ℂ → ℂ := fun r z =>
    if r.1=0 then (z-k)*R r.1 z r.2 else R r.1 z r.2
  have hrhs (r : Fin (d+1)×κ) : AnalyticAt ℂ (rhs r) k := by
    by_cases hn : r.1=0
    · simp only [rhs,hn,ite_eq_left]
      exact (analyticAt_id.sub analyticAt_const).mul (hR 0 r.2)
    · simpa only [rhs,ite_eq_right hn] using hR r.1 r.2
  intro r
  apply hw.2 (fun z b => regularizedBlock d A C Q z r b) (rhs r)
    (regularizedBlock_analytic d A C Q hA hC k hQ r) (hrhs r)
  by_cases hn : r.1=0
  · filter_upwards [he r.1 r.2] with z hz
    have hz' : (∑ j, A z r.2 j*G z j)=R r.1 z r.2 := by
      simpa only [hn,Fin.val_zero,Nat.cast_zero,sub_zero,Finset.range_zero,Finset.sum_empty] using hz
    simp only [regularizedBlock_apply,hn,ite_eq_left,regularizedStack,rhs]
    calc
      (∑ j, A z r.2 j*((z-k)*G z j))=(z-k)*(∑ j, A z r.2 j*G z j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hz',hn]
  · filter_upwards [he r.1 r.2] with z hz
    rw [regularizedBlock_recurrence d A C Q G k z r.1 r.2 hn (hfactor r.1 hn z r.2)]
    simpa only [rhs,ite_eq_right hn] using hz

#print axioms IsLeadingVector.regularized_block_rows
end QuantitativeArithmeticUniversalPoleVector
