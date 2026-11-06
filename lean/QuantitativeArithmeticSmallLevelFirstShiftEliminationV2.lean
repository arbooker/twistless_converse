module

public import SmallLevelContinuationTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelFirstShiftRectangular
open Complex Matrix Filter Set
open scoped Topology

variable {ι κ ρ : Type*} [Fintype ι] [Fintype κ]

/-- Analytic row combinations eliminate the lower-point unknown exactly.
The surviving upper-point rows have analytic right hand sides. No comparison
between the pole orders at the two points is needed. -/
theorem eliminate_lower_germ
    (A C : ℂ → Matrix κ ι ℂ) (L : ℂ → Matrix ρ κ ℂ)
    (U V : ℂ → ι → ℂ) (R : ℂ → κ → ℂ) (x : ℂ)
    (hL : ∀ r i, AnalyticAt ℂ (fun z => L z r i) x)
    (hR : ∀ i, AnalyticAt ℂ (fun z => R z i) x)
    (hLA : ∀ z, L z * A z=0)
    (he : (fun z => A z *ᵥ U z)=ᶠ[𝓝[≠] x]
      (fun z => R z+C z *ᵥ V z)) :
    ∀ r, ∃ H : ℂ → ℂ, AnalyticAt ℂ H x ∧
      (fun z => ((L z*C z) *ᵥ V z) r)=ᶠ[𝓝[≠] x] H := by
  classical
  intro r
  refine ⟨fun z => -(L z *ᵥ R z) r,?_,?_⟩
  · exact (Finset.analyticAt_fun_sum _ (fun i _ => (hL r i).mul (hR i))).neg
  · filter_upwards [he] with z hz
    have hh : (0 : ρ → ℂ)=L z *ᵥ R z+(L z*C z) *ᵥ V z := by
      calc
        0 = (L z*A z) *ᵥ U z := by rw [hLA, Matrix.zero_mulVec]
        _ = L z *ᵥ (A z *ᵥ U z) := by rw [Matrix.mulVec_mulVec]
        _ = _ := by rw [hz,Matrix.mulVec_add,Matrix.mulVec_mulVec]
    have hr := congrFun hh r
    simp only [Pi.zero_apply,Pi.add_apply] at hr
    linear_combination -hr

/-- The first correction in a continued Taylor system can be isolated at
one step below a rightmost pole. All subsequent shifts have analytic germs.
This statement supplies actual analytic remainders to the row-elimination
lemma rather than assuming first-jet equations for Laurent coefficients. -/
theorem continued_first_shift_source
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ)
    (hC : ∀ n i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ j : ℕ, 2≤j → ∀ i, AnalyticAt ℂ (fun z => G z i) (x+j))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) :
    ∃ R : ℂ → κ → ℂ, (∀ i, AnalyticAt ℂ (fun z => R z i) x) ∧
      (fun z => A z *ᵥ G z)=ᶠ[𝓝[≠] x]
        (fun z => R z+C 0 z *ᵥ G (z+1)) := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-(((n+1:ℕ):ℝ)+1)<x.re := by push_cast; linarith
  let R : ℂ → κ → ℂ := fun z i => H (n+1) z i+
    ∑ a∈Finset.range n, ∑ j, C (a+1) z i j*G (z+(((a+1:ℕ):ℂ)+1)) j
  refine ⟨R,?_,?_⟩
  · intro i
    apply (hH (n+1) i x hx).add
    apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro j _
    have hs : AnalyticAt ℂ (fun z => G z j) (x+(((a+1:ℕ):ℂ)+1)) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1+1) (by omega) j
    exact (hC (a+1) i j).mul (hs.comp (f:=fun z : ℂ => z+(((a+1:ℕ):ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  · filter_upwards [Filter.eventually_all.mpr (fun i => hrow (n+1) i x hx)] with z hz
    funext i
    have hi := hz i
    rw [Finset.sum_range_succ'] at hi
    simpa only [R,Matrix.mulVec,dotProduct,Pi.add_apply,Nat.cast_zero,zero_add,
      add_assoc,add_comm,add_left_comm] using hi

#print axioms eliminate_lower_germ
#print axioms continued_first_shift_source
end QuantitativeArithmeticSmallLevelFirstShiftRectangular
