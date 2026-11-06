module

public import SmallLevelContinuationTheoryV4
public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelContinuation
open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- A recurrence with meromorphic sources continues as punctured germs. -/
theorem continued_meromorphic_rows (B : ℝ) (F G : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hG : ∀ i x, MeromorphicAt (fun z => G z i) x)
    (hGF : ∀ z, B<z.re → G z=F z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re →
      A z *ᵥ F z=H n z+∑ m∈Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1)))
    (n : ℕ) (i : ι) (x : ℂ) (hx : B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j) := by
  apply halfplane_germ_identity (B-((n:ℝ)+1)) B _ _ _ x hx
  · intro z _
    exact MeromorphicAt.fun_sum (fun j _ => (hA z i j).meromorphicAt.mul (hG j z))
  · intro z hz
    apply (hH n i z hz).add
    apply MeromorphicAt.fun_sum
    intro m _
    apply MeromorphicAt.fun_sum
    intro j _
    exact (hC m z i j).meromorphicAt.mul
      ((hG j (z+((m:ℂ)+1))).comp_analyticAt (g:=fun w : ℂ => w+((m:ℂ)+1)) (by fun_prop))
  · intro z hz
    dsimp only
    change B<z.re at hz
    have he := congrFun (hrow n z hz) i
    simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] at he
    rw [hGF z hz]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    have hs : B<(z+((m:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) m]
    rw [hGF _ hs]


#print axioms continued_meromorphic_rows
end SmallLevelContinuation

namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set
open scoped Topology
variable {ι : Type*} [Fintype ι]

theorem IsLeadingVector.taylor_at {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G x v)
    (hG : ∀ j z, MeromorphicNFAt (fun s => G s j) z)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (B : ℝ) (A : ℂ → ι → ℂ) (C : ℕ → ℂ → ι → ℂ) (H : ℕ → ℂ → ℂ)
    (hA : ∀ j, AnalyticAt ℂ (fun z => A z j) x)
    (hC : ∀ n j, AnalyticAt ℂ (fun z => C n z j) x)
    (hH : ∀ n : ℕ, B-((n:ℝ)+1)<x.re → AnalyticAt ℂ (H n) x)
    (hrow : ∀ n : ℕ, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z+∑ a∈Finset.range n, ∑ j, C a z j*G (z+((a:ℂ)+1)) j)) :
    ∑ j, A x j*v j=0 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  apply hv.2 A _ hA _ (hrow n hx)
  apply (hH n hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro j _
  have hs : AnalyticAt ℂ (fun z => G z j) (x+((a:ℂ)+1)) := by
    apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) j
  exact (hC a j).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))


#print axioms IsLeadingVector.taylor_at
end QuantitativeArithmeticUniversalPoleVector
