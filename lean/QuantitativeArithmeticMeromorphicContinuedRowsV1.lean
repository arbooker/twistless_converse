module

public import SmallLevelContinuationTheoryV4
public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticMeromorphicRows
open Complex Filter Set Matrix
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

/-- Recurrences with meromorphic leading, shift and remainder coefficients
continue as punctured germs, including staged reconstruction coefficients. -/
theorem continued_rows (B : ℝ) (F G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ)
    (hG : ∀ i x, MeromorphicAt (fun z => G z i) x)
    (hGF : ∀ z, B<z.re → G z=F z)
    (hA : ∀ x i j, MeromorphicAt (fun z => A z i j) x)
    (hC : ∀ n x i j, MeromorphicAt (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re →
      A z *ᵥ F z=H n z+∑ m∈Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1)))
    (n : ℕ) (i : κ) (x : ℂ) (hx : B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j) := by
  apply SmallLevelContinuation.halfplane_germ_identity (B-((n:ℝ)+1)) B _ _ _ x hx
  · intro z _
    exact MeromorphicAt.fun_sum (fun j _ => (hA z i j).mul (hG j z))
  · intro z hz
    apply (hH n i z hz).add
    apply MeromorphicAt.fun_sum
    intro m _
    apply MeromorphicAt.fun_sum
    intro j _
    exact (hC m z i j).mul
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


#print axioms continued_rows
end QuantitativeArithmeticMeromorphicRows

