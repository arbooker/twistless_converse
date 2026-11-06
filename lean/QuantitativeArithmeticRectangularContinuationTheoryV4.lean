module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticUniversalPoleVectorV1
public import SmallLevelContinuationTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticRectangularContinuation. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticRectangularContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRectangularContinuation
open Complex Matrix
variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq ρ]

theorem left_matrix_of_kernel (A : Matrix ρ ι ℂ)
    (hA : ∀ v : ι → ℂ, A *ᵥ v=0 → v=0) :
    ∃ L : Matrix ι ρ ℂ, L*A=1 := by
  have hi : Function.Injective (Matrix.toLin' A) := by
    intro v w h
    have hz : A *ᵥ (v-w)=0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (hA (v-w) hz)
  obtain ⟨g,hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨g.toMatrix',?_⟩
  have hh := congrArg LinearMap.toMatrix' hg
  simpa only [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_toLin',LinearMap.toMatrix'_id] using hh

/-- A rectangular reconstruction system only needs trivial kernel at one
point. A constant left multiplier converts it to the existing square-system
continuation theorem; no determinant minor is selected computationally. -/
theorem meromorphic_continuation (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ρ ι ℂ) (C : ℕ → ℂ → Matrix ρ ι ℂ)
    (H : ℕ → ℂ → ρ → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hker : ∃ s, ∀ v : ι → ℂ, A s *ᵥ v=0 → v=0)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re → A z *ᵥ F z=H n z+
      ∑ m ∈ Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1))) :
    ∃ G : ℂ → ι → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=F z := by
  obtain ⟨s,hs⟩ := hker
  obtain ⟨L,hL⟩ := left_matrix_of_kernel (A s) hs
  have hLA (x : ℂ) (i j : ι) : AnalyticAt ℂ (fun z => (L*A z) i j) x := by
    apply Finset.analyticAt_fun_sum
    intro t _
    exact analyticAt_const.mul (hA x t j)
  have hLC (n : ℕ) (x : ℂ) (i j : ι) :
      AnalyticAt ℂ (fun z => (L*C n z) i j) x := by
    apply Finset.analyticAt_fun_sum
    intro t _
    exact analyticAt_const.mul (hC n x t j)
  have hLH (n : ℕ) (i : ι) (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) :
      MeromorphicAt (fun w => (L *ᵥ H n w) i) z := by
    apply MeromorphicAt.fun_sum
    intro t _
    exact analyticAt_const.meromorphicAt.mul (hH n t z hz)
  apply SmallLevelContinuation.closed_system_meromorphic_source
    B F (fun z => L*A z) (fun n z => L*C n z) (fun n z => L *ᵥ H n z)
    hF hLA ⟨s,by rw [hL,Matrix.det_one]; exact one_ne_zero⟩ hLC hLH
  intro n z hz i
  have hh := congrArg (fun v => L *ᵥ v) (hrow n z hz)
  simp only [Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_mulVec] at hh
  simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using congrFun hh i

#print axioms left_matrix_of_kernel
#print axioms meromorphic_continuation
end QuantitativeArithmeticRectangularContinuation
end
end

/-! ## QuantitativeArithmeticRectangularContinuedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticRectangularContinuation
open Complex Filter Set Matrix
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

/-- A recurrence with meromorphic sources continues as punctured germs. -/
theorem continued_meromorphic_rows (B : ℝ) (F G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ)
    (hG : ∀ i x, MeromorphicAt (fun z => G z i) x)
    (hGF : ∀ z, B<z.re → G z=F z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re →
      A z *ᵥ F z=H n z+∑ m∈Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1)))
    (n : ℕ) (i : κ) (x : ℂ) (hx : B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j) := by
  apply SmallLevelContinuation.halfplane_germ_identity (B-((n:ℝ)+1)) B _ _ _ x hx
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
end QuantitativeArithmeticRectangularContinuation
end
end
