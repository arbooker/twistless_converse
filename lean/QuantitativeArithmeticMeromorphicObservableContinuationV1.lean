module
public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import QuantitativeArithmeticMeromorphicCoefficientContinuationV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMeromorphicObservableContinuation
open Complex Matrix
variable {ι ρ κ : Type*} [Fintype ι] [Fintype ρ] [Fintype κ]
  [DecidableEq κ]

/-- Continue a constant observation family using meromorphic reconstruction
stages. Algebraic certificate identities are required only on the original
right half-plane; no auxiliary coordinate is assumed continued. -/
theorem meromorphic_observations_staged (B : ℝ) (F : ℂ → ι → ℂ)
    (Q : Matrix κ ι ℂ) (A : ℂ → Matrix ρ ι ℂ)
    (L : ℂ → Matrix κ ρ ℂ) (U : ℂ → Matrix κ κ ℂ)
    (C : ℕ → ℂ → Matrix ρ ι ℂ) (K : ℕ → ℂ → Matrix ρ κ ℂ)
    (H : ℕ → ℂ → ρ → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hL : ∀ x i j, MeromorphicAt (fun z => L z i j) x)
    (hU : ∀ x i j, AnalyticAt ℂ (fun z => U z i j) x)
    (hinvertible : ∃ s, (U s).det≠0)
    (hK : ∀ n x i j, MeromorphicAt (fun z => K n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hleading : ∀ z, B<z.re → L z*A z=U z*Q)
    (hsource : ∀ n z, B<z.re → C n z=K n z*Q)
    (hrow : ∀ n z, B<z.re → A z *ᵥ F z=H n z+
      ∑ m ∈ Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1))) :
    ∃ G : ℂ → κ → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=Q *ᵥ F z := by
  have hQF (i : κ) (z : ℂ) (hz : B<z.re) :
      AnalyticAt ℂ (fun w => (Q *ᵥ F w) i) z := by
    apply Finset.analyticAt_fun_sum
    intro t _
    exact analyticAt_const.mul (hF t z hz)
  have hLK (n : ℕ) (x : ℂ) (i j : κ) :
      MeromorphicAt (fun z => (L z*K n z) i j) x := by
    apply MeromorphicAt.fun_sum
    intro t _
    exact (hL x i t).mul (hK n x t j)
  have hLH (n : ℕ) (i : κ) (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) :
      MeromorphicAt (fun w => (L w *ᵥ H n w) i) z := by
    apply MeromorphicAt.fun_sum
    intro t _
    exact (hL z i t).mul (hH n t z hz)
  apply QuantitativeArithmeticMeromorphicCoefficientContinuation.closed_system_meromorphic_coefficients
    B (fun z => Q *ᵥ F z) U (fun n z => L z*K n z) (fun n z => L z *ᵥ H n z)
    hQF hU hinvertible hLK hLH
  intro n z hz i
  have hh := congrArg (fun v => L z *ᵥ v) (hrow n z hz)
  simp only [Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_mulVec] at hh
  rw [hleading z hz] at hh
  simp_rw [hsource _ z hz,← Matrix.mul_assoc] at hh
  have hv : U z *ᵥ (Q *ᵥ F z)=L z *ᵥ H n z+
      ∑ m ∈ Finset.range n, (L z*K m z) *ᵥ (Q *ᵥ F (z+((m:ℂ)+1))) := by
    simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hh
  simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply]
    using congrFun hv i
#print axioms meromorphic_observations_staged
end QuantitativeArithmeticMeromorphicObservableContinuation
