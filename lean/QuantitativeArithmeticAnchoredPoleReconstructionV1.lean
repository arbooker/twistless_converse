module
public import QuantitativeArithmeticAnalyticDivisorContinuationV1
public import QuantitativeArithmeticUniversalPoleVectorV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnchoredPoleReconstruction
open Complex Filter Set Matrix
open scoped Topology

/-- An anchored reconstruction determines every polar germ from one scalar
anchor, provided the positive translates are regular. -/
theorem difference_has_analytic_germ {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : ℝ) (G : ℂ → ι → ℂ) (L : ℂ → Matrix ι κ ℂ)
    (K : ℕ → ℂ → Matrix κ ι ℂ) (E : ℕ → ℂ → κ → ℂ)
    (P : ρ → ℂ → ℂ) (J : ℂ → ι → ℂ) (H : ℂ → ℂ) (x : ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hL : ∀ z i j, MeromorphicAt (fun w => L w i j) z)
    (hLx : ∀ i j, AnalyticAt ℂ (fun w => L w i j) x)
    (hK : ∀ n z i j, AnalyticAt ℂ (fun w => K n w i j) z)
    (hE : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z)
    (hPx : ∀ i, P i x≠0)
    (hJ : ∀ z i, MeromorphicAt (fun w => J w i) z)
    (hH : ∀ z, MeromorphicAt H z)
    (hrow : ∀ n z, B<z.re → (∀ i, P i z≠0) →
      G z=L z *ᵥ E n z+(∑ a∈Finset.range n, (L z*K a z) *ᵥ G (z+((a:ℂ)+1)))+(fun i => J z i*H z))
    (hshift : ∀ n : ℕ, 0<n → ∀ j : ι,
      0≤meromorphicOrderAt (fun z => G z j) (x+n)) (i : ι) :
    QuantitativeArithmeticAnalyticGerm.HasAnalyticGerm (fun z => G z i-J z i*H z) x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hb : B-((n:ℝ)+1)<x.re := by linarith
  let R : ℂ → ℂ := fun z => (L z *ᵥ E n z) i+
    ∑ a∈Finset.range n, ∑ j : ι, (L z*K a z) i j*G (z+((a:ℂ)+1)) j
  have hC (a : ℕ) (z : ℂ) (j : ι) : MeromorphicAt (fun w => (L w*K a w) i j) z := by
    change MeromorphicAt (fun w => ∑ t : κ, L w i t*K a w t j) z
    apply MeromorphicAt.fun_sum
    intro t _
    exact (hL z i t).mul (hK a z t j).meromorphicAt
  have hR (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) : MeromorphicAt R z := by
    apply MeromorphicAt.add
    · change MeromorphicAt (fun w => ∑ t : κ, L w i t*E n w t) z
      apply MeromorphicAt.fun_sum
      intro t _
      exact (hL z i t).mul (hE n t z hz).meromorphicAt
    · apply MeromorphicAt.fun_sum
      intro a _
      apply MeromorphicAt.fun_sum
      intro j _
      exact (hC a z j).mul ((hG j (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
        (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : (fun z => G z i)=ᶠ[𝓝[≠] x] (fun z => R z+J z i*H z) := by
    apply QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity P hP x hPx
      (B-((n:ℝ)+1)) B (fun z _ => (hG i z).meromorphicAt)
      (fun z hz => (hR z hz).add ((hJ z i).mul (hH z))) _ hb
    intro z hz hp
    have hh := congrFun (hrow n z hz hp) i
    simpa only [R,Matrix.mulVec,dotProduct,Pi.add_apply,Pi.mul_apply,Finset.sum_apply] using hh
  have hRE : AnalyticAt ℂ (fun z => (L z *ᵥ E n z) i) x := by
    change AnalyticAt ℂ (fun z => ∑ t : κ, L z i t*E n z t) x
    apply Finset.analyticAt_fun_sum
    intro t _
    exact (hLx i t).mul (hE n t x hb)
  have hRT : AnalyticAt ℂ (fun z => ∑ a∈Finset.range n,
      ∑ j : ι, (L z*K a z) i j*G (z+((a:ℂ)+1)) j) x := by
    apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro j _
    have hCx : AnalyticAt ℂ (fun z => (L z*K a z) i j) x := by
      change AnalyticAt ℂ (fun z => ∑ t : κ, L z i t*K a z t j) x
      apply Finset.analyticAt_fun_sum
      intro t _
      exact (hLx i t).mul (hK a x t j)
    have hGx : AnalyticAt ℂ (fun z => G z j) (x+((a:ℂ)+1)) := by
      apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) j
    exact hCx.mul (hGx.comp (f:=fun z : ℂ => z+((a:ℂ)+1)) (analyticAt_id.add analyticAt_const))
  refine ⟨R,hRE.add hRT,?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  ring
#print axioms difference_has_analytic_germ
end QuantitativeArithmeticAnchoredPoleReconstruction
