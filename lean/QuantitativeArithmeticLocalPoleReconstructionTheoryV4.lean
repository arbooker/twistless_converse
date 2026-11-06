module

public import QuantitativeArithmeticAnalyticDivisorContinuationV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticInitialTaylorGermTheoryV4
public import QuantitativeArithmeticUniversalPoleVectorV1

/-! Consolidated chapter: QuantitativeArithmeticLocalPoleReconstruction. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticLocalPoleReconstructionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLocalPoleReconstruction
open Complex Filter Set Matrix
open scoped Topology

/-- An observable reconstruction regular at the candidate point excludes a
pole there when its strictly positive translates are regular. The recurrence
is required only off the entire pivot divisors in the initial half-plane. -/
theorem regular_at {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : ℝ) (G : ℂ → ι → ℂ) (L : ℂ → Matrix ι κ ℂ)
    (K : ℕ → ℂ → Matrix κ ι ℂ) (E : ℕ → ℂ → κ → ℂ)
    (P : ρ → ℂ → ℂ) (x : ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hL : ∀ z i j, MeromorphicAt (fun w => L w i j) z)
    (hLx : ∀ i j, AnalyticAt ℂ (fun w => L w i j) x)
    (hK : ∀ n z i j, AnalyticAt ℂ (fun w => K n w i j) z)
    (hE : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z)
    (hPx : ∀ i, P i x≠0)
    (hrow : ∀ n z, B<z.re → (∀ i, P i z≠0) →
      G z=L z *ᵥ E n z+∑ a∈Finset.range n, (L z*K a z) *ᵥ G (z+((a:ℂ)+1)))
    (hshift : ∀ n : ℕ, 0<n → ∀ j : ι,
      0≤meromorphicOrderAt (fun z => G z j) (x+n)) (i : ι) :
    AnalyticAt ℂ (fun z => G z i) x := by
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
  have he : (fun z => G z i)=ᶠ[𝓝[≠] x] R := by
    apply QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity P hP x hPx
      (B-((n:ℝ)+1)) B (fun z _ => (hG i z).meromorphicAt) hR _ hb
    intro z hz hp
    have hh := congrFun (hrow n z hz hp) i
    simpa only [R,Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using hh
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
  have hg : QuantitativeArithmeticAnalyticGerm.HasAnalyticGerm (fun z => G z i) x :=
    ⟨R,hRE.add hRT,he⟩
  exact hg.analyticAt (hG i x)
#print axioms regular_at
end QuantitativeArithmeticLocalPoleReconstruction
end
end

/-! ## QuantitativeArithmeticLocalPoleAllowedReconstructionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLocalPoleReconstruction
open Matrix
/-- Reconstruction cancels a permitted simple pole in every positive Taylor tail. -/
theorem regular_at_allowed {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : ℝ) (G : ℂ → ι → ℂ) (L : ℂ → Matrix ι κ ℂ)
    (K : ℕ → ℂ → Matrix κ ι ℂ) (E : ℕ → ℂ → κ → ℂ)
    (P : ρ → ℂ → ℂ) (x k : ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hL : ∀ z i j, MeromorphicAt (fun w => L w i j) z)
    (hLx : ∀ i j, AnalyticAt ℂ (fun w => L w i j) x)
    (hK : ∀ n z i j, AnalyticAt ℂ (fun w => K n w i j) z)
    (hE : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z) (hPx : ∀ i, P i x≠0)
    (hrow : ∀ n z, B<z.re → (∀ i, P i z≠0) →
      G z=L z *ᵥ E n z+∑ a∈Finset.range n, (L z*K a z) *ᵥ G (z+((a:ℂ)+1)))
    (hzero : ∀ (n : ℕ) t j, x+((n:ℂ)+1)=k → K n x t j=0)
    (hk : ∀ i, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z i) k)
    (hshift : ∀ n : ℕ, 0<n → x+n≠k → ∀ j : ι,
      0≤meromorphicOrderAt (fun z => G z j) (x+n)) (i : ι) :
    AnalyticAt ℂ (fun z => G z i) x := by
  have hc (n : ℕ) (j : ι) (z : ℂ) : MeromorphicAt (fun w => (L w*K n w) i j) z := by
    change MeromorphicAt (fun w => ∑ t : κ, L w i t*K n w t j) z
    exact MeromorphicAt.fun_sum (fun t _ => (hL z i t).mul (hK n z t j).meromorphicAt)
  have hcx (n : ℕ) (j : ι) : AnalyticAt ℂ (fun w => (L w*K n w) i j) x := by
    change AnalyticAt ℂ (fun w => ∑ t : κ, L w i t*K n w t j) x
    exact Finset.analyticAt_fun_sum _ (fun t _ => (hLx i t).mul (hK n x t j))
  have he (n : ℕ) (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) :
      MeromorphicAt (fun w => (L w *ᵥ E n w) i) z := by
    change MeromorphicAt (fun w => ∑ t : κ, L w i t*E n w t) z
    exact MeromorphicAt.fun_sum (fun t _ => (hL z i t).mul (hE n t z hz).meromorphicAt)
  have hex (n : ℕ) (hz : B-((n:ℝ)+1)<x.re) :
      AnalyticAt ℂ (fun w => (L w *ᵥ E n w) i) x := by
    change AnalyticAt ℂ (fun w => ∑ t : κ, L w i t*E n w t) x
    exact Finset.analyticAt_fun_sum _ (fun t _ => (hLx i t).mul (hE n t x hz))
  apply QuantitativeArithmeticAnalyticGerm.HasAnalyticGerm.analyticAt (F:=fun z => G z i) (x:=x) ?_ (hG i x)
  apply QuantitativeArithmeticInitialTaylorGerm.analytic_germ_off_pivots_allowed_pole
    P hP G (fun z => G z i) B (fun n z j => (L z*K n z) i j)
    (fun n z => (L z *ᵥ E n z) i) hG (fun z => (hG i z).meromorphicAt)
    hc he ?_ x k hPx hcx hex ?_ hk hshift
  · intro n z hz hp
    simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using congrFun (hrow n z hz hp) i
  · intro n j hn
    change (∑ t : κ, L x i t*K n x t j)=0
    apply Finset.sum_eq_zero
    intro t _
    rw [hzero n t j hn,mul_zero]
#print axioms regular_at_allowed
end QuantitativeArithmeticLocalPoleReconstruction
end
end

/-! ## QuantitativeArithmeticLocalReconstructionValueV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLocalPoleReconstruction
open Complex Filter Set Matrix
open scoped Topology

/-- An observable reconstruction regular at the candidate point excludes a
pole there when its strictly positive translates are regular. The recurrence
is required only off the entire pivot divisors in the initial half-plane. -/
theorem value_at {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : ℝ) (G : ℂ → ι → ℂ) (L : ℂ → Matrix ι κ ℂ)
    (K : ℕ → ℂ → Matrix κ ι ℂ) (E : ℕ → ℂ → κ → ℂ)
    (P : ρ → ℂ → ℂ) (n : ℕ) (x : ℂ) (hb : B-((n:ℝ)+1)<x.re)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hL : ∀ z i j, MeromorphicAt (fun w => L w i j) z)
    (hLx : ∀ i j, AnalyticAt ℂ (fun w => L w i j) x)
    (hK : ∀ n z i j, AnalyticAt ℂ (fun w => K n w i j) z)
    (hE : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z)
    (hP : ∀ i z, AnalyticAt ℂ (P i) z)
    (hPx : ∀ i, P i x≠0)
    (hrow : ∀ n z, B<z.re → (∀ i, P i z≠0) →
      G z=L z *ᵥ E n z+∑ a∈Finset.range n, (L z*K a z) *ᵥ G (z+((a:ℂ)+1)))
    (hshift : ∀ n : ℕ, 0<n → ∀ j : ι,
      0≤meromorphicOrderAt (fun z => G z j) (x+n)) (i : ι) :
    G x i=(L x *ᵥ E n x) i+
      ∑ a∈Finset.range n, ∑ j : ι, (L x*K a x) i j*G (x+((a:ℂ)+1)) j := by
  classical
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
  have he : (fun z => G z i)=ᶠ[𝓝[≠] x] R := by
    apply QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity P hP x hPx
      (B-((n:ℝ)+1)) B (fun z _ => (hG i z).meromorphicAt) hR _ hb
    intro z hz hp
    have hh := congrFun (hrow n z hz hp) i
    simpa only [R,Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using hh
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
  have hg : QuantitativeArithmeticAnalyticGerm.HasAnalyticGerm (fun z => G z i) x :=
    ⟨R,hRE.add hRT,he⟩
  have hGa := hg.analyticAt (hG i x)
  exact ((hGa.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hRE.add hRT).continuousAt).mp he).eq_of_nhds
#print axioms value_at
end QuantitativeArithmeticLocalPoleReconstruction
end
end
