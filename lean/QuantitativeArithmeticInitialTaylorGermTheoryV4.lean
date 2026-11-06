module

public import QuantitativeArithmeticAnalyticDivisorContinuationV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import SmallLevelAllowedSimplePoleTailV1

/-! Consolidated chapter: QuantitativeArithmeticInitialTaylorGerm. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticInitialTaylorGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex Filter
open scoped Topology
open QuantitativeArithmeticAnalyticGerm

/-- An initial-half-plane Taylor identity suffices for local analyticity
when every positive observed translate is regular. -/
theorem analytic_germ {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (A : ℂ → ℂ) (B : ℝ)
    (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hA : ∀ z, MeromorphicAt A z)
    (hC : ∀ n i z, AnalyticAt ℂ (fun w => C n w i) z)
    (hE : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (E n) z)
    (hrow : ∀ (n : ℕ) z, B<z.re →
      A z=E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i)
    (x : ℂ) (hshift : ∀ n : ℕ, 0<n → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) (x+n)) : HasAnalyticGerm A x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R : ℂ → ℂ := fun z => E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i
  have hR (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) : MeromorphicAt R z := by
    apply (hE n z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro i _
    exact (hC a i z).meromorphicAt.mul ((hG i (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
      (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : A=ᶠ[𝓝[≠] x] R := by
    apply QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity
      (fun _ : Unit => fun _ : ℂ => (1:ℂ))
      (by intro _ _; exact analyticAt_const) x (by intro _; norm_num)
      (B-((n:ℝ)+1)) B (fun z _ => hA z) hR _ hx
    intro z hz _
    exact hrow n z hz
  refine ⟨R,?_,he⟩
  apply (hE n x hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro i _
  have hs : AnalyticAt ℂ (fun z => G z i) (x+((a:ℂ)+1)) := by
    apply (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) i
  exact (hC a i x).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))
#print axioms analytic_germ
end QuantitativeArithmeticInitialTaylorGerm
end
end

/-! ## QuantitativeArithmeticInitialTaylorAllowedDivisorGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex Filter
open scoped Topology
open QuantitativeArithmeticAnalyticGerm

/-- Taylor elimination may use meromorphic row weights, provided those
weights are analytic at the point under examination. This permits the
regular local layer rescalings without claiming global holomorphy. -/
theorem analytic_germ_off_pivots_allowed_pole {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (P : ρ → ℂ → ℂ) (hP : ∀ i z, AnalyticAt ℂ (P i) z)
    (G : ℂ → ι → ℂ) (A : ℂ → ℂ) (B : ℝ)
    (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hA : ∀ z, MeromorphicAt A z)
    (hC : ∀ n i z, MeromorphicAt (fun w => C n w i) z)
    (hE : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → MeromorphicAt (E n) z)
    (hrow : ∀ (n : ℕ) z, B<z.re → (∀ i, P i z≠0) →
      A z=E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i)
    (x k : ℂ) (hPx : ∀ i, P i x≠0)
    (hCx : ∀ n i, AnalyticAt ℂ (fun w => C n w i) x)
    (hEx : ∀ n : ℕ, B-((n:ℝ)+1)<x.re → AnalyticAt ℂ (E n) x)
    (hzero : ∀ (n : ℕ) (i : ι), x+((n:ℂ)+1)=k → C n x i=0)
    (hk : ∀ i, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z i) k)
    (hshift : ∀ n : ℕ,0<n → x+n≠k → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) (x+n)) : HasAnalyticGerm A x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R : ℂ → ℂ := fun z => E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i
  have hR (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) : MeromorphicAt R z := by
    apply (hE n z hz).add
    apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro i _
    exact (hC a i z).mul ((hG i (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
      (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : A=ᶠ[𝓝[≠] x] R :=
    QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity P hP x hPx
      (B-((n:ℝ)+1)) B (fun z _ => hA z) hR (fun z hz hp => hrow n z hz hp) hx
  have ht (a : ℕ) (i : ι) :
      HasAnalyticGerm (fun z => C a z i*G (z+((a:ℂ)+1)) i) x := by
    by_cases hs : x+((a:ℂ)+1)=k
    · apply vanishing_mul_simple_pole (hCx a i) (hzero a i hs)
        ((hG i _).meromorphicAt.comp_analyticAt
          (g:=fun z : ℂ => z+((a:ℂ)+1)) (analyticAt_id.add analyticAt_const))
      change (-1:WithTop ℤ)≤meromorphicOrderAt
        ((fun z => G z i) ∘ (fun z : ℂ => z+((a:ℂ)+1))) x
      rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt,hs]
      exact hk i
    · have hr : AnalyticAt ℂ (fun z => G z i) (x+((a:ℂ)+1)) := by
        apply (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
        simpa only [Nat.cast_add,Nat.cast_one] using
          hshift (a+1) (by omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hs) i
      exact HasAnalyticGerm.of_analytic ((hCx a i).mul
        (hr.comp (f:=fun z : ℂ => z+((a:ℂ)+1)) (analyticAt_id.add analyticAt_const)))
  have hsum (t : Finset ℕ) :
      HasAnalyticGerm (fun z => ∑ a∈t, ∑ i, C a z i*G (z+((a:ℂ)+1)) i) x := by
    induction t using Finset.induction_on with
    | empty => simpa using (HasAnalyticGerm.of_analytic (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) x))
    | @insert a t ha ih =>
      have ht' := HasAnalyticGerm.sum (fun i z => C a z i*G (z+((a:ℂ)+1)) i) x (ht a)
      simpa only [Finset.sum_insert ha] using ht'.add ih
  have hr : HasAnalyticGerm R x := (HasAnalyticGerm.of_analytic (hEx n hx)).add (hsum (Finset.range n))
  exact hr.congr he.symm

#print axioms analytic_germ_off_pivots_allowed_pole
end QuantitativeArithmeticInitialTaylorGerm
end
end

/-! ## QuantitativeArithmeticInitialTaylorDivisorGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex Filter
open scoped Topology
open QuantitativeArithmeticAnalyticGerm

/-- Taylor elimination may use meromorphic row weights, provided those
weights are analytic at the point under examination. This permits the
regular local layer rescalings without claiming global holomorphy. -/
theorem analytic_germ_off_pivots {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (P : ρ → ℂ → ℂ) (hP : ∀ i z, AnalyticAt ℂ (P i) z)
    (G : ℂ → ι → ℂ) (A : ℂ → ℂ) (B : ℝ)
    (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hA : ∀ z, MeromorphicAt A z)
    (hC : ∀ n i z, MeromorphicAt (fun w => C n w i) z)
    (hE : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → MeromorphicAt (E n) z)
    (hrow : ∀ (n : ℕ) z, B<z.re → (∀ i, P i z≠0) →
      A z=E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i)
    (x : ℂ) (hPx : ∀ i, P i x≠0)
    (hCx : ∀ n i, AnalyticAt ℂ (fun w => C n w i) x)
    (hEx : ∀ n : ℕ, B-((n:ℝ)+1)<x.re → AnalyticAt ℂ (E n) x)
    (hshift : ∀ n : ℕ,0<n → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) (x+n)) : HasAnalyticGerm A x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R : ℂ → ℂ := fun z => E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i
  have hR (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) : MeromorphicAt R z := by
    apply (hE n z hz).add
    apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro i _
    exact (hC a i z).mul ((hG i (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
      (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : A=ᶠ[𝓝[≠] x] R :=
    QuantitativeArithmeticAnalyticDivisorContinuation.halfplane_identity P hP x hPx
      (B-((n:ℝ)+1)) B (fun z _ => hA z) hR (fun z hz hp => hrow n z hz hp) hx
  refine ⟨R,?_,he⟩
  apply (hEx n hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro i _
  have hs : AnalyticAt ℂ (fun z => G z i) (x+((a:ℂ)+1)) := by
    apply (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) i
  exact (hCx a i).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))

#print axioms analytic_germ_off_pivots
end QuantitativeArithmeticInitialTaylorGerm
end
end

/-! ## QuantitativeArithmeticInitialTaylorLocalGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex Filter
open scoped Topology
open QuantitativeArithmeticAnalyticGerm

/-- Taylor elimination may use meromorphic row weights, provided those
weights are analytic at the point under examination. This permits the
regular local layer rescalings without claiming global holomorphy. -/
theorem analytic_germ_of_local_coefficients {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (A : ℂ → ℂ) (B : ℝ)
    (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hA : ∀ z, MeromorphicAt A z)
    (hC : ∀ n i z, MeromorphicAt (fun w => C n w i) z)
    (hE : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → MeromorphicAt (E n) z)
    (hrow : ∀ (n : ℕ) z, B<z.re →
      A z=E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i)
    (x : ℂ)
    (hCx : ∀ n i, AnalyticAt ℂ (fun w => C n w i) x)
    (hEx : ∀ n : ℕ, B-((n:ℝ)+1)<x.re → AnalyticAt ℂ (E n) x)
    (hshift : ∀ n : ℕ,0<n → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) (x+n)) : HasAnalyticGerm A x := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R : ℂ → ℂ := fun z => E n z+∑ a∈Finset.range n, ∑ i, C a z i*G (z+((a:ℂ)+1)) i
  have hR (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) : MeromorphicAt R z := by
    apply (hE n z hz).add
    apply MeromorphicAt.fun_sum
    intro a _
    apply MeromorphicAt.fun_sum
    intro i _
    exact (hC a i z).mul ((hG i (z+((a:ℂ)+1))).meromorphicAt.comp_analyticAt
      (g:=fun w : ℂ => w+((a:ℂ)+1)) (by fun_prop))
  have he : A=ᶠ[𝓝[≠] x] R :=
    SmallLevelContinuation.halfplane_germ_identity (B-((n:ℝ)+1)) B
      (fun z _ => hA z) hR (fun z hz => hrow n z hz) x hx
  refine ⟨R,?_,he⟩
  apply (hEx n hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro i _
  have hs : AnalyticAt ℂ (fun z => G z i) (x+((a:ℂ)+1)) := by
    apply (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) i
  exact (hCx a i).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))

#print axioms analytic_germ_of_local_coefficients
end QuantitativeArithmeticInitialTaylorGerm
end
end

/-! ## QuantitativeArithmeticInitialTaylorPrefixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex

/-- Remove exactly the Taylor terms at and below the point under examination.
The original functions in this formula need exist only on their initial half-plane. -/
def shiftedPrefix {ι : Type*} [Fintype ι]
    (G₀ : ℂ → ι → ℂ) (R : ℂ → ℂ) (C : ℕ → ℂ → ι → ℂ)
    (d : ℕ) (s : ℂ) : ℂ :=
  R (s-(d:ℂ))-∑ n∈Finset.range d, ∑ i,
    C n (s-(d:ℂ)) i*G₀ (s-(d:ℂ)+((n:ℂ)+1)) i

/-- A depth-d row contributes only strictly positive translates after its
first d Taylor terms have been removed. This is an identity on the original
half-plane, not a continuation assertion for its individual lower terms. -/
theorem shifted_prefix_identity {ι : Type*} [Fintype ι]
    (G₀ : ℂ → ι → ℂ) (R : ℂ → ℂ)
    (C : ℕ → ℂ → ι → ℂ) (E : ℕ → ℂ → ℂ) (B : ℝ)
    (hrow : ∀ M : ℕ, ∀ z : ℂ, B<z.re →
      R z=E M z+∑ n∈Finset.range M, ∑ i, C n z i*G₀ (z+((n:ℂ)+1)) i)
    (d M : ℕ) (s : ℂ) (hs : B+(d:ℝ)<s.re) :
    shiftedPrefix G₀ R C d s=E (d+M) (s-(d:ℂ))+
      ∑ n∈Finset.range M, ∑ i,
        C (n+d) (s-(d:ℂ)) i*G₀ (s+((n:ℂ)+1)) i := by
  classical
  have hz : B<(s-(d:ℂ)).re := by simp only [Complex.sub_re,Complex.natCast_re]; linarith
  have hr := hrow (d+M) (s-(d:ℂ)) hz
  rw [Finset.sum_range_add] at hr
  have he (n : ℕ) : s-(d:ℂ)+(((d+n:ℕ):ℂ)+1)=s+((n:ℂ)+1) := by push_cast; ring
  simp_rw [he] at hr
  simp_rw [Nat.add_comm d] at hr
  rw [show M+d=d+M from Nat.add_comm _ _] at hr
  unfold shiftedPrefix
  linear_combination hr

/-- The Taylor-remainder domain is unchanged by moving a source down d
layers and taking d additional Taylor terms. -/
theorem shifted_remainder_analytic
    (E : ℕ → ℂ → ℂ) (B : ℝ)
    (hE : ∀ M : ℕ, ∀ z : ℂ, B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (E M) z)
    (d M : ℕ) (s : ℂ) (hs : B-((M:ℝ)+1)<s.re) :
    AnalyticAt ℂ (fun z => E (d+M) (z-(d:ℂ))) s := by
  apply (hE (d+M) (s-(d:ℂ)) ?_).comp (f:=fun z : ℂ => z-(d:ℂ))
    (analyticAt_id.sub analyticAt_const)
  simp only [Complex.sub_re,Complex.natCast_re,Nat.cast_add]
  linarith

#print axioms shifted_prefix_identity
#print axioms shifted_remainder_analytic
end QuantitativeArithmeticInitialTaylorGerm
end
end
