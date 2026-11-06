module

public import QuantitativeArithmeticSmallLevelFirstShiftEliminationV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelFirstShiftRectangular
open Complex Matrix Filter Set
open scoped Topology

theorem tendsto_sub_one_punctured (x : ℂ) :
    Tendsto (fun z : ℂ => z-1) (𝓝[≠] x) (𝓝[≠] (x-1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,sub_left_inj] using hz

/-- The original leading rows and the first-shift syzygy rows annihilate
one and the same nonzero Laurent vector. This is the analytic justification
for adjoining first-Taylor projection rows at a rightmost pole. -/
theorem continued_first_shift_kernel {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (L : ℂ → Matrix ρ κ ℂ)
    (hG : ∀ i x, MeromorphicNFAt (fun z => G z i) x)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hL : ∀ x r i, AnalyticAt ℂ (fun z => L z r i) x)
    (hLA : ∀ z, L z*A z=0)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ a∈Finset.range n, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (x : ℂ) (hpole : ∃ i, meromorphicOrderAt (fun z => G z i) x<0)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j)) :
    ∃ v : ι → ℂ, v≠0 ∧ A x *ᵥ v=0 ∧ (L (x-1)*C 0 (x-1)) *ᵥ v=0 := by
  classical
  have hupper (j : ℕ) (hj : 2≤j) (i : ι) :
      AnalyticAt ℂ (fun z => G z i) (x-1+j) := by
    have he : x-1+(j:ℂ)=x+((j-1:ℕ):ℂ) := by
      have hj' : j=(j-1)+1 := by omega
      conv_lhs => rw [hj']
      push_cast
      ring
    rw [he]
    exact (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (hshift (j-1) (by omega) i)
  obtain ⟨R,hR,heR⟩ := continued_first_shift_source B G A C H (x-1)
    (fun n i j => hC n (x-1) i j) hH hupper hrow
  choose E hE heE using eliminate_lower_germ A (C 0) L G (fun z => G (z+1)) R
    (x-1) (hL (x-1)) hR hLA heR
  have hEshift (r : ρ) : AnalyticAt ℂ (fun z => E r (z-1)) x :=
    (hE r).comp (f:=fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)
  have heEshift (r : ρ) :
      (fun z => ((L (z-1)*C 0 (z-1)) *ᵥ G z) r)=ᶠ[𝓝[≠] x]
        (fun z => E r (z-1)) := by
    simpa only [Function.comp_def,sub_add_cancel] using
      (heE r).comp_tendsto (tendsto_sub_one_punctured x)
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R0 : κ → ℂ → ℂ := fun i z => H n z i+
    ∑ a∈Finset.range n, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j
  have hR0 (i : κ) : AnalyticAt ℂ (R0 i) x := by
    apply (hH n i x hx).add
    apply Finset.analyticAt_fun_sum
    intro a _
    apply Finset.analyticAt_fun_sum
    intro j _
    have hs : AnalyticAt ℂ (fun z => G z j) (x+((a:ℂ)+1)) := by
      apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) j
    exact (hC a x i j).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  let rows : ℂ → (κ ⊕ ρ) → ι → ℂ := fun z =>
    Sum.elim (A z) (L (z-1)*C 0 (z-1))
  let rhs : (κ ⊕ ρ) → ℂ → ℂ := Sum.elim R0 (fun r z => E r (z-1))
  have hrows (r : κ ⊕ ρ) (j : ι) : AnalyticAt ℂ (fun z => rows z r j) x := by
    cases r with
    | inl i => exact hA x i j
    | inr r =>
      apply Finset.analyticAt_fun_sum
      intro i _
      exact ((hL (x-1) r i).comp (f:=fun z : ℂ => z-1)
        (analyticAt_id.sub analyticAt_const)).mul
        ((hC 0 (x-1) i j).comp (f:=fun z : ℂ => z-1)
          (analyticAt_id.sub analyticAt_const))
  have hrhs (r : κ ⊕ ρ) : AnalyticAt ℂ (rhs r) x := by
    cases r with
    | inl i => exact hR0 i
    | inr r => exact hEshift r
  have he (r : κ ⊕ ρ) :
      (fun z => ∑ j, rows z r j*G z j)=ᶠ[𝓝[≠] x] rhs r := by
    cases r with
    | inl i => exact hrow n i x hx
    | inr r => exact heEshift r
  obtain ⟨v,hv,hvrows⟩ := SmallLevelPoleGrid.leading_kernel
    (fun i => (hG i x).meromorphicAt) hpole rows rhs hrows hrhs he
  refine ⟨v,hv,?_,?_⟩
  · funext i
    exact hvrows (Sum.inl i)
  · funext r
    exact hvrows (Sum.inr r)

#print axioms tendsto_sub_one_punctured
#print axioms continued_first_shift_kernel
end QuantitativeArithmeticSmallLevelFirstShiftRectangular
