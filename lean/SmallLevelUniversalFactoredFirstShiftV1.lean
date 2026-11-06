module

public import SmallLevelUniversalPoleFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Matrix Filter Set
open QuantitativeArithmeticSmallLevelFirstShiftRectangular
open scoped Topology

/-- A principal vector for an analytically regularized grid also satisfies
all analytic rows of the original grid. -/
theorem IsLeadingVector.of_analytic_factor {ι : Type*} [Fintype ι]
    {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ} (c : ℂ → ℂ)
    (hv : IsLeadingVector (fun z i => c z*G z i) x v) (hc : AnalyticAt ℂ c x) :
    IsLeadingVector G x v := by
  refine ⟨hv.1,?_⟩
  intro A H hA hH he
  apply hv.2 A (fun z => c z*H z) hA (hc.mul hH)
  filter_upwards [he] with z hz
  calc
    (∑ j, A z j*(c z*G z j))=c z*(∑ j, A z j*G z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hz]

/-- Isolate the analytic germ produced by a first-shift syzygy, before
extracting any Laurent coefficient. -/
theorem continued_first_shift_analytic_rows {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (L : ℂ → Matrix ρ κ ℂ)
    (hG : ∀ i x, MeromorphicNFAt (fun z => G z i) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hL : ∀ x r i, AnalyticAt ℂ (fun z => L z r i) x)
    (hLA : ∀ z, L z*A z=0)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ a∈Finset.range n, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (x : ℂ)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j)) :
    ∀ r, ∃ E : ℂ → ℂ, AnalyticAt ℂ E x ∧
      (fun z => ((L (z-1)*C 0 (z-1)) *ᵥ G z) r)=ᶠ[𝓝[≠] x] E := by
  have hupper (j : ℕ) (hj : 2≤j) (i : ι) :
      AnalyticAt ℂ (fun z => G z i) (x-1+j) := by
    have he : x-1+(j:ℂ)=x+((j-1:ℕ):ℂ) := by
      rw [Nat.cast_sub (by omega : 1≤j)]
      push_cast
      ring
    rw [he]
    exact (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (hshift (j-1) (by omega) i)
  obtain ⟨R,hR,heR⟩ := continued_first_shift_source B G A C H (x-1)
    (fun n i j => hC n (x-1) i j) hH hupper hrow
  intro r
  obtain ⟨E,hE,heE⟩ := eliminate_lower_germ A (C 0) L G (fun z => G (z+1)) R
    (x-1) (hL (x-1)) hR hLA heR r
  refine ⟨fun z => E (z-1),?_,?_⟩
  · exact hE.comp (f:=fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)
  · simpa only [Function.comp_def,sub_add_cancel] using
      heE.comp_tendsto (tendsto_sub_one_punctured x)

/-- Cancel a known analytic scalar factor by regularizing the grid,
rather than assuming this factor is nonzero at the pole. -/
theorem IsLeadingVector.factored_first_shift {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (L : ℂ → Matrix ρ κ ℂ)
    (hG : ∀ i x, MeromorphicNFAt (fun z => G z i) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hL : ∀ x r i, AnalyticAt ℂ (fun z => L z r i) x)
    (hLA : ∀ z, L z*A z=0)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ a∈Finset.range n, ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (x : ℂ)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j))
    (c : ℂ → ℂ) (D : ℂ → Matrix ρ ι ℂ)
    (hD : ∀ r i, AnalyticAt ℂ (fun z => D z r i) x)
    (hfactor : ∀ z r i, (L (z-1)*C 0 (z-1)) r i=c z*D z r i)
    (v : ι → ℂ) (hv : IsLeadingVector (fun z i => c z*G z i) x v) : D x *ᵥ v=0 := by
  funext r
  obtain ⟨E,hE,he⟩ := continued_first_shift_analytic_rows B G A C H L
    hG hC hH hL hLA hrow x hshift r
  apply hv.2 (fun z => D z r) E (hD r) hE
  filter_upwards [he] with z hz
  calc
    (∑ j, D z r j*(c z*G z j))=((L (z-1)*C 0 (z-1)) *ᵥ G z) r := by
      simp only [Matrix.mulVec,dotProduct,hfactor]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := hz

#print axioms IsLeadingVector.of_analytic_factor
#print axioms continued_first_shift_analytic_rows
#print axioms IsLeadingVector.factored_first_shift
end QuantitativeArithmeticUniversalPoleVector
