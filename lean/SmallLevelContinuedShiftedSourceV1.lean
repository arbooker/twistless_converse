module

public import SmallLevelContinuedFiniteShiftSourceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

/-- Bring all lower-point Taylor equations to the same center. The
remainder is analytic at the original rightmost pole. -/
theorem continued_shifted_source
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j)) :
    ∃ R : ℂ → κ → ℂ, (∀ i, AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ i, (fun z => (∑ j, A (z-d) i j*G (z-d) j)-
        ∑ a∈Finset.range d, ∑ j, C a (z-d) i j*G (z-((d-1-a:ℕ):ℂ)) j)=ᶠ[𝓝[≠] x]
        (fun z => R z i) := by
  have hupper (j : ℕ) (hj : d<j) (i : ι) :
      AnalyticAt ℂ (fun z => G z i) (x-(d:ℂ)+j) := by
    have he : x-(d:ℂ)+(j:ℂ)=x+((j-d:ℕ):ℂ) := by
      rw [Nat.cast_sub (by omega : d≤j)]
      ring
    rw [he]
    exact (hG i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hshift (j-d) (by omega) i)
  obtain ⟨R0,hR0,he⟩ := continued_finite_shift_source B G A C H (x-d) d
    (fun n i j => hC n (x-d) i j) hH hupper hrow
  refine ⟨fun z => R0 (z-d),?_,?_⟩
  · intro i
    exact (hR0 i).comp (f:=fun z : ℂ => z-(d:ℂ)) (analyticAt_id.sub analyticAt_const)
  · intro i
    filter_upwards [(he i).comp_tendsto (tendsto_sub_punctured x d)] with z hz
    simp only [Function.comp_def] at hz
    have hs : (∑ a∈Finset.range d, ∑ j, C a (z-d) i j*G (z-d+((a:ℂ)+1)) j)=
        ∑ a∈Finset.range d, ∑ j, C a (z-d) i j*G (z-((d-1-a:ℕ):ℂ)) j := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : a<d := Finset.mem_range.mp ha
      have hd : d-1-a+a+1=d := by omega
      have hdz : ((d-1-a:ℕ):ℂ)+(a:ℂ)+1=(d:ℂ) := by exact_mod_cast hd
      have hez : z-(d:ℂ)+((a:ℂ)+1)=z-((d-1-a:ℕ):ℂ) := by linear_combination hdz
      rw [hez]
    rw [hz,hs]
    ring

#print axioms continued_shifted_source
end SmallLevelFiniteShift
