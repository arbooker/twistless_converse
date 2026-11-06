module

public import SmallLevelContinuedShiftedSourceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

def lowerIndex {d : ℕ} (n : Fin (d+1)) (a : ℕ) : Fin (d+1) :=
  ⟨n.val-1-a,by omega⟩

def stackGrid (d : ℕ) (G : ℂ → ι → ℂ) (z : ℂ) (b : Fin (d+1)×ι) : ℂ :=
  G (z-(b.1.val:ℂ)) b.2

def blockLeading (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (z : ℂ) :
    Matrix (Fin (d+1)×κ) (Fin (d+1)×ι) ℂ := fun r b =>
  (if b.1=r.1 then A (z-r.1.val) r.2 b.2 else 0)-
    ∑ a∈Finset.range r.1.val,
      if b.1=lowerIndex r.1 a then C a (z-r.1.val) r.2 b.2 else 0

theorem block_delta_apply {d : ℕ} (n : Fin (d+1)) (c : ι → ℂ)
    (w : Fin (d+1)×ι → ℂ) :
    (∑ b, (if b.1=n then c b.2 else 0)*w b)=∑ j, c j*w (n,j) := by
  simp [Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]

theorem blockLeading_apply (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (z : ℂ) (r : Fin (d+1)×κ)
    (w : Fin (d+1)×ι → ℂ) :
    (∑ b, blockLeading d A C z r b*w b)=
      (∑ j, A (z-r.1.val) r.2 j*w (r.1,j))-
        ∑ a∈Finset.range r.1.val, ∑ j, C a (z-r.1.val) r.2 j*w (lowerIndex r.1 a,j) := by
  simp only [blockLeading,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [Finset.sum_comm,block_delta_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact block_delta_apply _ _ _

omit [Fintype ι] in
theorem blockLeading_analytic (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (x : ℂ) (r : Fin (d+1)×κ) (b : Fin (d+1)×ι) :
    AnalyticAt ℂ (fun z => blockLeading d A C z r b) x := by
  apply AnalyticAt.sub
  · by_cases h : b.1=r.1
    · simp only [h,ite_true]
      exact (hA (x-r.1.val) r.2 b.2).comp (f:=fun z : ℂ => z-(r.1.val:ℂ))
        (analyticAt_id.sub analyticAt_const)
    · simpa only [ite_false,h] using (analyticAt_const (v:=(0:ℂ)))
  · apply Finset.analyticAt_fun_sum
    intro a _
    by_cases h : b.1=lowerIndex r.1 a
    · simp only [h,ite_true]
      exact (hC a (x-r.1.val) r.2 b.2).comp (f:=fun z : ℂ => z-(r.1.val:ℂ))
        (analyticAt_id.sub analyticAt_const)
    · simpa only [h,ite_false] using (analyticAt_const (v:=(0:ℂ)))

/-- A rightmost pole produces a nonzero kernel vector for a finite stack
of lower points. Pole orders at these points need not agree. -/
theorem continued_block_kernel
    (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix κ ι ℂ) (C : ℕ → ℂ → Matrix κ ι ℂ)
    (H : ℕ → ℂ → κ → ℂ) (x : ℂ) (d : ℕ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
      AnalyticAt ℂ (fun w => H n w i) z)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j))
    (hrow : ∀ (n : ℕ) i y, B-((n:ℝ)+1)<y.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] y]
        (fun z => H n z i+∑ a∈Finset.range n,
          ∑ j, C a z i j*G (z+((a:ℂ)+1)) j))
    (hpole : ∃ i, meromorphicOrderAt (fun z => G z i) x<0) :
    ∃ w : Fin (d+1)×ι → ℂ, w≠0 ∧
      ∀ r, ∑ b, blockLeading d A C x r b*w b=0 := by
  classical
  have hsrc (n : Fin (d+1)) :=
    continued_shifted_source B G A C H x n.val hG hC hH hshift hrow
  choose R hR he using hsrc
  have hstack (b : Fin (d+1)×ι) : MeromorphicAt (fun z => stackGrid d G z b) x :=
    (hG b.2 (x-b.1.val)).meromorphicAt.comp_analyticAt
      (g:=fun z : ℂ => z-(b.1.val:ℂ)) (analyticAt_id.sub analyticAt_const)
  have hpstack : ∃ b : Fin (d+1)×ι, meromorphicOrderAt (fun z => stackGrid d G z b) x<0 := by
    obtain ⟨i,hi⟩ := hpole
    exact ⟨(0,i),by simpa only [stackGrid,Fin.val_zero,Nat.cast_zero,sub_zero] using hi⟩
  apply SmallLevelPoleGrid.leading_kernel hstack hpstack (blockLeading d A C)
    (fun r z => R r.1 z r.2) (blockLeading_analytic d A C hA hC x)
    (fun r => hR r.1 r.2)
  intro r
  simpa only [Filter.EventuallyEq,blockLeading_apply,stackGrid,lowerIndex] using he r.1 r.2

#print axioms blockLeading_apply
#print axioms continued_block_kernel
end SmallLevelFiniteShift
